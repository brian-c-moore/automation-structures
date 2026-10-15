//! Checked public entry points for reusable execution modalities.

use crate::connectives::buffer::{
    Buffer, BufferLayout, BufferStorage, ContiguousStorage, FifoStorage,
};
use crate::connectives::ordering_pass::{PositionOrder, try_arrange_indices};
use crate::modalities::fork_join::{
    CountedWorkerStates, ForkJoin as ForkJoinCarrier, ForkJoinWorkers, JoinedValuesSnapshot,
};

type CheckedForkJoinCarrier = ForkJoinCarrier<CountedWorkerStates, JoinedValuesSnapshot>;
use crate::modalities::sequential::Sequential as SequentialCarrier;
use crate::modalities::step_graph::{
    CountedStepStates, StepGraph as StepGraphCarrier, StepGraphStates,
};
type CheckedStepGraphCarrier = StepGraphCarrier<CountedStepStates>;
use crate::modalities::stream_graph::StreamGraph as StreamGraphCarrier;
use vstd::prelude::*;

verus! {

/// Invalid sequential-execution configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SequentialBuildError {
    /// Sequential execution requires at least one step.
    NoSteps,
    /// The value domain must contain at least one value.
    EmptyValueDomain,
    /// The initial value is outside the configured domain.
    InitialValueOutOfRange,
}

/// A totally ordered, finite-step execution modality.
///
/// # Examples
///
/// ```rust
/// use automation_structures::Sequential;
///
/// let mut execution = Sequential::new(1, 3, 0)?;
/// assert!(execution.begin_step());
/// assert!(execution.complete_step(2));
/// assert!(execution.is_done());
/// # Ok::<(), automation_structures::SequentialBuildError>(())
/// ```
pub struct Sequential {
    inner: SequentialCarrier,
}

impl Sequential {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate and construct an inactive sequential execution.
    ///
    /// # Errors
    ///
    /// Returns an error for zero steps, an empty value domain, or an out-of-domain
    /// initial value.
    pub fn new(steps: usize, value_domain_size: u64, initial_value: u64)
        -> (result: Result<Self, SequentialBuildError>) {
        if steps == 0 { return Err(SequentialBuildError::NoSteps); }
        if value_domain_size == 0 { return Err(SequentialBuildError::EmptyValueDomain); }
        if initial_value >= value_domain_size {
            return Err(SequentialBuildError::InitialValueOutOfRange);
        }
        Ok(Self { inner: SequentialCarrier::new(steps, value_domain_size, initial_value) })
    }

    /// Total number of steps.
    pub fn steps(&self) -> usize { self.inner.steps }

    /// Number of completed steps.
    pub fn completed(&self) -> usize { self.inner.pc }

    /// Current carried value.
    pub fn value(&self) -> u64 { self.inner.value }

    /// Whether a step is active.
    pub fn is_active(&self) -> bool { self.inner.active }

    /// Whether all steps are complete and inactive.
    pub fn is_done(&self) -> bool {
        proof { use_type_invariant(&*self); }
        self.inner.terminal_inactive()
    }

    /// Read a completed-step value by execution order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the history index is in bounds")]
    pub fn history(&self, index: usize) -> Option<u64> {
        if index < self.inner.history.len() { Some(self.inner.history[index]) } else { None }
    }

    /// Begin the next step if execution is inactive and incomplete.
    #[must_use]
    pub fn begin_step(&mut self) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = sequential_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.begin_step();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Complete the active step with a value in the configured domain.
    #[must_use]
    pub fn complete_step(&mut self, next_value: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = sequential_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.complete_step(next_value);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }
}

/// Invalid fork-join configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ForkJoinBuildError {
    /// The value domain must contain at least one value.
    EmptyValueDomain,
    /// The initial worker value is outside the configured domain.
    InitialValueOutOfRange,
}

/// One worker's fork-join lifecycle state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerState {
    /// The worker may be started.
    Ready,
    /// The worker is running.
    Running,
    /// The worker has produced its value.
    Complete,
}

/// The global fork-join phase.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForkJoinPhase {
    /// Workers may be started and completed.
    Fork,
    /// All workers are complete and the barrier has committed.
    Join,
    /// A stable output snapshot has been produced.
    Done,
}

/// A barriered fork-join execution with a stable output snapshot.
///
/// # Examples
///
/// ```rust
/// use automation_structures::ForkJoin;
///
/// let mut execution = ForkJoin::new(1, 4, 0)?;
/// assert!(execution.start_worker(0));
/// assert!(execution.complete_worker(0, 3));
/// assert!(execution.barrier());
/// assert!(execution.produce_output());
/// assert_eq!(execution.outputs(), Some(&[3][..]));
/// # Ok::<(), automation_structures::ForkJoinBuildError>(())
/// ```
pub struct ForkJoin {
    inner: CheckedForkJoinCarrier,
}

impl ForkJoin {
    /// Erased view of the one retained fork-join transition owner.
    pub closed spec fn state_spec(&self) -> CheckedForkJoinCarrier { self.inner }

    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate and construct a fork-join execution.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty value domain or an out-of-domain initial value.
    pub fn new(workers: usize, value_domain_size: u64, initial_value: u64)
        -> (result: Result<Self, ForkJoinBuildError>)
        ensures (result is Ok) == (value_domain_size > 0 && initial_value < value_domain_size),
            result is Ok ==> {
                let owner = result.unwrap().state_spec();
                &&& owner.inv() && owner.value_domain_size == value_domain_size
                &&& owner.wstate@.len() == workers && owner.wvalue@.len() == workers
                &&& owner.phase == ForkJoinPhase::Fork && !owner.output_ready
                &&& forall|i: int| 0 <= i < workers ==> #[trigger] owner.wstate@[i] == WorkerState::Ready
                &&& forall|i: int| 0 <= i < workers ==> #[trigger] owner.wvalue@[i] == initial_value
                &&& forall|i: int| 0 <= i < workers ==> #[trigger] owner.snapshot_spec()[i] == initial_value
                &&& owner.snapshot_spec().len() == workers
            },
    {
        if value_domain_size == 0 { return Err(ForkJoinBuildError::EmptyValueDomain); }
        if initial_value >= value_domain_size {
            return Err(ForkJoinBuildError::InitialValueOutOfRange);
        }
        Ok(Self { inner: ForkJoinCarrier::new_indexed(workers, value_domain_size, initial_value) })
    }

    /// Number of workers.
    pub fn len(&self) -> (length: usize)
        ensures length == self.state_spec().wstate@.len(),
    { self.inner.wstate.len() }

    /// Whether no workers are configured.
    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.state_spec().wstate@.len() == 0),
    { self.inner.wstate.is_empty() }

    /// Whether every worker has completed, as observed by the barrier owner.
    pub fn all_complete(&self) -> (complete: bool)
        ensures complete == self.state_spec().all_complete(), self.state_spec().inv(),
    {
        proof { use_type_invariant(&*self); }
        self.inner.all_complete_exec()
    }

    /// Current global phase.
    pub fn phase(&self) -> (phase: ForkJoinPhase)
        ensures phase == self.state_spec().phase,
    {
        self.inner.phase
    }

    /// Whether the output snapshot is ready.
    pub fn output_ready(&self) -> (ready: bool)
        ensures ready == self.state_spec().output_ready,
    { self.inner.output_ready }

    /// Read one worker lifecycle state.
    pub fn worker_state(&self, worker: usize) -> (state: Option<WorkerState>)
        ensures state == crate::modalities::fork_join::worker_at(self.state_spec().wstate@, worker as int),
    {
        if worker >= self.inner.wstate.len() { return None; }
        Some(self.inner.wstate.state_at(worker))
    }

    /// Read one worker's current value.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the worker index is in bounds")]
    pub fn worker_value(&self, worker: usize) -> (value: Option<u64>)
        ensures value == if worker < self.state_spec().wvalue@.len()
            { Some(self.state_spec().wvalue@[worker as int]) } else { None },
    {
        if worker < self.inner.wvalue.len() { Some(self.inner.wvalue[worker]) } else { None }
    }

    /// Read one stable output value after output production.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the output index is in bounds")]
    pub fn output(&self, worker: usize) -> (value: Option<u64>)
        ensures value == if self.state_spec().output_ready && worker < self.state_spec().wvalue@.len()
            { Some(self.state_spec().snapshot_spec()[worker as int]) } else { None },
            self.state_spec().inv(),
    {
        proof { use_type_invariant(self); }
        if self.inner.output_ready && worker < self.inner.wvalue.len() {
            Some(self.inner.output_values()[worker])
        } else { None }
    }

    /// Start one ready worker during the fork phase.
    #[must_use]
    pub fn start_worker(&mut self, worker: usize) -> (accepted: bool)
        ensures final(self).state_spec().inv(),
            final(self).state_spec().value_domain_size == old(self).state_spec().value_domain_size,
            final(self).state_spec().wvalue@ == old(self).state_spec().wvalue@,
            final(self).state_spec().phase == old(self).state_spec().phase,
            final(self).state_spec().output_ready == old(self).state_spec().output_ready,
            final(self).state_spec().snapshot_spec() == old(self).state_spec().snapshot_spec(),
            crate::modalities::fork_join::start_worker_action(old(self).state_spec().wstate@,
                final(self).state_spec().wstate@, old(self).state_spec().phase,
                worker as int, true, accepted),
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.start_worker(worker);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Complete one running worker with an in-domain value.
    #[must_use]
    pub fn complete_worker(&mut self, worker: usize, value: u64) -> (accepted: bool)
        ensures final(self).state_spec().inv(),
            final(self).state_spec().value_domain_size == old(self).state_spec().value_domain_size,
            final(self).state_spec().phase == old(self).state_spec().phase,
            final(self).state_spec().output_ready == old(self).state_spec().output_ready,
            final(self).state_spec().snapshot_spec() == old(self).state_spec().snapshot_spec(),
            crate::modalities::fork_join::complete_worker_action(old(self).state_spec().wstate@,
                final(self).state_spec().wstate@, old(self).state_spec().phase,
                worker as int, true, value < old(self).state_spec().value_domain_size, accepted),
            final(self).state_spec().wvalue@ == if accepted
                { old(self).state_spec().wvalue@.update(worker as int, value) } else { old(self).state_spec().wvalue@ },
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.complete_worker(worker, value);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Commit the barrier when every worker is complete.
    #[must_use]
    pub fn barrier(&mut self) -> (accepted: bool)
        ensures final(self).state_spec().inv(),
            final(self).state_spec().value_domain_size == old(self).state_spec().value_domain_size,
            final(self).state_spec().wstate@ == old(self).state_spec().wstate@,
            final(self).state_spec().wvalue@ == old(self).state_spec().wvalue@,
            final(self).state_spec().output_ready == old(self).state_spec().output_ready,
            final(self).state_spec().snapshot_spec() == old(self).state_spec().snapshot_spec(),
            crate::modalities::fork_join::barrier_action(old(self).state_spec().phase,
                final(self).state_spec().phase, true, old(self).state_spec().all_complete(), accepted),
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.barrier();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Produce the immutable output snapshot from the joined worker values.
    #[must_use]
    pub fn produce_output(&mut self) -> (accepted: bool)
        ensures final(self).state_spec().inv(),
            final(self).state_spec().value_domain_size == old(self).state_spec().value_domain_size,
            final(self).state_spec().wstate@ == old(self).state_spec().wstate@,
            final(self).state_spec().wvalue@ == old(self).state_spec().wvalue@,
            if accepted {
                final(self).state_spec().phase == ForkJoinPhase::Done
                    && final(self).state_spec().output_ready
                    && final(self).state_spec().snapshot_spec() == old(self).state_spec().wvalue@
            } else {
                final(self).state_spec().phase == old(self).state_spec().phase
                    && final(self).state_spec().output_ready == old(self).state_spec().output_ready
                    && final(self).state_spec().snapshot_spec() == old(self).state_spec().snapshot_spec()
            },
            crate::modalities::fork_join::produce_output_action(old(self).state_spec().phase,
                final(self).state_spec().phase, true, accepted),
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.produce_output();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }
}

/// Invalid step-graph configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum StepGraphBuildError {
    /// At least one edge endpoint is outside the node universe.
    EdgeEndpointOutOfRange,
    /// Duplicate edges are not admitted.
    DuplicateEdge,
}

/// One step's lifecycle state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StepState {
    /// A predecessor is incomplete.
    NotReady,
    /// All predecessors are complete.
    Ready,
    /// The step is running.
    Running,
    /// The step is complete.
    Complete,
}

/// A predecessor-governed directed step graph.
///
/// # Examples
///
/// ```rust
/// use automation_structures::StepGraph;
///
/// let mut graph = StepGraph::new(2, vec![(0, 1)])?;
/// assert!(graph.start(0));
/// assert!(graph.complete(0));
/// assert!(graph.become_ready(1));
/// # Ok::<(), automation_structures::StepGraphBuildError>(())
/// ```
pub struct StepGraph {
    inner: CheckedStepGraphCarrier,
}

impl StepGraph {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate edges and construct initial readiness states.
    ///
    /// # Errors
    ///
    /// Returns an error when an endpoint is outside the node universe or an edge is duplicated.
    pub fn new(num_nodes: usize, edges: Vec<(usize, usize)>)
        -> (result: Result<Self, StepGraphBuildError>) {
        if !step_edges_valid(&edges, num_nodes) {
            return Err(StepGraphBuildError::EdgeEndpointOutOfRange);
        }
        if !step_edges_distinct(&edges) { return Err(StepGraphBuildError::DuplicateEdge); }
        Ok(Self { inner: StepGraphCarrier::new_counted(num_nodes, edges) })
    }

    /// Number of steps.
    pub fn len(&self) -> usize { self.inner.num_nodes }

    /// Whether the graph has no steps.
    pub fn is_empty(&self) -> bool { self.inner.num_nodes == 0 }

    /// Number of directed predecessor edges.
    pub fn edge_count(&self) -> usize { self.inner.edges.len() }

    /// Observe the dependency owner's completion guard for a valid node.
    /// Returns `None` when the node is outside the graph.
    pub fn predecessors_complete(&self, node: usize) -> Option<bool> {
        proof { use_type_invariant(&*self); }
        if node >= self.inner.num_nodes { return None; }
        Some(self.inner.predecessors_complete_exec(node))
    }

    /// Read one directed predecessor edge.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the edge index is in bounds")]
    pub fn edge(&self, index: usize) -> Option<(usize, usize)> {
        if index < self.inner.edges.len() { Some(self.inner.edges[index]) } else { None }
    }

    /// Read one step lifecycle state.
    pub fn state(&self, node: usize) -> Option<StepState> {
        if node >= self.inner.nstate.len() { return None; }
        Some(self.inner.nstate.state_at(node))
    }

    /// Promote a blocked node after every predecessor completes.
    #[must_use]
    pub fn become_ready(&mut self, node: usize) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = step_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.become_ready(node);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Start one ready step.
    #[must_use]
    pub fn start(&mut self, node: usize) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        if !self.inner.can_start_ready(node) { return false; }
        let mut carrier = step_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.start_running(node);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Complete one running step.
    #[must_use]
    pub fn complete(&mut self, node: usize) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = step_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.complete_node(node);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Whether every step is complete.
    pub fn is_done(&self) -> bool {
        proof { use_type_invariant(&*self); }
        self.inner.all_nodes_complete()
    }
}

/// Invalid stream-graph configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum StreamGraphBuildError {
    /// Only three- and four-stage chains are currently represented.
    UnsupportedChainLength,
    /// Every inter-stage queue needs positive capacity.
    ZeroCapacity,
    /// The record value domain must be nonempty.
    EmptyRecordDomain,
    /// Physical queue reservation failed before an owner was constructed.
    StorageUnavailable,
}

/// A bounded three- or four-stage FIFO stream graph.
///
/// The default contiguous layout preserves borrowed queue slices; removing its
/// first record shifts the remaining queue. Select `FifoStorage` with
/// [`Self::try_with_storage`] for pre-reserved constant-time FIFO actions and
/// borrowed queue iterators. Both layouts use the same transition owner.
///
/// # Examples
///
/// ```rust
/// use automation_structures::StreamGraph;
///
/// let mut graph = StreamGraph::new(3, 1, 1, 4)?;
/// assert!(graph.ingest(3));
/// assert!(graph.advance_first());
/// assert_eq!(graph.consume(), Some(3));
/// assert!(graph.is_done());
/// # Ok::<(), automation_structures::StreamGraphBuildError>(())
/// ```
pub struct StreamGraph<S: BufferLayout<u64> = ContiguousStorage> {
    inner: StreamGraphCarrier<S>,
}

impl StreamGraph {
    /// Validate and construct an empty stream graph.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsupported chain length, zero queue capacity, or an
    /// empty record domain.
    pub fn new(chain_length: usize, capacity: usize, max_inputs: usize, record_domain_size: u64)
        -> (result: Result<Self, StreamGraphBuildError>)
        ensures result is Ok ==> result->Ok_0.config_spec()
                == (chain_length, capacity, max_inputs, record_domain_size),
            result is Ok ==> result->Ok_0.first_queue_spec() == Seq::<u64>::empty(),
            result is Ok ==> result->Ok_0.second_queue_spec() == Seq::<u64>::empty(),
            result is Ok ==> result->Ok_0.third_queue_spec() == Seq::<u64>::empty(),
            result is Ok ==> result->Ok_0.ingested_spec() == 0,
            result is Ok ==> result->Ok_0.emitted_spec() == 0,
            result is Ok <==> ((chain_length == 3 || chain_length == 4)
                && capacity > 0 && record_domain_size > 0),
            matches!(result, Err(StreamGraphBuildError::UnsupportedChainLength))
                <==> (chain_length != 3 && chain_length != 4),
            matches!(result, Err(StreamGraphBuildError::ZeroCapacity))
                <==> ((chain_length == 3 || chain_length == 4) && capacity == 0),
            matches!(result, Err(StreamGraphBuildError::EmptyRecordDomain))
                <==> ((chain_length == 3 || chain_length == 4) && capacity > 0 && record_domain_size == 0),
    {
        if chain_length != 3 && chain_length != 4 {
            return Err(StreamGraphBuildError::UnsupportedChainLength);
        }
        if capacity == 0 { return Err(StreamGraphBuildError::ZeroCapacity); }
        if record_domain_size == 0 { return Err(StreamGraphBuildError::EmptyRecordDomain); }
        Ok(Self { inner: StreamGraphCarrier::new(
            chain_length, capacity, max_inputs, record_domain_size,
        ) })
    }
}

impl<S: BufferLayout<u64>> StreamGraph<S> {
    /// Erased view of the one retained linear-stream transition owner.
    pub closed spec fn state_spec(&self) -> StreamGraphCarrier<S> { self.inner }

    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Source occurrence count observed from the retained Counter.
    pub closed spec fn ingested_spec(&self) -> nat { self.inner.ingested.value_spec() }
    /// Sink occurrence count observed from the retained Counter.
    pub closed spec fn emitted_spec(&self) -> nat { self.inner.emitted.value_spec() }
    /// Immutable chain length, edge capacity, input bound and record domain.
    pub closed spec fn config_spec(&self) -> (usize, usize, usize, u64) {
        (self.inner.chain_length, self.inner.q1.capacity,
            self.inner.max_inputs, self.inner.record_domain_size)
    }
    /// Actual first Buffer's logical FIFO contents.
    pub closed spec fn first_queue_spec(&self) -> Seq<u64> { self.inner.q1.values@ }
    /// Actual second Buffer's logical FIFO contents.
    pub closed spec fn second_queue_spec(&self) -> Seq<u64> { self.inner.q2.values@ }
    /// Actual optional third Buffer's logical FIFO contents.
    pub closed spec fn third_queue_spec(&self) -> Seq<u64> { self.inner.q3.values@ }
    /// Maximum number of source records admitted by this run.
    pub fn max_inputs(&self) -> (bound: usize)
        ensures bound == self.config_spec().2,
    { self.inner.max_inputs }

    /// Exclusive upper bound of record values.
    pub fn record_domain_size(&self) -> (domain: u64)
        ensures domain == self.config_spec().3,
    { self.inner.record_domain_size }

    /// Construct the selected layout and reserve each active queue before admission.
    ///
    /// # Errors
    /// Returns the existing configuration errors before reservation, or
    /// `StorageUnavailable` if physical queue storage cannot be reserved.
    pub fn try_with_storage(chain_length: usize, capacity: usize, max_inputs: usize,
        record_domain_size: u64) -> (result: Result<Self, StreamGraphBuildError>)
        ensures result is Ok ==> result->Ok_0.config_spec()
                == (chain_length, capacity, max_inputs, record_domain_size),
            result is Ok ==> result->Ok_0.first_queue_spec() == Seq::<u64>::empty(),
            result is Ok ==> result->Ok_0.second_queue_spec() == Seq::<u64>::empty(),
            result is Ok ==> result->Ok_0.third_queue_spec() == Seq::<u64>::empty(),
            result is Ok ==> result->Ok_0.ingested_spec() == 0,
            result is Ok ==> result->Ok_0.emitted_spec() == 0,
            matches!(result, Err(StreamGraphBuildError::UnsupportedChainLength))
                <==> (chain_length != 3 && chain_length != 4),
            matches!(result, Err(StreamGraphBuildError::ZeroCapacity))
                <==> ((chain_length == 3 || chain_length == 4) && capacity == 0),
            matches!(result, Err(StreamGraphBuildError::EmptyRecordDomain))
                <==> ((chain_length == 3 || chain_length == 4) && capacity > 0 && record_domain_size == 0),
            matches!(result, Err(StreamGraphBuildError::StorageUnavailable))
                ==> ((chain_length == 3 || chain_length == 4) && capacity > 0 && record_domain_size > 0),
    {
        if chain_length != 3 && chain_length != 4 {
            return Err(StreamGraphBuildError::UnsupportedChainLength);
        }
        if capacity == 0 { return Err(StreamGraphBuildError::ZeroCapacity); }
        if record_domain_size == 0 { return Err(StreamGraphBuildError::EmptyRecordDomain); }
        let q1 = match Buffer::<u64, S>::try_with_storage(capacity) {
            Ok(queue) => queue, Err(_) => return Err(StreamGraphBuildError::StorageUnavailable),
        };
        let q2 = match Buffer::<u64, S>::try_with_storage(capacity) {
            Ok(queue) => queue, Err(_) => return Err(StreamGraphBuildError::StorageUnavailable),
        };
        let q3 = if chain_length == 4 {
            match Buffer::<u64, S>::try_with_storage(capacity) {
                Ok(queue) => queue, Err(_) => return Err(StreamGraphBuildError::StorageUnavailable),
            }
        } else { Buffer::<u64, S>::with_storage(capacity) };
        Ok(Self { inner: StreamGraphCarrier::<S>::with_buffers(
            chain_length, q1, q2, q3, max_inputs, record_domain_size,
        ) })
    }

    /// Number of execution stages.
    pub fn chain_length(&self) -> (stages: usize)
        ensures stages == self.config_spec().0,
    { self.inner.chain_length }

    /// Per-edge FIFO capacity.
    pub fn capacity(&self) -> (capacity: usize)
        ensures capacity == self.config_spec().1,
            self.state_spec().inv(),
            self.state_spec().some_action_enabled(),
            self.config_spec() == (self.state_spec().chain_length,
                self.state_spec().q1.capacity, self.state_spec().max_inputs,
                self.state_spec().record_domain_size),
            self.ingested_spec() == self.state_spec().ingested.value_spec(),
            self.emitted_spec() == self.state_spec().emitted.value_spec(),
            self.first_queue_spec() == self.state_spec().q1.values@,
            self.second_queue_spec() == self.state_spec().q2.values@,
            self.third_queue_spec() == self.state_spec().q3.values@,
    {
        proof {
            use_type_invariant(self);
            self.inner.lemma_some_action_enabled();
        }
        self.inner.capacity()
    }

    /// Records admitted at the source.
    #[expect(clippy::cast_possible_truncation, reason = "the private stream invariant bounds the source Counter by max_inputs: usize")]
    pub fn ingested(&self) -> (count: usize)
        ensures count == self.ingested_spec(),
            self.ingested_spec() == self.first_queue_spec().len()
                + self.second_queue_spec().len() + self.third_queue_spec().len()
                + self.emitted_spec(),
    {
        proof { use_type_invariant(self); }
        self.inner.ingested.value() as usize
    }

    /// Records consumed at the sink.
    #[expect(clippy::cast_possible_truncation, reason = "the private stream invariant bounds the sink Counter by max_inputs: usize")]
    pub fn emitted(&self) -> (count: usize)
        ensures count == self.emitted_spec(),
    {
        proof { use_type_invariant(self); }
        self.inner.emitted.value() as usize
    }

    /// Current depth of the first queue.
    pub fn first_queue_len(&self) -> (length: usize)
        ensures length == self.first_queue_spec().len(),
    { self.inner.q1.len() }

    /// Current depth of the second queue.
    pub fn second_queue_len(&self) -> (length: usize)
        ensures length == self.second_queue_spec().len(),
    { self.inner.q2.len() }

    /// Current depth of the optional third queue.
    pub fn third_queue_len(&self) -> (length: usize)
        ensures length == self.third_queue_spec().len(),
    { self.inner.q3.len() }

    /// Whether at least one modeled transition is enabled in the current state.
    ///
    /// This state-level observation does not promise that a scheduler will choose an action.
    pub fn has_enabled_action(&self) -> (enabled: bool)
        ensures enabled == (
            (self.ingested_spec() < self.config_spec().2
                && self.first_queue_spec().len() < self.config_spec().1)
            || (self.first_queue_spec().len() > 0 && self.second_queue_spec().len() < self.config_spec().1)
            || (self.config_spec().0 == 3 && self.second_queue_spec().len() > 0)
            || (self.config_spec().0 == 4 && self.second_queue_spec().len() > 0
                && self.third_queue_spec().len() < self.config_spec().1)
            || (self.config_spec().0 == 4 && self.third_queue_spec().len() > 0)
            || (self.ingested_spec() == self.config_spec().2
                && self.first_queue_spec().len() == 0 && self.second_queue_spec().len() == 0
                && self.third_queue_spec().len() == 0)),
    {
        proof { use_type_invariant(self); }
        self.inner.some_action_enabled_exec()
    }

    /// Admit one source record if its value, input bound, and backpressure permit it.
    #[must_use]
    pub fn ingest(&mut self, value: u64) -> (accepted: bool)
        ensures accepted == (value < old(self).config_spec().3
                && old(self).ingested_spec() < old(self).config_spec().2
                && old(self).first_queue_spec().len() < old(self).config_spec().1),
            final(self).config_spec() == old(self).config_spec(),
            final(self).first_queue_spec() == if accepted {
                old(self).first_queue_spec().push(value)
            } else { old(self).first_queue_spec() },
            final(self).second_queue_spec() == old(self).second_queue_spec(),
            final(self).third_queue_spec() == old(self).third_queue_spec(),
            final(self).ingested_spec() == old(self).ingested_spec()
                + if accepted { 1nat } else { 0nat },
            final(self).emitted_spec() == old(self).emitted_spec(),
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.source_ingest(value);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Transfer one FIFO record across the first internal stage.
    #[must_use]
    pub fn advance_first(&mut self) -> (accepted: bool)
        ensures accepted == (old(self).first_queue_spec().len() > 0
                && old(self).second_queue_spec().len() < old(self).config_spec().1),
            final(self).config_spec() == old(self).config_spec(),
            final(self).first_queue_spec() == if accepted {
                old(self).first_queue_spec().skip(1)
            } else { old(self).first_queue_spec() },
            final(self).second_queue_spec() == if accepted {
                old(self).second_queue_spec().push(old(self).first_queue_spec()[0])
            } else { old(self).second_queue_spec() },
            final(self).third_queue_spec() == old(self).third_queue_spec(),
            final(self).ingested_spec() == old(self).ingested_spec(),
            final(self).emitted_spec() == old(self).emitted_spec(),
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.middle2_fire();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Transfer one FIFO record across the optional four-stage link.
    #[must_use]
    pub fn advance_second(&mut self) -> (accepted: bool)
        ensures accepted == (old(self).config_spec().0 == 4
                && old(self).second_queue_spec().len() > 0
                && old(self).third_queue_spec().len() < old(self).config_spec().1),
            final(self).config_spec() == old(self).config_spec(),
            final(self).first_queue_spec() == old(self).first_queue_spec(),
            final(self).second_queue_spec() == if accepted {
                old(self).second_queue_spec().skip(1)
            } else { old(self).second_queue_spec() },
            final(self).third_queue_spec() == if accepted {
                old(self).third_queue_spec().push(old(self).second_queue_spec()[0])
            } else { old(self).third_queue_spec() },
            final(self).ingested_spec() == old(self).ingested_spec(),
            final(self).emitted_spec() == old(self).emitted_spec(),
    {
        proof { use_type_invariant(&*self); }
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.middle3_fire();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Consume and return the next FIFO record at the sink.
    pub fn consume(&mut self) -> (value: Option<u64>)
        ensures value == if old(self).config_spec().0 == 3 {
                if old(self).second_queue_spec().len() > 0 {
                    Some(old(self).second_queue_spec()[0])
                } else { None }
            } else {
                if old(self).third_queue_spec().len() > 0 {
                    Some(old(self).third_queue_spec()[0])
                } else { None }
            },
            final(self).config_spec() == old(self).config_spec(),
            final(self).first_queue_spec() == old(self).first_queue_spec(),
            final(self).second_queue_spec() == if value is Some && old(self).config_spec().0 == 3 {
                old(self).second_queue_spec().skip(1) } else { old(self).second_queue_spec() },
            final(self).third_queue_spec() == if value is Some && old(self).config_spec().0 == 4 {
                old(self).third_queue_spec().skip(1) } else { old(self).third_queue_spec() },
            final(self).ingested_spec() == old(self).ingested_spec(),
            final(self).emitted_spec() == old(self).emitted_spec()
                + if value is Some { 1nat } else { 0nat },
    {
        proof { use_type_invariant(&*self); }
        let value = if self.inner.chain_length == 3 {
            match self.inner.q2.values.value_at(0) {
                Some(value) => *value, None => return None,
            }
        } else {
            match self.inner.q3.values.value_at(0) {
                Some(value) => *value, None => return None,
            }
        };
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.sink_consume();
        if !accepted {
            core::mem::swap(&mut self.inner, &mut carrier);
            return None;
        }
        core::mem::swap(&mut self.inner, &mut carrier);
        Some(value)
    }

    /// Whether the input bound is reached and every queue is drained.
    pub fn is_done(&self) -> (complete: bool)
        ensures complete == (self.ingested_spec() == self.config_spec().2
            && self.first_queue_spec().len() == 0
            && self.second_queue_spec().len() == 0
            && self.third_queue_spec().len() == 0),
    {
        proof { use_type_invariant(&*self); }
        self.inner.input_drained()
    }
}

#[expect(clippy::indexing_slicing, reason = "the loop proves the edge index is in bounds")]
#[expect(clippy::arithmetic_side_effects, reason = "the loop proves the cursor remains within the vector")]
#[expect(clippy::ptr_arg, reason = "Verus sequence-view contracts are stated over Vec in this checked boundary")]
fn step_edges_valid(edges: &Vec<(usize, usize)>, num_nodes: usize) -> (valid: bool)
    ensures valid == StepGraphCarrier::edges_valid(edges@, num_nodes),
{
    let mut index = 0;
    while index < edges.len()
        invariant
            index <= edges.len(),
            forall|i: int| 0 <= i < index ==>
                #[trigger] edges@[i].0 < num_nodes && edges@[i].1 < num_nodes,
        decreases edges.len() - index,
    {
        if edges[index].0 >= num_nodes || edges[index].1 >= num_nodes {
            assert(!StepGraphCarrier::edges_valid(edges@, num_nodes));
            return false;
        }
        index = index + 1;
    }
    true
}

#[expect(clippy::indexing_slicing, reason = "the nested loops prove both edge indices are in bounds")]
#[expect(clippy::arithmetic_side_effects, reason = "the loops prove both cursors remain within the vector")]
#[expect(clippy::ptr_arg, reason = "Verus sequence-view contracts are stated over Vec in this checked boundary")]
fn step_edges_distinct_quadratic(edges: &Vec<(usize, usize)>) -> (distinct: bool)
    ensures distinct == StepGraphCarrier::edges_distinct(edges@),
{
    let mut left = 0;
    while left < edges.len()
        invariant
            left <= edges.len(),
            forall|i: int, j: int| 0 <= i < left && 0 <= j < edges.len() && i != j
                ==> #[trigger] edges@[i] != #[trigger] edges@[j],
        decreases edges.len() - left,
    {
        let mut right = left + 1;
        while right < edges.len()
            invariant
                left < edges.len(),
                left + 1 <= right <= edges.len(),
                forall|j: int| left < j < right ==> edges@[left as int] != edges@[j],
            decreases edges.len() - right,
        {
            if edges[left].0 == edges[right].0 && edges[left].1 == edges[right].1 {
                assert(!StepGraphCarrier::edges_distinct(edges@));
                return false;
            }
            right = right + 1;
        }
        left = left + 1;
    }
    true
}

// Pure borrowed edge keys; OrderingPass owns the temporary permutation and sort.
struct StepEdgeOrder<'a> {
    edges: &'a Vec<(usize, usize)>,
}
impl PositionOrder for StepEdgeOrder<'_> {
    closed spec fn domain_len(&self) -> nat { self.edges@.len() }
    closed spec fn key_le(&self, left: usize, right: usize) -> bool {
        let left = self.edges@[left as int];
        let right = self.edges@[right as int];
        left.0 < right.0 || (left.0 == right.0 && left.1 <= right.1)
    }
    proof fn establish(&self) {
        assert forall|a: usize| a < self.domain_len() implies #[trigger] self.key_le(a, a) by {}
        assert forall|a: usize, b: usize| a < self.domain_len() && b < self.domain_len()
            implies #[trigger] self.key_le(a, b) || self.key_le(b, a) by {}
        assert forall|a: usize, b: usize, c: usize|
            a < self.domain_len() && b < self.domain_len() && c < self.domain_len()
            && #[trigger] self.key_le(a, b) && #[trigger] self.key_le(b, c)
            implies self.key_le(a, c) by {}
    }
    fn len(&self) -> (length: usize) { self.edges.len() }
    #[expect(clippy::indexing_slicing, reason = "PositionOrder bounds both immutable edge positions")]
    fn compare(&self, left: usize, right: usize) -> (ordering: i8) {
        let left = self.edges[left];
        let right = self.edges[right];
        if left.0 < right.0 || (left.0 == right.0 && left.1 < right.1) { -1 }
        else if left.0 == right.0 && left.1 == right.1 { 0 } else { 1 }
    }
}

proof fn adjacent_step_edges_are_distinct(order: &StepEdgeOrder<'_>, positions: Seq<usize>)
    requires
        order.edges@.len() <= usize::MAX,
        crate::connectives::ordering_pass::permutation(positions, order.edges@.len()),
        crate::connectives::ordering_pass::arranged(positions, order),
        forall|rank: int| 1 <= rank < positions.len() ==>
            #[trigger] order.edges@[positions[rank - 1] as int] != #[trigger] order.edges@[positions[rank] as int],
    ensures StepGraphCarrier::edges_distinct(order.edges@),
{
    let edges = order.edges@;
    assert forall|i: int, j: int| 0 <= i < edges.len() && 0 <= j < edges.len() && i != j
        implies #[trigger] edges[i] != #[trigger] edges[j] by {
        assert(0 <= i <= usize::MAX && 0 <= j <= usize::MAX);
        let original_i = i as usize;
        let original_j = j as usize;
        assert(original_i as int == i && original_j as int == j);
        assert(positions.contains(original_i));
        assert(positions.contains(original_j));
        let left = choose|rank: int| 0 <= rank < positions.len()
            && positions[rank] == original_i;
        let right = choose|rank: int| 0 <= rank < positions.len()
            && positions[rank] == original_j;
        assert(0 <= left < positions.len() && positions[left] as int == i);
        assert(0 <= right < positions.len() && positions[right] as int == j);
        assert(left != right);
        if edges[i] == edges[j] {
            let first = if left < right { left } else { right };
            let last = if left < right { right } else { left };
            assert(0 <= first < last < positions.len());
            assert(positions[last - 1] < edges.len());
            if first < last - 1 {
                assert(crate::connectives::ordering_pass::position_le(order, positions[first], positions[last - 1]));
            } else {
                assert(first == last - 1);
                assert(order.key_le(positions[first], positions[last - 1]));
            }
            assert(crate::connectives::ordering_pass::position_le(order, positions[last - 1], positions[last]));
            assert(order.key_le(positions[first], positions[last - 1]));
            assert(order.key_le(positions[last - 1], positions[last]));
            let lower = edges[positions[first] as int];
            let middle = edges[positions[last - 1] as int];
            let upper = edges[positions[last] as int];
            assert(lower == upper);
            assert(lower.0 <= middle.0 && middle.0 <= upper.0);
            assert(middle.0 == upper.0);
            assert(lower.1 <= middle.1 && middle.1 <= upper.1);
            assert(middle == upper);
            assert(false);
        }
    }
}

#[expect(clippy::indexing_slicing, reason = "the permutation certificate and adjacent-rank guard bound every read")]
#[expect(clippy::arithmetic_side_effects, reason = "the adjacent rank is positive and advances only below the admitted length")]
fn step_edges_distinct(edges: &Vec<(usize, usize)>) -> (distinct: bool)
    ensures distinct == StepGraphCarrier::edges_distinct(edges@),
{
    if edges.len() < 2 { return true; }
    if edges.len() <= 32 { return step_edges_distinct_quadratic(edges); }
    let order = StepEdgeOrder { edges };
    let positions = match try_arrange_indices(edges.len(), &order) {
        Ok(positions) => positions,
        Err(_) => return step_edges_distinct_quadratic(edges),
    };
    let mut rank: usize = 1;
    while rank < positions.len()
        invariant
            1 <= rank <= positions.len(),
            crate::connectives::ordering_pass::permutation(positions@, edges@.len()),
            crate::connectives::ordering_pass::arranged(positions@, &order),
            forall|i: int| 1 <= i < rank ==>
                #[trigger] edges@[positions@[i - 1] as int] != #[trigger] edges@[positions@[i] as int],
        decreases positions.len() - rank,
    {
        let left = positions[rank - 1];
        let right = positions[rank];
        if edges[left].0 == edges[right].0 && edges[left].1 == edges[right].1 {
            assert(left != right);
            assert(!StepGraphCarrier::edges_distinct(edges@));
            return false;
        }
        rank = rank + 1;
    }
    proof { adjacent_step_edges_are_distinct(&order, positions@); }
    true
}

fn sequential_sentinel() -> (carrier: SequentialCarrier)
    ensures carrier.inv(),
{ SequentialCarrier::new(1, 1, 0) }

fn fork_join_sentinel() -> (carrier: CheckedForkJoinCarrier)
    ensures carrier.inv(),
{ ForkJoinCarrier::new_indexed(0, 1, 0) }

fn step_graph_sentinel() -> (carrier: CheckedStepGraphCarrier)
    ensures carrier.inv(),
{
    let edges: Vec<(usize, usize)> = Vec::new();
    StepGraphCarrier::new_counted(0, edges)
}

fn stream_graph_sentinel<S: BufferLayout<u64>>() -> (carrier: StreamGraphCarrier<S>)
    ensures carrier.inv(),
{
    StreamGraphCarrier::<S>::with_buffers(3, Buffer::<u64, S>::with_storage(1),
        Buffer::<u64, S>::with_storage(1), Buffer::<u64, S>::with_storage(1), 0, 1)
}

}

impl Sequential {
    /// Exclusive upper bound of carried values.
    pub fn value_domain_size(&self) -> u64 {
        self.inner.value_domain_size
    }

    /// Borrow completed-step values in execution order.
    pub fn history_values(&self) -> &[u64] {
        self.inner.history.as_slice()
    }
}

impl ForkJoin {
    /// Exclusive upper bound of worker values.
    pub fn value_domain_size(&self) -> u64 {
        self.inner.value_domain_size
    }

    /// Borrow worker lifecycle states by worker index.
    pub fn worker_states(&self) -> &[WorkerState] {
        self.inner.wstate.as_slice()
    }

    /// Borrow current worker values by worker index.
    pub fn worker_values(&self) -> &[u64] {
        self.inner.wvalue.as_slice()
    }

    /// Borrow the stable output snapshot after output production.
    pub fn outputs(&self) -> Option<&[u64]> {
        if self.inner.output_ready {
            Some(self.inner.output_values())
        } else {
            None
        }
    }
}

impl StepGraph {
    /// Borrow directed predecessor edges in configured order.
    pub fn edges(&self) -> &[(usize, usize)] {
        self.inner.edges.as_slice()
    }

    /// Borrow all current step states by node index.
    pub fn states(&self) -> &[StepState] {
        self.inner.nstate.as_slice()
    }
}

impl StreamGraph {
    /// Borrow records waiting at the first FIFO edge.
    pub fn first_queue(&self) -> &[u64] {
        self.inner.q1.values.as_slice()
    }

    /// Borrow records waiting at the second FIFO edge.
    pub fn second_queue(&self) -> &[u64] {
        self.inner.q2.values.as_slice()
    }

    /// Borrow records waiting at the optional third FIFO edge.
    pub fn third_queue(&self) -> &[u64] {
        self.inner.q3.values.as_slice()
    }
}

impl StreamGraph<FifoStorage> {
    /// Borrow the first queue in FIFO order without copying or making it contiguous.
    pub fn first_queue(&self) -> std::collections::vec_deque::Iter<'_, u64> {
        self.inner.q1.values.values.iter()
    }
    /// Borrow the second queue in FIFO order without copying or making it contiguous.
    pub fn second_queue(&self) -> std::collections::vec_deque::Iter<'_, u64> {
        self.inner.q2.values.values.iter()
    }
    /// Borrow the optional third queue in FIFO order without copying or making it contiguous.
    pub fn third_queue(&self) -> std::collections::vec_deque::Iter<'_, u64> {
        self.inner.q3.values.values.iter()
    }
}

impl_observational_debug!(Sequential, "Sequential",
    "steps" => steps,
    "completed" => completed,
    "value" => value,
    "active" => is_active,
    "done" => is_done,
);
impl_observational_debug!(ForkJoin, "ForkJoin",
    "len" => len,
    "phase" => phase,
    "output_ready" => output_ready,
);
impl_observational_debug!(StepGraph, "StepGraph",
    "len" => len,
    "edge_count" => edge_count,
    "done" => is_done,
);
impl<S: BufferLayout<u64>> core::fmt::Debug for StreamGraph<S> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("StreamGraph")
            .field("chain_length", &self.chain_length())
            .field("capacity", &self.capacity())
            .field("has_enabled_action", &self.has_enabled_action())
            .field("ingested", &self.ingested())
            .field("emitted", &self.emitted())
            .field("first_queue_len", &self.first_queue_len())
            .field("second_queue_len", &self.second_queue_len())
            .field("third_queue_len", &self.third_queue_len())
            .field("done", &self.is_done())
            .finish()
    }
}

impl_public_error!(SequentialBuildError, {
    Self::NoSteps => "sequential execution requires at least one step",
    Self::EmptyValueDomain => "sequential value domain is empty",
    Self::InitialValueOutOfRange => "initial sequential value is outside its domain",
});
impl_public_error!(ForkJoinBuildError, {
    Self::EmptyValueDomain => "fork-join value domain is empty",
    Self::InitialValueOutOfRange => "initial worker value is outside its domain",
});
impl_public_error!(StepGraphBuildError, {
    Self::EdgeEndpointOutOfRange => "step-graph edge endpoint is outside the node universe",
    Self::DuplicateEdge => "step graph contains a duplicate edge",
});
impl_public_error!(StreamGraphBuildError, {
    Self::UnsupportedChainLength => "stream graph supports only three- or four-stage chains",
    Self::ZeroCapacity => "stream-graph queue capacity must be positive",
    Self::EmptyRecordDomain => "stream-graph record domain is empty",
    Self::StorageUnavailable => "stream-graph queue storage could not be reserved",
});
