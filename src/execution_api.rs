//! Checked public entry points for reusable execution modalities.

use crate::modalities::fork_join::ForkJoin as ForkJoinCarrier;
use crate::modalities::sequential::Sequential as SequentialCarrier;
use crate::modalities::step_graph::StepGraph as StepGraphCarrier;
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
pub struct Sequential {
    inner: SequentialCarrier,
}

impl Sequential {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate and construct an inactive sequential execution.
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
    pub fn is_done(&self) -> bool { self.inner.pc == self.inner.steps && !self.inner.active }

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
pub struct ForkJoin {
    inner: ForkJoinCarrier,
}

impl ForkJoin {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate and construct a fork-join execution.
    pub fn new(workers: usize, value_domain_size: u64, initial_value: u64)
        -> (result: Result<Self, ForkJoinBuildError>) {
        if value_domain_size == 0 { return Err(ForkJoinBuildError::EmptyValueDomain); }
        if initial_value >= value_domain_size {
            return Err(ForkJoinBuildError::InitialValueOutOfRange);
        }
        Ok(Self { inner: ForkJoinCarrier::new(workers, value_domain_size, initial_value) })
    }

    /// Number of workers.
    pub fn len(&self) -> usize { self.inner.wstate.len() }

    /// Whether no workers are configured.
    pub fn is_empty(&self) -> bool { self.inner.wstate.is_empty() }

    /// Current global phase.
    pub fn phase(&self) -> ForkJoinPhase {
        if self.inner.phase == 0 { ForkJoinPhase::Fork }
        else if self.inner.phase == 1 { ForkJoinPhase::Join }
        else { ForkJoinPhase::Done }
    }

    /// Whether the output snapshot is ready.
    pub fn output_ready(&self) -> bool { self.inner.output_ready }

    /// Read one worker lifecycle state.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the worker index is in bounds")]
    pub fn worker_state(&self, worker: usize) -> Option<WorkerState> {
        if worker >= self.inner.wstate.len() { return None; }
        Some(if self.inner.wstate[worker] == 0 { WorkerState::Ready }
            else if self.inner.wstate[worker] == 1 { WorkerState::Running }
            else { WorkerState::Complete })
    }

    /// Read one worker's current value.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the worker index is in bounds")]
    pub fn worker_value(&self, worker: usize) -> Option<u64> {
        if worker < self.inner.wvalue.len() { Some(self.inner.wvalue[worker]) } else { None }
    }

    /// Read one stable output value after output production.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the output index is in bounds")]
    pub fn output(&self, worker: usize) -> Option<u64> {
        if self.inner.output_ready && worker < self.inner.output_snapshot.len() {
            Some(self.inner.output_snapshot[worker])
        } else { None }
    }

    /// Start one ready worker during the fork phase.
    #[must_use]
    pub fn start_worker(&mut self, worker: usize) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.start_worker(worker);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Complete one running worker with an in-domain value.
    #[must_use]
    pub fn complete_worker(&mut self, worker: usize, value: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.complete_worker(worker, value);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Commit the barrier when every worker is complete.
    #[must_use]
    pub fn barrier(&mut self) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = fork_join_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.barrier();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Produce the immutable output snapshot from the joined worker values.
    #[must_use]
    pub fn produce_output(&mut self) -> (accepted: bool) {
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
pub struct StepGraph {
    inner: StepGraphCarrier,
}

impl StepGraph {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate edges and construct initial readiness states.
    pub fn new(num_nodes: usize, edges: Vec<(usize, usize)>)
        -> (result: Result<Self, StepGraphBuildError>) {
        if !step_edges_valid(&edges, num_nodes) {
            return Err(StepGraphBuildError::EdgeEndpointOutOfRange);
        }
        if !step_edges_distinct(&edges) { return Err(StepGraphBuildError::DuplicateEdge); }
        Ok(Self { inner: StepGraphCarrier::new(num_nodes, edges) })
    }

    /// Number of steps.
    pub fn len(&self) -> usize { self.inner.num_nodes }

    /// Whether the graph has no steps.
    pub fn is_empty(&self) -> bool { self.inner.num_nodes == 0 }

    /// Number of directed predecessor edges.
    pub fn edge_count(&self) -> usize { self.inner.edges.len() }

    /// Read one directed predecessor edge.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the edge index is in bounds")]
    pub fn edge(&self, index: usize) -> Option<(usize, usize)> {
        if index < self.inner.edges.len() { Some(self.inner.edges[index]) } else { None }
    }

    /// Read one step lifecycle state.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the node index is in bounds")]
    pub fn state(&self, node: usize) -> Option<StepState> {
        if node >= self.inner.nstate.len() { return None; }
        Some(if self.inner.nstate[node] == 0 { StepState::NotReady }
            else if self.inner.nstate[node] == 1 { StepState::Ready }
            else if self.inner.nstate[node] == 2 { StepState::Running }
            else { StepState::Complete })
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
    #[expect(clippy::indexing_slicing, reason = "the loop proves the state index is in bounds")]
    #[expect(clippy::arithmetic_side_effects, reason = "the loop proves the cursor remains within the vector")]
    pub fn is_done(&self) -> bool {
        let mut index = 0;
        while index < self.inner.nstate.len()
            invariant index <= self.inner.nstate.len(),
            decreases self.inner.nstate.len() - index,
        {
            if self.inner.nstate[index] != 3 { return false; }
            index = index + 1;
        }
        true
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
}

/// A bounded three- or four-stage FIFO stream graph.
pub struct StreamGraph {
    inner: StreamGraphCarrier,
}

impl StreamGraph {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Validate and construct an empty stream graph.
    pub fn new(chain_length: usize, capacity: usize, max_inputs: usize, record_domain_size: u64)
        -> (result: Result<Self, StreamGraphBuildError>) {
        if chain_length != 3 && chain_length != 4 {
            return Err(StreamGraphBuildError::UnsupportedChainLength);
        }
        if capacity == 0 { return Err(StreamGraphBuildError::ZeroCapacity); }
        if record_domain_size == 0 { return Err(StreamGraphBuildError::EmptyRecordDomain); }
        Ok(Self { inner: StreamGraphCarrier::new(
            chain_length, capacity, max_inputs, record_domain_size,
        ) })
    }

    /// Number of execution stages.
    pub fn chain_length(&self) -> usize { self.inner.chain_length }

    /// Per-edge FIFO capacity.
    pub fn capacity(&self) -> usize { self.inner.capacity }

    /// Records admitted at the source.
    pub fn ingested(&self) -> usize { self.inner.ingested }

    /// Records consumed at the sink.
    pub fn emitted(&self) -> usize { self.inner.emitted }

    /// Current depth of the first queue.
    pub fn first_queue_len(&self) -> usize { self.inner.q1.len() }

    /// Current depth of the second queue.
    pub fn second_queue_len(&self) -> usize { self.inner.q2.len() }

    /// Current depth of the optional third queue.
    pub fn third_queue_len(&self) -> usize { self.inner.q3.len() }

    /// Admit one source record if its value, input bound, and backpressure permit it.
    #[must_use]
    pub fn ingest(&mut self, value: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.source_ingest(value);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Transfer one FIFO record across the first internal stage.
    #[must_use]
    pub fn advance_first(&mut self) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.middle2_fire();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Transfer one FIFO record across the optional four-stage link.
    #[must_use]
    pub fn advance_second(&mut self) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = stream_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.middle3_fire();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Consume and return the next FIFO record at the sink.
    #[expect(clippy::indexing_slicing, reason = "the queue guards prove the sink head is present")]
    pub fn consume(&mut self) -> (value: Option<u64>) {
        proof { use_type_invariant(&*self); }
        let value = if self.inner.chain_length == 3 {
            if self.inner.q2.is_empty() { return None; }
            self.inner.q2[0]
        } else {
            if self.inner.q3.is_empty() { return None; }
            self.inner.q3[0]
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
    pub fn is_done(&self) -> bool {
        self.inner.ingested == self.inner.max_inputs
            && self.inner.q1.is_empty()
            && self.inner.q2.is_empty()
            && self.inner.q3.is_empty()
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
fn step_edges_distinct(edges: &Vec<(usize, usize)>) -> (distinct: bool)
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

fn sequential_sentinel() -> (carrier: SequentialCarrier)
    ensures carrier.inv(),
{ SequentialCarrier::new(1, 1, 0) }

fn fork_join_sentinel() -> (carrier: ForkJoinCarrier)
    ensures carrier.inv(),
{ ForkJoinCarrier::new(0, 1, 0) }

fn step_graph_sentinel() -> (carrier: StepGraphCarrier)
    ensures carrier.inv(),
{
    let edges: Vec<(usize, usize)> = Vec::new();
    StepGraphCarrier::new(0, edges)
}

fn stream_graph_sentinel() -> (carrier: StreamGraphCarrier)
    ensures carrier.inv(),
{ StreamGraphCarrier::new(3, 1, 0, 1) }

}

macro_rules! impl_error {
    ($type:ty, { $($variant:path => $message:literal),+ $(,)? }) => {
        impl core::fmt::Display for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str(match self { $($variant => $message),+ })
            }
        }
        impl std::error::Error for $type {}
    };
}

macro_rules! impl_observational_debug {
    ($type:ty, $name:literal, $($field:literal => $method:ident),+ $(,)?) => {
        impl core::fmt::Debug for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let mut state = formatter.debug_struct($name);
                $(state.field($field, &self.$method());)+
                state.finish()
            }
        }
    };
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
impl_observational_debug!(StreamGraph, "StreamGraph",
    "chain_length" => chain_length,
    "capacity" => capacity,
    "ingested" => ingested,
    "emitted" => emitted,
    "first_queue_len" => first_queue_len,
    "second_queue_len" => second_queue_len,
    "third_queue_len" => third_queue_len,
    "done" => is_done,
);

impl_error!(SequentialBuildError, {
    Self::NoSteps => "sequential execution requires at least one step",
    Self::EmptyValueDomain => "sequential value domain is empty",
    Self::InitialValueOutOfRange => "initial sequential value is outside its domain",
});
impl_error!(ForkJoinBuildError, {
    Self::EmptyValueDomain => "fork-join value domain is empty",
    Self::InitialValueOutOfRange => "initial worker value is outside its domain",
});
impl_error!(StepGraphBuildError, {
    Self::EdgeEndpointOutOfRange => "step-graph edge endpoint is outside the node universe",
    Self::DuplicateEdge => "step graph contains a duplicate edge",
});
impl_error!(StreamGraphBuildError, {
    Self::UnsupportedChainLength => "stream graph supports only three- or four-stage chains",
    Self::ZeroCapacity => "stream-graph queue capacity must be positive",
    Self::EmptyRecordDomain => "stream-graph record domain is empty",
});
