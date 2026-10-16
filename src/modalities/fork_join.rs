//! Finite-index ForkJoin execution carrier.

use crate::connectives::counter::Counter;
use crate::execution_api::{ForkJoinPhase, WorkerState as ForkJoinWorkerState};
use vstd::prelude::*;

verus! {

mod fork_join_storage_seal { pub trait Sealed {} }

/// Physical worker-state binding beneath the one ForkJoin transition owner.
pub trait ForkJoinWorkers: fork_join_storage_seal::Sealed + View<V = Seq<ForkJoinWorkerState>> {
    /// Exact retained worker count.
    fn len(&self) -> (length: usize) ensures length == self@.len();
    /// Whether the retained worker set is empty.
    fn is_empty(&self) -> (empty: bool) ensures empty == (self@.len() == 0),
    { self.len() == 0 }
    /// Read the selected worker without changing its state.
    fn state_at(&self, worker: usize) -> (state: ForkJoinWorkerState)
        requires worker < self@.len(), ensures state == self@[worker as int];
    /// Replace one state; the ForkJoin action supplies the lifecycle guard.
    fn set_state(&mut self, worker: usize, state: ForkJoinWorkerState)
        requires worker < old(self)@.len(),
        ensures final(self)@ == old(self)@.update(worker as int, state);
    /// Observe the exact quantified completion predicate.
    fn all_complete(&self) -> (complete: bool)
        ensures complete == (forall|i: int| 0 <= i < self@.len()
            ==> #[trigger] self@[i] == ForkJoinWorkerState::Complete);
}

impl fork_join_storage_seal::Sealed for Vec<ForkJoinWorkerState> {}
impl ForkJoinWorkers for Vec<ForkJoinWorkerState> {
    fn len(&self) -> (length: usize) { self.len() }
    #[expect(clippy::indexing_slicing, reason = "the storage contract bounds the worker index")]
    fn state_at(&self, worker: usize) -> (state: ForkJoinWorkerState) { self[worker] }
    fn set_state(&mut self, worker: usize, state: ForkJoinWorkerState) {
        vstd::pervasive::VecAdditionalExecFns::set(self, worker, state);
    }
    #[expect(clippy::indexing_slicing, reason = "the scan cursor is bounded by the retained worker count")]
    #[expect(clippy::arithmetic_side_effects, reason = "the scan advances only below the worker count")]
    fn all_complete(&self) -> (complete: bool) {
        let mut i = 0;
        while i < self.len()
            invariant i <= self.len(),
                forall|k: int| 0 <= k < i ==> self@[k] == ForkJoinWorkerState::Complete,
            decreases self.len() - i,
        {
            if !matches!(self[i], ForkJoinWorkerState::Complete) { return false; }
            i += 1;
        }
        true
    }
}

spec fn unfinished_tag(state: ForkJoinWorkerState) -> nat {
    if state == ForkJoinWorkerState::Complete { 0 } else { 1 }
}
spec fn unfinished_prefix(states: Seq<ForkJoinWorkerState>, end: int) -> nat
    decreases end,
{
    if end <= 0 || end > states.len() { 0 }
    else { unfinished_prefix(states, end - 1) + unfinished_tag(states[end - 1]) }
}
proof fn unfinished_prefix_frame(before: Seq<ForkJoinWorkerState>, after: Seq<ForkJoinWorkerState>, end: int)
    requires 0 <= end <= before.len(), end <= after.len(),
        forall|i: int| 0 <= i < end ==> #[trigger] before[i] == after[i],
    ensures unfinished_prefix(before, end) == unfinished_prefix(after, end),
    decreases end,
{
    reveal_with_fuel(unfinished_prefix, 2);
    if end > 0 { unfinished_prefix_frame(before, after, end - 1); }
}
proof fn unfinished_prefix_bounds(states: Seq<ForkJoinWorkerState>, end: int)
    requires 0 <= end <= states.len(),
    ensures unfinished_prefix(states, end) <= end,
        (unfinished_prefix(states, end) == 0) <==> (forall|i: int| 0 <= i < end
            ==> #[trigger] states[i] == ForkJoinWorkerState::Complete),
    decreases end,
{
    reveal_with_fuel(unfinished_prefix, 2);
    if end > 0 {
        unfinished_prefix_bounds(states, end - 1);
        assert forall|i: int| 0 <= i < end && unfinished_prefix(states, end) == 0
            implies #[trigger] states[i] == ForkJoinWorkerState::Complete by {
            if i < end - 1 { assert(states[i] == ForkJoinWorkerState::Complete); }
        }
    }
}
proof fn unfinished_prefix_update(states: Seq<ForkJoinWorkerState>, worker: int,
    state: ForkJoinWorkerState, end: int)
    requires 0 <= worker < states.len(), 0 <= end <= states.len(),
    ensures unfinished_prefix(states.update(worker, state), end)
            + (if worker < end { unfinished_tag(states[worker]) } else { 0 })
        == unfinished_prefix(states, end)
            + (if worker < end { unfinished_tag(state) } else { 0 }),
    decreases end,
{
    reveal_with_fuel(unfinished_prefix, 2);
    if end > 0 { unfinished_prefix_update(states, worker, state, end - 1); }
}

/// Private checked layout: worker tags and their canonical unfinished Counter.
pub struct CountedWorkerStates { data: CountedWorkerData }
struct CountedWorkerData { states: Vec<ForkJoinWorkerState>, unfinished: Counter }
impl fork_join_storage_seal::Sealed for CountedWorkerStates {}
impl View for CountedWorkerStates {
    type V = Seq<ForkJoinWorkerState>;
    closed spec fn view(&self) -> Seq<ForkJoinWorkerState> { self.data.states@ }
}
impl CountedWorkerStates {
    /// Borrow the actual worker tags without exposing a mutable writer.
    pub(crate) fn as_slice(&self) -> (states: &[ForkJoinWorkerState])
        ensures states@ == self@,
    { self.data.states.as_slice() }
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.data.states@.len() <= u64::MAX as nat
            && self.data.unfinished.value_spec() == unfinished_prefix(self.data.states@, self.data.states@.len() as int)
    }
    pub(crate) fn new(workers: usize) -> (states: Self)
        requires workers as nat <= u64::MAX as nat,
        ensures states@.len() == workers,
            forall|i: int| 0 <= i < workers ==> #[trigger] states@[i] == ForkJoinWorkerState::Ready,
    {
        let states = initialize_worker_states(workers, Vec::new());
        Self { data: CountedWorkerData { states, unfinished: Counter::new(workers as u64) } }
    }
}
impl ForkJoinWorkers for CountedWorkerStates {
    fn len(&self) -> (length: usize) { self.data.states.len() }
    #[expect(clippy::indexing_slicing, reason = "the storage contract bounds the worker index")]
    fn state_at(&self, worker: usize) -> (state: ForkJoinWorkerState) { self.data.states[worker] }
    #[expect(clippy::indexing_slicing, reason = "the storage contract bounds the worker index")]
    fn set_state(&mut self, worker: usize, state: ForkJoinWorkerState) {
        proof { use_type_invariant(&*self); }
        // Keep a valid empty carrier in the borrowed owner while updating its data.
        // Neither the Counter nor the pinned Vec update promises no_unwind.
        let mut data = CountedWorkerData { states: Vec::new(), unfinished: Counter::new(0) };
        core::mem::swap(&mut self.data, &mut data);
        let ghost before = data.states@;
        let previous = data.states[worker];
        proof { unfinished_prefix_update(before, worker as int, state, before.len() as int); }
        if matches!(previous, ForkJoinWorkerState::Complete) && !matches!(state, ForkJoinWorkerState::Complete) {
            proof { unfinished_prefix_bounds(before.update(worker as int, state), before.len() as int); }
            let _incremented = data.unfinished.try_increment();
            assert(_incremented);
        } else if !matches!(previous, ForkJoinWorkerState::Complete) && matches!(state, ForkJoinWorkerState::Complete) {
            let _decremented = data.unfinished.try_decrement();
            assert(_decremented);
        }
        data.states.set(worker, state);
        core::mem::swap(&mut self.data, &mut data);
    }
    fn all_complete(&self) -> (complete: bool) {
        proof {
            use_type_invariant(self);
            unfinished_prefix_bounds(self.data.states@, self.data.states@.len() as int);
        }
        self.data.unfinished.value() == 0
    }
}

/// Joint snapshot projection and physical binding for the one ForkJoin owner.
pub trait ForkJoinSnapshot: fork_join_storage_seal::Sealed {
    /// Abstract snapshot, including its defined pre-publication contents.
    spec fn contents(&self, worker_values: Seq<u64>, ready: bool) -> Seq<u64>;
    /// Before publication, changing values at fixed length frames the snapshot.
    proof fn unpublished_frame(&self, before: Seq<u64>, after: Seq<u64>)
        requires before.len() == after.len(),
        ensures self.contents(before, false) == self.contents(after, false);
    /// Bind completed values; ForkJoin owns readiness and phase publication.
    fn capture(&mut self, worker_values: &[u64])
        requires old(self).contents(worker_values@, false).len() == worker_values@.len(),
        ensures final(self).contents(worker_values@, true) == worker_values@;
    /// Borrow the published snapshot without copying or transferring custody.
    fn values<'a>(&'a self, worker_values: &'a [u64]) -> (values: &'a [u64])
        ensures values@ == self.contents(worker_values@, true);
}
impl fork_join_storage_seal::Sealed for Vec<u64> {}
impl ForkJoinSnapshot for Vec<u64> {
    open spec fn contents(&self, _worker_values: Seq<u64>, _ready: bool) -> Seq<u64> { self@ }
    proof fn unpublished_frame(&self, _before: Seq<u64>, _after: Seq<u64>) {}
    #[expect(clippy::indexing_slicing, reason = "the copy cursor bounds both equally sized arrays")]
    #[expect(clippy::arithmetic_side_effects, reason = "the copy cursor advances only below the value length")]
    fn capture(&mut self, worker_values: &[u64]) {
        let mut i = 0;
        while i < worker_values.len()
            invariant i <= worker_values.len(), self@.len() == worker_values@.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] self@[j] == worker_values@[j],
            decreases worker_values.len() - i,
        {
            self.set(i, worker_values[i]);
            i += 1;
        }
        assert(self@ =~= worker_values@);
    }
    fn values<'a>(&'a self, _worker_values: &'a [u64]) -> (values: &'a [u64]) { self.as_slice() }
}

/// Checked snapshot layout: initial uniform values, then frozen joined values.
/// Readiness is supplied by ForkJoin; no duplicate publication state is retained.
pub struct JoinedValuesSnapshot { initial: u64 }
impl fork_join_storage_seal::Sealed for JoinedValuesSnapshot {}
impl ForkJoinSnapshot for JoinedValuesSnapshot {
    closed spec fn contents(&self, worker_values: Seq<u64>, ready: bool) -> Seq<u64> {
        if ready { worker_values } else { Seq::new(worker_values.len(), |_i: int| self.initial) }
    }
    proof fn unpublished_frame(&self, before: Seq<u64>, after: Seq<u64>) {
        assert(self.contents(before, false) =~= self.contents(after, false));
    }
    fn capture(&mut self, _worker_values: &[u64]) {}
    fn values<'a>(&'a self, worker_values: &'a [u64]) -> (values: &'a [u64]) { worker_values }
}

#[expect(clippy::arithmetic_side_effects, reason = "the construction cursor advances only below the worker bound")]
fn initialize_worker_states(workers: usize, mut states: Vec<ForkJoinWorkerState>) -> (initialized: Vec<ForkJoinWorkerState>)
    requires states@.len() == 0,
    ensures initialized@.len() == workers,
        forall|i: int| 0 <= i < workers ==> #[trigger] initialized@[i] == ForkJoinWorkerState::Ready,
        unfinished_prefix(initialized@, workers as int) == workers,
{
    let mut i = 0;
    while i < workers
        invariant i <= workers, states@.len() == i,
            unfinished_prefix(states@, i as int) == i,
            forall|j: int| 0 <= j < i ==> #[trigger] states@[j] == ForkJoinWorkerState::Ready,
        decreases workers - i,
    {
        let ghost before = states@;
        states.push(ForkJoinWorkerState::Ready);
        proof {
            unfinished_prefix_frame(before, states@, i as int);
            reveal_with_fuel(unfinished_prefix, 2);
        }
        i += 1;
    }
    states
}
#[expect(clippy::arithmetic_side_effects, reason = "the construction cursor advances only below the worker bound")]
fn initialize_worker_values(workers: usize, initial: u64, mut values: Vec<u64>) -> (initialized: Vec<u64>)
    requires values@.len() == 0,
    ensures initialized@.len() == workers,
        forall|i: int| 0 <= i < workers ==> #[trigger] initialized@[i] == initial,
{
    let mut i = 0;
    while i < workers
        invariant i <= workers, values@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] values@[j] == initial,
        decreases workers - i,
    {
        values.push(initial);
        i += 1;
    }
    values
}

/// Observe one worker without inventing a value for an invalid ordinal.
pub open spec fn worker_at(
    workers: Seq<ForkJoinWorkerState>,
    worker: int,
) -> Option<ForkJoinWorkerState> {
    if 0 <= worker < workers.len() {
        Some(workers[worker])
    } else {
        None
    }
}

/// Transition for starting one observed ForkJoin worker.
pub open spec fn start_worker_transition(
    before: Option<ForkJoinWorkerState>,
    after: Option<ForkJoinWorkerState>,
    phase: ForkJoinPhase,
    selected: bool,
    accepted: bool,
) -> bool {
    let enabled = selected
        && phase == ForkJoinPhase::Fork
        && before == Some(ForkJoinWorkerState::Ready);
    &&& accepted == enabled
    &&& after == if accepted {
        Some(ForkJoinWorkerState::Running)
    } else {
        before
    }
}

/// Transition for completing one observed ForkJoin worker.
pub open spec fn complete_worker_transition(
    before: Option<ForkJoinWorkerState>,
    after: Option<ForkJoinWorkerState>,
    phase: ForkJoinPhase,
    selected: bool,
    value_admitted: bool,
    accepted: bool,
) -> bool {
    let enabled = selected
        && value_admitted
        && phase == ForkJoinPhase::Fork
        && before == Some(ForkJoinWorkerState::Running);
    &&& accepted == enabled
    &&& after == if accepted {
        Some(ForkJoinWorkerState::Complete)
    } else {
        before
    }
}

/// Worker-start action over any faithful ForkJoin state carrier.
pub open spec fn start_worker_action(
    before: Seq<ForkJoinWorkerState>,
    after: Seq<ForkJoinWorkerState>,
    phase: ForkJoinPhase,
    worker: int,
    selected: bool,
    accepted: bool,
) -> bool {
    &&& start_worker_transition(
        worker_at(before, worker),
        worker_at(after, worker),
        phase,
        selected,
        accepted,
    )
    &&& after == if accepted {
        before.update(worker, ForkJoinWorkerState::Running)
    } else {
        before
    }
}

/// Worker-completion action over any faithful ForkJoin state carrier.
pub open spec fn complete_worker_action(
    before: Seq<ForkJoinWorkerState>,
    after: Seq<ForkJoinWorkerState>,
    phase: ForkJoinPhase,
    worker: int,
    selected: bool,
    value_admitted: bool,
    accepted: bool,
) -> bool {
    &&& complete_worker_transition(
        worker_at(before, worker),
        worker_at(after, worker),
        phase,
        selected,
        value_admitted,
        accepted,
    )
    &&& after == if accepted {
        before.update(worker, ForkJoinWorkerState::Complete)
    } else {
        before
    }
}

/// Barrier phase transition.
pub open spec fn barrier_action(
    before: ForkJoinPhase,
    after: ForkJoinPhase,
    selected: bool,
    completion_observed: bool,
    accepted: bool,
) -> bool {
    let enabled = selected && before == ForkJoinPhase::Fork && completion_observed;
    &&& accepted == enabled
    &&& after == if accepted { ForkJoinPhase::Join } else { before }
}

/// Output-publication phase transition.
pub open spec fn produce_output_action(
    before: ForkJoinPhase,
    after: ForkJoinPhase,
    selected: bool,
    accepted: bool,
) -> bool {
    let enabled = selected && before == ForkJoinPhase::Join;
    &&& accepted == enabled
    &&& after == if accepted { ForkJoinPhase::Done } else { before }
}

/// Fork-join execution owner.
pub struct ForkJoin<W: ForkJoinWorkers = Vec<ForkJoinWorkerState>, S: ForkJoinSnapshot = Vec<u64>> {
    /// Exclusive upper bound of worker values.
    pub value_domain_size: u64,
    /// Worker lifecycle states by worker index.
    pub wstate: W,
    /// Current values by worker index.
    pub wvalue: Vec<u64>,
    /// Global fork-join phase.
    pub phase: ForkJoinPhase,
    /// Whether a stable output snapshot has been produced.
    pub output_ready: bool,
    /// Stable joined output values.
    pub output_snapshot: S,
}

impl<W: ForkJoinWorkers, S: ForkJoinSnapshot> ForkJoin<W, S> {
    /// Abstract snapshot under the selected physical representation.
    pub open spec fn snapshot_spec(&self) -> Seq<u64> {
        self.output_snapshot.contents(self.wvalue@, self.output_ready)
    }

    /// Whether every worker has completed.
    pub open spec fn all_complete(&self) -> bool {
        forall|i: int| 0 <= i < self.wstate@.len()
            ==> #[trigger] self.wstate@[i] == ForkJoinWorkerState::Complete
    }

    /// Whether worker, phase, and output storage has valid shape and values.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.value_domain_size > 0
        &&& self.wstate@.len() == self.wvalue@.len()
        &&& self.snapshot_spec().len() == self.wvalue@.len()
        &&& (forall|i: int| 0 <= i < self.wvalue@.len()
                ==> #[trigger] self.wvalue@[i] < self.value_domain_size)
        &&& (forall|i: int| 0 <= i < self.snapshot_spec().len()
                ==> #[trigger] self.snapshot_spec()[i] < self.value_domain_size)
    }

    /// Whether entering the join phase requires every worker to be complete.
    pub open spec fn barrier_completeness(&self) -> bool {
        self.output_ready ==> self.all_complete()
    }

    /// Whether a published output exactly reflects completed worker values.
    pub open spec fn output_consistency(&self) -> bool {
        self.output_ready ==> self.snapshot_spec() == self.wvalue@
    }

    /// Whether phase progress follows fork, join, and completion order.
    pub open spec fn phase_ordering(&self) -> bool {
        &&& (self.phase == ForkJoinPhase::Join ==> self.all_complete())
        &&& (self.phase == ForkJoinPhase::Done ==> self.output_ready)
    }

    /// Whether output readiness occurs only in the terminal phase.
    pub open spec fn ready_only_done(&self) -> bool {
        self.output_ready ==> self.phase == ForkJoinPhase::Done
    }

    /// Whether all fork-join contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.barrier_completeness()
        &&& self.output_consistency()
        &&& self.phase_ordering()
        &&& self.ready_only_done()
    }
}

impl ForkJoin {

    /// Construct a fork-phase execution with ready workers.
    pub fn new(workers: usize, value_domain_size: u64, initial_value: u64) -> (s: ForkJoin)
        requires
            value_domain_size > 0,
            initial_value < value_domain_size,
        ensures
            s.value_domain_size == value_domain_size,
            s.wstate@.len() == workers,
            s.wvalue@.len() == workers,
            s.output_snapshot@.len() == workers,
            forall|i: int| 0 <= i < workers ==>
                s.wstate@[i] == ForkJoinWorkerState::Ready,
            forall|i: int| 0 <= i < workers ==> s.wvalue@[i] == initial_value,
            forall|i: int| 0 <= i < workers ==> s.output_snapshot@[i] == initial_value,
            s.phase == ForkJoinPhase::Fork,
            !s.output_ready,
            s.inv(),
    {
        Self::initialize(workers, value_domain_size, initial_value, Vec::new(), Vec::new(), Vec::new())
    }

    /// Reserve all worker and output storage before exposing the fork.
    ///
    /// # Errors
    /// Returns the allocation error before any worker can start.
    pub fn try_new(workers: usize, value_domain_size: u64, initial_value: u64)
        -> (result: Result<Self, std::collections::TryReserveError>)
        requires value_domain_size > 0, initial_value < value_domain_size,
        ensures result is Ok ==> {
            let s = result.unwrap();
            &&& s.inv() && s.value_domain_size == value_domain_size
            &&& s.wstate@.len() == workers && s.wvalue@.len() == workers
            &&& s.output_snapshot@.len() == workers
            &&& s.phase == ForkJoinPhase::Fork && !s.output_ready
            &&& forall|i: int| 0 <= i < workers ==> #[trigger] s.wstate@[i] == ForkJoinWorkerState::Ready
            &&& forall|i: int| 0 <= i < workers ==> #[trigger] s.wvalue@[i] == initial_value
            &&& forall|i: int| 0 <= i < workers ==> #[trigger] s.output_snapshot@[i] == initial_value
        },
    {
        let mut states = Vec::new(); let mut values = Vec::new(); let mut snapshot = Vec::new();
        states.try_reserve(workers)?; values.try_reserve(workers)?; snapshot.try_reserve(workers)?;
        Ok(Self::initialize(workers, value_domain_size, initial_value, states, values, snapshot))
    }

    fn initialize(workers: usize, value_domain_size: u64, initial_value: u64, wstate: Vec<ForkJoinWorkerState>, wvalue: Vec<u64>, snapshot: Vec<u64>) -> (s: ForkJoin)
        requires
            wstate@.len() == 0, wvalue@.len() == 0, snapshot@.len() == 0,
            value_domain_size > 0,
            initial_value < value_domain_size,
        ensures
            s.value_domain_size == value_domain_size,
            s.wstate@.len() == workers,
            s.wvalue@.len() == workers,
            s.output_snapshot@.len() == workers,
            forall|i: int| 0 <= i < workers ==>
                s.wstate@[i] == ForkJoinWorkerState::Ready,
            forall|i: int| 0 <= i < workers ==> s.wvalue@[i] == initial_value,
            forall|i: int| 0 <= i < workers ==> s.output_snapshot@[i] == initial_value,
            s.phase == ForkJoinPhase::Fork,
            !s.output_ready,
            s.inv(),
    {
        let wstate = initialize_worker_states(workers, wstate);
        let wvalue = initialize_worker_values(workers, initial_value, wvalue);
        let snapshot = initialize_worker_values(workers, initial_value, snapshot);
        ForkJoin {
            value_domain_size,
            wstate,
            wvalue,
            phase: ForkJoinPhase::Fork,
            output_ready: false,
            output_snapshot: snapshot,
        }
    }

    /// Construct the private counted/borrowed representation of the same machine.
    pub(crate) fn new_indexed(workers: usize, value_domain_size: u64, initial_value: u64)
        -> (s: ForkJoin<CountedWorkerStates, JoinedValuesSnapshot>)
        requires value_domain_size > 0, initial_value < value_domain_size,
            workers as nat <= u64::MAX as nat,
        ensures s.inv(), s.value_domain_size == value_domain_size,
            s.wstate@.len() == workers, s.wvalue@.len() == workers,
            s.snapshot_spec().len() == workers,
            s.phase == ForkJoinPhase::Fork, !s.output_ready,
            forall|i: int| 0 <= i < workers ==> #[trigger] s.wstate@[i] == ForkJoinWorkerState::Ready,
            forall|i: int| 0 <= i < workers ==> #[trigger] s.wvalue@[i] == initial_value,
            forall|i: int| 0 <= i < workers ==> #[trigger] s.snapshot_spec()[i] == initial_value,
    {
        ForkJoin {
            value_domain_size,
            wstate: CountedWorkerStates::new(workers),
            wvalue: initialize_worker_values(workers, initial_value, Vec::new()),
            phase: ForkJoinPhase::Fork,
            output_ready: false,
            output_snapshot: JoinedValuesSnapshot { initial: initial_value },
        }
    }
}

impl<W: ForkJoinWorkers, S: ForkJoinSnapshot> ForkJoin<W, S> {
    /// Borrow the published snapshot through its actual physical binding.
    pub fn output_values(&self) -> (values: &[u64])
        requires self.output_ready,
        ensures values@ == self.snapshot_spec(),
    { self.output_snapshot.values(self.wvalue.as_slice()) }

    /// Observe the exact worker-completion predicate used by the barrier action.
    pub fn all_complete_exec(&self) -> (b: bool)
        ensures b == self.all_complete(),
    {
        self.wstate.all_complete()
    }

    /// Start one ready worker, returning false when the transition is disabled.
    pub fn start_worker(&mut self, worker: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).snapshot_spec() == old(self).snapshot_spec(),
            start_worker_action(
                old(self).wstate@,
                final(self).wstate@,
                old(self).phase,
                worker as int,
                true,
                accepted,
            ),
            final(self).inv(),
    {
        if worker < self.wstate.len()
            && matches!(self.phase, ForkJoinPhase::Fork)
            && matches!(self.wstate.state_at(worker), ForkJoinWorkerState::Ready)
        {
            assert(!self.output_ready);
            self.wstate.set_state(worker, ForkJoinWorkerState::Running);
            assert(!self.all_complete()) by {
                assert(self.wstate@[worker as int] == ForkJoinWorkerState::Running);
            }
            true
        } else {
            false
        }
    }

    /// Complete one running worker with an in-domain value.
    pub fn complete_worker(&mut self, worker: usize, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).snapshot_spec() == old(self).snapshot_spec(),
            complete_worker_action(
                old(self).wstate@,
                final(self).wstate@,
                old(self).phase,
                worker as int,
                true,
                value < old(self).value_domain_size,
                accepted,
            ),
            final(self).wvalue@ == if accepted {
                old(self).wvalue@.update(worker as int, value)
            } else { old(self).wvalue@ },
            final(self).inv(),
    {
        if worker < self.wstate.len()
            && matches!(self.phase, ForkJoinPhase::Fork)
            && matches!(self.wstate.state_at(worker), ForkJoinWorkerState::Running)
            && value < self.value_domain_size
        {
            assert(!self.output_ready);
            self.wvalue.set(worker, value);
            self.wstate.set_state(worker, ForkJoinWorkerState::Complete);
            proof {
                self.output_snapshot.unpublished_frame(old(self).wvalue@, self.wvalue@);
            }
            assert forall|i: int| 0 <= i < self.wvalue@.len()
                implies #[trigger] self.wvalue@[i] < self.value_domain_size by {
                if i != worker as int {
                    assert(self.wvalue@[i] == old(self).wvalue@[i]);
                }
            }
            true
        } else {
            false
        }
    }

    /// Commit the join barrier after every worker completes.
    pub fn barrier(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wstate@ == old(self).wstate@,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).output_ready == old(self).output_ready,
            final(self).snapshot_spec() == old(self).snapshot_spec(),
            barrier_action(
                old(self).phase,
                final(self).phase,
                true,
                old(self).all_complete(),
                accepted,
            ),
            final(self).inv(),
    {
        if matches!(self.phase, ForkJoinPhase::Fork) && self.all_complete_exec() {
            assert(!self.output_ready);
            self.phase = ForkJoinPhase::Join;
            true
        } else {
            false
        }
    }

    /// Produce the stable output snapshot from joined worker values.
    pub fn produce_output(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wstate@ == old(self).wstate@,
            final(self).wvalue@ == old(self).wvalue@,
            if accepted {
                final(self).phase == ForkJoinPhase::Done
                    && final(self).output_ready
                    && final(self).snapshot_spec() == old(self).wvalue@
            } else {
                final(self).phase == old(self).phase
                    && final(self).output_ready == old(self).output_ready
                    && final(self).snapshot_spec() == old(self).snapshot_spec()
            },
            produce_output_action(
                old(self).phase,
                final(self).phase,
                true,
                accepted,
            ),
            final(self).inv(),
    {
        if matches!(self.phase, ForkJoinPhase::Join) {
            self.output_snapshot.capture(self.wvalue.as_slice());
            self.output_ready = true;
            self.phase = ForkJoinPhase::Done;
            true
        } else {
            false
        }
    }

    /// Execute the terminal stutter when output production is complete.
    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (old(self).phase == ForkJoinPhase::Done),
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wstate@ == old(self).wstate@,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).snapshot_spec() == old(self).snapshot_spec(),
            final(self).inv(),
    {
        matches!(self.phase, ForkJoinPhase::Done)
    }
}

}
