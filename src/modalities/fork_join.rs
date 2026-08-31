//! Finite-index ForkJoin execution carrier.

use crate::execution_api::{ForkJoinPhase, WorkerState as ForkJoinWorkerState};
use vstd::prelude::*;

verus! {

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
pub struct ForkJoin {
    /// Exclusive upper bound of worker values.
    pub value_domain_size: u64,
    /// Worker lifecycle states by worker index.
    pub wstate: Vec<ForkJoinWorkerState>,
    /// Current values by worker index.
    pub wvalue: Vec<u64>,
    /// Global fork-join phase.
    pub phase: ForkJoinPhase,
    /// Whether a stable output snapshot has been produced.
    pub output_ready: bool,
    /// Stable joined output values.
    pub output_snapshot: Vec<u64>,
}

impl ForkJoin {
    /// Whether every worker has completed.
    pub open spec fn all_complete(&self) -> bool {
        forall|i: int| 0 <= i < self.wstate@.len()
            ==> #[trigger] self.wstate@[i] == ForkJoinWorkerState::Complete
    }

    /// Whether worker, phase, and output storage has valid shape and values.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.value_domain_size > 0
        &&& self.wstate@.len() == self.wvalue@.len()
        &&& self.output_snapshot@.len() == self.wvalue@.len()
        &&& (forall|i: int| 0 <= i < self.wvalue@.len()
                ==> #[trigger] self.wvalue@[i] < self.value_domain_size)
        &&& (forall|i: int| 0 <= i < self.output_snapshot@.len()
                ==> #[trigger] self.output_snapshot@[i] < self.value_domain_size)
    }

    /// Whether entering the join phase requires every worker to be complete.
    pub open spec fn barrier_completeness(&self) -> bool {
        self.output_ready ==> self.all_complete()
    }

    /// Whether a published output exactly reflects completed worker values.
    pub open spec fn output_consistency(&self) -> bool {
        self.output_ready ==> self.output_snapshot@ == self.wvalue@
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

    /// Whether all fork-join obligations hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.barrier_completeness()
        &&& self.output_consistency()
        &&& self.phase_ordering()
        &&& self.ready_only_done()
    }

    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the construction cursor remains within the worker bound")]
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
        let mut wstate = Vec::new();
        let mut wvalue = Vec::new();
        let mut snapshot = Vec::new();
        let mut i = 0;
        while i < workers
            invariant
                i <= workers,
                wstate@.len() == i,
                wvalue@.len() == i,
                snapshot@.len() == i,
                forall|k: int| 0 <= k < i ==>
                    wstate@[k] == ForkJoinWorkerState::Ready,
                forall|k: int| 0 <= k < i ==> wvalue@[k] == initial_value,
                forall|k: int| 0 <= k < i ==> snapshot@[k] == initial_value,
            decreases workers - i,
        {
            wstate.push(ForkJoinWorkerState::Ready);
            wvalue.push(initial_value);
            snapshot.push(initial_value);
            i += 1;
        }
        ForkJoin {
            value_domain_size,
            wstate,
            wvalue,
            phase: ForkJoinPhase::Fork,
            output_ready: false,
            output_snapshot: snapshot,
        }
    }

    #[expect(clippy::indexing_slicing, reason = "Verus proves the completeness cursor remains in bounds")]
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the completeness cursor increment remains in bounds")]
    fn all_complete_exec(&self) -> (b: bool)
        ensures b == self.all_complete(),
    {
        let mut i = 0;
        while i < self.wstate.len()
            invariant
                i <= self.wstate.len(),
                forall|k: int| 0 <= k < i ==>
                    self.wstate@[k] == ForkJoinWorkerState::Complete,
            decreases self.wstate.len() - i,
        {
            if !matches!(self.wstate[i], ForkJoinWorkerState::Complete) {
                assert(!self.all_complete()) by {
                    assert(self.wstate@[i as int] != ForkJoinWorkerState::Complete);
                }
                return false;
            }
            i += 1;
        }
        true
    }

    #[expect(clippy::indexing_slicing, reason = "the action guard and Verus invariant bound the worker index")]
    /// Start one ready worker, returning false when the transition is disabled.
    pub fn start_worker(&mut self, worker: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).wvalue@ == old(self).wvalue@,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).output_snapshot@ == old(self).output_snapshot@,
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
            && matches!(self.wstate[worker], ForkJoinWorkerState::Ready)
        {
            assert(!self.output_ready);
            self.wstate.set(worker, ForkJoinWorkerState::Running);
            assert(!self.all_complete()) by {
                assert(self.wstate@[worker as int] == ForkJoinWorkerState::Running);
            }
            true
        } else {
            false
        }
    }

    #[expect(clippy::indexing_slicing, reason = "the action guard and Verus invariant bound the worker index")]
    /// Complete one running worker with an in-domain value.
    pub fn complete_worker(&mut self, worker: usize, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).phase == old(self).phase,
            final(self).output_ready == old(self).output_ready,
            final(self).output_snapshot@ == old(self).output_snapshot@,
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
            && matches!(self.wstate[worker], ForkJoinWorkerState::Running)
            && value < self.value_domain_size
        {
            assert(!self.output_ready);
            self.wvalue.set(worker, value);
            self.wstate.set(worker, ForkJoinWorkerState::Complete);
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
            final(self).output_snapshot@ == old(self).output_snapshot@,
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
                    && final(self).output_snapshot@ == old(self).wvalue@
            } else {
                final(self).phase == old(self).phase
                    && final(self).output_ready == old(self).output_ready
                    && final(self).output_snapshot@ == old(self).output_snapshot@
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
            self.output_snapshot = self.wvalue.clone();
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
            final(self).output_snapshot@ == old(self).output_snapshot@,
            final(self).inv(),
    {
        matches!(self.phase, ForkJoinPhase::Done)
    }
}

}
