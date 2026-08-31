//! Hard selection composed with the ActuationPass lifecycle.
//!
//! Each seat owns one CompetitiveSelectionHard instance. ActuationPass owns the shared
//! allocation/effect handoff and pass closure. This composition adds only the allocation
//! agreement between those owners and the atomic methods that call their existing actions.

use crate::primitives::actuation_pass::ActuationPass;
use crate::primitives::competitive_selection::CompetitiveSelectionHard;
use vstd::prelude::*;

verus! {

/// Per-seat hard selection followed by effect application through ActuationPass.
pub struct SelectThenActuate {
    /// Candidate count retained for the zero-seat configuration.
    pub num_candidates: usize,
    /// One selection owner per seat.
    pub selections: Vec<CompetitiveSelectionHard>,
    /// Allocation, effect, and closure owner.
    pub actuation: ActuationPass,
}

impl SelectThenActuate {
    /// Whether every per-seat selection owner satisfies its local invariant.
    pub open spec fn selection_owners_well_formed(&self) -> bool {
        &&& self.num_candidates >= 1
        &&& self.selections@.len() == self.actuation.num_seats
        &&& forall|seat: int| 0 <= seat < self.selections@.len() ==> {
            let selection = #[trigger] self.selections@[seat];
            &&& selection.scores@.len() == self.num_candidates
            &&& selection.inv()
        }
    }

    /// The shared allocation is a projection of each seat's selection owner.
    pub open spec fn allocation_agreement(&self) -> bool {
        forall|seat: int| 0 <= seat < self.selections@.len() ==> {
            let selected = #[trigger] self.selections@[seat].allocation;
            let allocated = self.actuation.allocation@[seat];
            &&& (selected is None) == (allocated is None)
            &&& (selected matches Some(candidate) ==>
                allocated == Some(candidate as u64))
        }
    }

    /// Whether each retained winner is score-optimal for its seat.
    pub open spec fn winner_optimality(&self) -> bool {
        forall|seat: int| 0 <= seat < self.selections@.len() ==>
            #[trigger] self.selections@[seat].winner_optimality()
    }

    /// Whether the component state is locally well formed.
    pub open spec fn type_invariant(&self) -> bool {
        self.selection_owners_well_formed() && self.actuation.invariant()
    }

    /// Whether selection and actuation agree on every allocated seat.
    pub open spec fn composition_invariant(&self) -> bool {
        &&& self.allocation_agreement()
        &&& self.winner_optimality()
        &&& self.actuation.effect_fidelity()
        &&& self.actuation.actuation_scope()
        &&& self.actuation.pass_completeness()
    }

    /// Whether all local and cross-component obligations hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.composition_invariant()
    }

    /// Reveal the facts contained in [`Self::inv`].
    pub proof fn expose(&self)
        requires self.inv(),
        ensures
            self.selection_owners_well_formed(),
            self.allocation_agreement(),
            self.actuation.invariant(),
            self.selections@.len() == self.actuation.num_seats,
            forall|seat: int| 0 <= seat < self.selections@.len() ==> {
                let selection = #[trigger] self.selections@[seat];
                &&& selection.scores@.len() == self.num_candidates
                &&& selection.inv()
            },
    {
        reveal(SelectThenActuate::inv);
        reveal(SelectThenActuate::type_invariant);
        reveal(SelectThenActuate::composition_invariant);
        reveal(SelectThenActuate::selection_owners_well_formed);
    }

    /// Construct one empty CompetitiveSelectionHard owner per seat and one empty
    /// ActuationPass over the same seat universe.
    pub fn new(num_seats: usize, num_candidates: usize) -> (composition: Self)
        requires num_candidates >= 1,
        ensures
            composition.inv(),
            composition.num_candidates == num_candidates,
            composition.selections@.len() == num_seats,
            composition.actuation.num_seats == num_seats,
            !composition.actuation.complete,
            forall|seat: int| 0 <= seat < num_seats ==>
                composition.selections@[seat].allocation is None,
    {
        let mut selections: Vec<CompetitiveSelectionHard> = Vec::new();
        let mut allocation: Vec<Option<u64>> = Vec::new();
        let mut seat: usize = 0;
        while seat < num_seats
            invariant
                seat <= num_seats,
                num_candidates >= 1,
                selections.len() == seat,
                allocation.len() == seat,
                forall|index: int| 0 <= index < selections@.len() ==> {
                    let selection = #[trigger] selections@[index];
                    &&& selection.scores@.len() == num_candidates
                    &&& selection.allocation is None
                    &&& selection.inv()
                },
                forall|index: int| 0 <= index < allocation@.len() ==>
                    #[trigger] allocation@[index] is None,
            decreases num_seats - seat,
        {
            selections.push(CompetitiveSelectionHard::new(num_candidates));
            allocation.push(None);
            seat += 1;
        }
        let actuation = ActuationPass::new(allocation, num_seats);
        let composition = Self { num_candidates, selections, actuation };
        assert(composition.selection_owners_well_formed()) by {
            reveal(SelectThenActuate::selection_owners_well_formed);
        }
        assert(composition.allocation_agreement()) by {
            reveal(SelectThenActuate::allocation_agreement);
        }
        assert(composition.winner_optimality()) by {
            reveal(SelectThenActuate::winner_optimality);
        }
        composition
    }

    /// Read one seat-local candidate score.
    pub fn score_at(&self, seat: usize, candidate: usize) -> (score: u64)
        requires
            self.inv(),
            seat < self.selections.len(),
            candidate < self.num_candidates,
        ensures score == self.selections@[seat as int].scores@[candidate as int],
    {
        self.selections[seat].scores[candidate]
    }

    /// Read one seat's selected candidate.
    pub fn allocation_at(&self, seat: usize) -> (allocation: Option<usize>)
        requires self.inv(), seat < self.selections.len(),
        ensures allocation == self.selections@[seat as int].allocation,
    {
        self.selections[seat].allocation
    }

    /// Whether one seat has a selected candidate.
    pub fn is_allocated(&self, seat: usize) -> (allocated: bool)
        requires self.inv(), seat < self.actuation.num_seats,
        ensures allocated == (self.selections@[seat as int].allocation is Some),
    {
        proof { self.expose(); }
        let allocated = self.actuation.is_allocated(seat);
        assert(allocated == (self.selections@[seat as int].allocation is Some)) by {
            reveal(SelectThenActuate::allocation_agreement);
        }
        allocated
    }

    /// Whether one seat's selected candidate has been actuated.
    pub fn is_actuated(&self, seat: usize) -> (actuated: bool)
        requires self.inv(), seat < self.actuation.num_seats,
        ensures actuated == (self.actuation.effects@[seat as int] is Some),
    {
        self.actuation.is_actuated(seat)
    }

    /// Whether the shared actuation pass is closed.
    pub fn is_complete(&self) -> (complete: bool)
        ensures complete == self.actuation.complete,
    {
        self.actuation.complete
    }

    /// Whether selection is enabled for one seat.
    pub fn can_evaluate(&self, seat: usize) -> (enabled: bool)
        requires self.inv(),
        ensures enabled == (seat < self.selections@.len()
            && !self.actuation.complete
            && self.selections@[seat as int].allocation is None),
    {
        seat < self.selections.len()
            && !self.actuation.complete
            && !self.actuation.is_allocated(seat)
    }

    /// Whether one seat-local score can be updated.
    pub fn can_update_score(&self, seat: usize, candidate: usize) -> (enabled: bool)
        requires self.inv(),
        ensures enabled == (seat < self.selections@.len()
            && candidate < self.num_candidates
            && !self.actuation.complete
            && self.actuation.effects@[seat as int] is None),
    {
        seat < self.selections.len()
            && candidate < self.num_candidates
            && !self.actuation.complete
            && !self.actuation.is_actuated(seat)
    }

    /// Whether actuation is enabled for one seat.
    pub fn can_actuate(&self, seat: usize) -> (enabled: bool)
        requires self.inv(),
        ensures enabled == (seat < self.actuation.num_seats
            && !self.actuation.complete
            && self.actuation.allocation@[seat as int] is Some
            && self.actuation.effects@[seat as int] is None),
    {
        seat < self.actuation.num_seats
            && !self.actuation.complete
            && self.actuation.is_allocated(seat)
            && !self.actuation.is_actuated(seat)
    }

    /// Whether every seat is actuated and the pass can close.
    pub fn can_finish(&self) -> (enabled: bool)
        requires self.inv(),
        ensures enabled == (!self.actuation.complete && self.actuation.ready_to_finish()),
    {
        !self.actuation.complete && self.actuation.ready_to_finish_exec()
    }

    /// CompetitiveSelectionHard.Evaluate followed by ActuationPass.Allocate.
    pub fn evaluate(&mut self, seat: usize)
        requires
            old(self).inv(),
            seat < old(self).selections.len(),
            !old(self).actuation.complete,
            old(self).selections@[seat as int].allocation is None,
        ensures
            final(self).inv(),
            final(self).num_candidates == old(self).num_candidates,
            final(self).selections@.len() == old(self).selections@.len(),
            final(self).selections@[seat as int].allocation is Some,
            final(self).selections@[seat as int].scores@
                == old(self).selections@[seat as int].scores@,
            final(self).actuation.effects@ == old(self).actuation.effects@,
            final(self).actuation.complete == old(self).actuation.complete,
    {
        proof { self.expose(); }
        let ghost old_selections = self.selections@;
        let mut selection = CompetitiveSelectionHard::new(self.num_candidates);
        self.selections.set_and_swap(seat, &mut selection);
        assert(selection == old_selections[seat as int]);
        selection.evaluate();
        let winner = match selection.allocation {
            Some(candidate) => candidate,
            None => {
                assert(false);
                0
            },
        };
        self.actuation.allocate(seat, winner as u64);
        self.selections.set(seat, selection);
        assert(self.selection_owners_well_formed()) by {
            reveal(SelectThenActuate::selection_owners_well_formed);
            assert forall|index: int| 0 <= index < self.selections@.len() implies {
                let owner = #[trigger] self.selections@[index];
                &&& owner.scores@.len() == self.num_candidates
                &&& owner.inv()
            } by {
                if index != seat as int {
                    assert(self.selections@[index] == old_selections[index]);
                }
            }
        }
        assert(self.allocation_agreement()) by {
            reveal(SelectThenActuate::allocation_agreement);
            assert forall|index: int| 0 <= index < self.selections@.len() implies {
                let selected = #[trigger] self.selections@[index].allocation;
                let allocated = self.actuation.allocation@[index];
                &&& (selected is None) == (allocated is None)
                &&& (selected matches Some(candidate) ==>
                    allocated == Some(candidate as u64))
            } by {
                if index == seat as int {
                    assert(self.selections@[index].allocation == Some(winner));
                    assert(self.actuation.allocation@[index] == Some(winner as u64));
                } else {
                    assert(self.selections@[index] == old_selections[index]);
                    assert(self.actuation.allocation@[index]
                        == old(self).actuation.allocation@[index]);
                }
            }
        }
        assert(self.winner_optimality()) by {
            reveal(SelectThenActuate::winner_optimality);
        }
    }

    /// Revise one unapplied seat through ActuationPass.Deallocate and
    /// CompetitiveSelectionHard.UpdateScore.
    pub fn update_score(&mut self, seat: usize, candidate: usize, value: u64)
        requires
            old(self).inv(),
            seat < old(self).selections.len(),
            candidate < old(self).num_candidates,
            !old(self).actuation.complete,
            old(self).actuation.effects@[seat as int] is None,
        ensures
            final(self).inv(),
            final(self).num_candidates == old(self).num_candidates,
            final(self).selections@.len() == old(self).selections@.len(),
            final(self).selections@[seat as int].allocation is None,
            final(self).selections@[seat as int].scores@
                == old(self).selections@[seat as int].scores@.update(candidate as int, value),
            final(self).actuation.allocation@[seat as int] is None,
            final(self).actuation.effects@ == old(self).actuation.effects@,
            final(self).actuation.complete == old(self).actuation.complete,
    {
        proof { self.expose(); }
        let ghost old_selections = self.selections@;
        if self.actuation.is_allocated(seat) {
            self.actuation.deallocate(seat);
        }
        let mut selection = CompetitiveSelectionHard::new(self.num_candidates);
        self.selections.set_and_swap(seat, &mut selection);
        assert(selection == old_selections[seat as int]);
        selection.update_score(candidate, value);
        self.selections.set(seat, selection);
        assert(self.selection_owners_well_formed()) by {
            reveal(SelectThenActuate::selection_owners_well_formed);
            assert forall|index: int| 0 <= index < self.selections@.len() implies {
                let owner = #[trigger] self.selections@[index];
                &&& owner.scores@.len() == self.num_candidates
                &&& owner.inv()
            } by {
                if index != seat as int {
                    assert(self.selections@[index] == old_selections[index]);
                }
            }
        }
        assert(self.allocation_agreement()) by {
            reveal(SelectThenActuate::allocation_agreement);
            assert forall|index: int| 0 <= index < self.selections@.len() implies {
                let selected = #[trigger] self.selections@[index].allocation;
                let allocated = self.actuation.allocation@[index];
                &&& (selected is None) == (allocated is None)
                &&& (selected matches Some(owner_candidate) ==>
                    allocated == Some(owner_candidate as u64))
            } by {
                if index == seat as int {
                    assert(self.selections@[index].allocation is None);
                    assert(self.actuation.allocation@[index] is None);
                } else {
                    assert(self.selections@[index] == old_selections[index]);
                    assert(self.actuation.allocation@[index]
                        == old(self).actuation.allocation@[index]);
                }
            }
        }
        assert(self.winner_optimality()) by {
            reveal(SelectThenActuate::winner_optimality);
        }
    }

    /// Apply one selected seat through ActuationPass.Actuate.
    pub fn actuate(&mut self, seat: usize)
        requires
            old(self).inv(),
            seat < old(self).actuation.num_seats,
            !old(self).actuation.complete,
            old(self).actuation.allocation@[seat as int] is Some,
            old(self).actuation.effects@[seat as int] is None,
        ensures
            final(self).inv(),
            final(self).selections@ == old(self).selections@,
            final(self).actuation.allocation@ == old(self).actuation.allocation@,
            final(self).actuation.effects@
                == old(self).actuation.effects@.update(
                    seat as int,
                    old(self).actuation.allocation@[seat as int],
                ),
    {
        proof { self.expose(); }
        self.actuation.actuate(seat);
    }

    /// Close the ActuationPass after every allocated seat is applied.
    pub fn finish(&mut self)
        requires
            old(self).inv(),
            !old(self).actuation.complete,
            old(self).actuation.ready_to_finish(),
        ensures
            final(self).inv(),
            final(self).selections@ == old(self).selections@,
            final(self).actuation.allocation@ == old(self).actuation.allocation@,
            final(self).actuation.effects@ == old(self).actuation.effects@,
            final(self).actuation.complete,
    {
        proof { self.expose(); }
        self.actuation.finish();
    }
}

}
