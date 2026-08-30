// Executable counterpart of the `ActuationPass` TLA+ specification.
//
// The governed state and actions correspond directly:
//
//   allocation : Seats -> Resources \cup {NULL}  -> Vec<Option<u64>>
//   effects    : Seats -> Resources \cup {NULL}  -> Vec<Option<u64>>
//   complete   : BOOLEAN                         -> bool
//
// `allocate`, `deallocate`, `actuate`, and `finish` implement the four
// non-stuttering TLA+ actions. Their `requires` clauses are the action guards;
// their postconditions name the exact commit and re-establish the specified
// obligations: EffectFidelity, ActuationScope, and PassCompleteness.
//
// The executable `can_*` methods expose admission/rejection without weakening
// the transition contracts. Rust's exclusive mutable borrow is the sequential
// commit boundary; concurrent realization remains a separate runtime rely.

use vstd::prelude::*;

verus! {

pub struct ActuationPass {
    /// |Seats|: the seat universe is the index range `0..num_seats`.
    pub num_seats: usize,
    /// Live allocation record. `Some(r)` is resource r; `None` is TLA+ NULL.
    pub allocation: Vec<Option<u64>>,
    /// Resource-valued effect record. `Some(r)` means the operation was
    /// applied to resource r; `None` means the seat has not been actuated.
    pub effects: Vec<Option<u64>>,
    /// The pass has committed its closure transition.
    pub complete: bool,
}

impl ActuationPass {
    // -- State predicates -------------------------------------------------

    pub open spec fn type_invariant(&self) -> bool {
        &&& self.allocation.len() == self.num_seats
        &&& self.effects.len() == self.num_seats
    }

    /// EffectFidelity: every effect names exactly the resource held by the seat's
    /// live allocation at the governed actuation commit.
    pub open spec fn effect_fidelity(&self) -> bool {
        forall|i: int|
            #![trigger self.effects@[i]]
            0 <= i < self.effects.len()
                ==> (self.effects@[i] is Some ==> self.effects@[i] == self.allocation@[i])
    }

    /// ActuationScope: `effects[i] is Some` is the executable projection of TLA+
    /// `i \in Actuated`; this is intentionally not duplicated as held state.
    pub open spec fn actuation_scope(&self) -> bool {
        forall|i: int|
            #![trigger self.effects@[i]]
            0 <= i < self.effects.len()
                ==> (self.effects@[i] is Some ==> self.allocation@[i] is Some)
    }

    /// The closure guard shared by TLA+ `Finish` and PassCompleteness.
    pub open spec fn ready_to_finish(&self) -> bool {
        forall|i: int|
            #![trigger self.allocation@[i]]
            0 <= i < self.allocation.len()
                ==> (self.allocation@[i] is Some ==> self.effects@[i] is Some)
    }

    /// PassCompleteness: a completed pass has applied every currently allocated seat.
    pub open spec fn pass_completeness(&self) -> bool {
        self.complete ==> self.ready_to_finish()
    }

    pub open spec fn invariant(&self) -> bool {
        &&& self.type_invariant()
        &&& self.effect_fidelity()
        &&& self.actuation_scope()
        &&& self.pass_completeness()
    }

    // -- Init -------------------------------------------------------------

    /// TLA+ Init: allocation is environment-supplied, every effect is NULL,
    /// and the pass has not reported closure.
    pub fn new(allocation: Vec<Option<u64>>, num_seats: usize) -> (s: ActuationPass)
        requires
            allocation.len() == num_seats,
        ensures
            s.num_seats == num_seats,
            s.allocation@ == allocation@,
            s.effects.len() == num_seats,
            forall|i: int| 0 <= i < num_seats ==> s.effects@[i] is None,
            !s.complete,
            s.invariant(),
    {
        let mut effects: Vec<Option<u64>> = Vec::new();
        let mut i: usize = 0;
        while i < num_seats
            invariant
                i <= num_seats,
                effects.len() == i,
                forall|k: int| 0 <= k < i ==> effects@[k] is None,
            decreases num_seats - i,
        {
            effects.push(None);
            i = i + 1;
        }
        ActuationPass { num_seats, allocation, effects, complete: false }
    }

    // -- Executable admission predicates --------------------------------

    pub fn is_allocated(&self, s: usize) -> (b: bool)
        requires
            s < self.allocation.len(),
        ensures
            b == (self.allocation@[s as int] is Some),
    {
        match self.allocation[s] {
            Some(_) => true,
            None => false,
        }
    }

    pub fn is_actuated(&self, s: usize) -> (b: bool)
        requires
            s < self.effects.len(),
        ensures
            b == (self.effects@[s as int] is Some),
    {
        match self.effects[s] {
            Some(_) => true,
            None => false,
        }
    }

    pub fn can_allocate(&self, s: usize) -> (b: bool)
        requires
            self.type_invariant(),
            s < self.num_seats,
        ensures
            b == (!self.complete && self.allocation@[s as int] is None),
    {
        !self.complete && !self.is_allocated(s)
    }

    pub fn can_deallocate(&self, s: usize) -> (b: bool)
        requires
            self.type_invariant(),
            s < self.num_seats,
        ensures
            b == (!self.complete
                && self.allocation@[s as int] is Some
                && self.effects@[s as int] is None),
    {
        !self.complete && self.is_allocated(s) && !self.is_actuated(s)
    }

    pub fn can_actuate(&self, s: usize) -> (b: bool)
        requires
            self.type_invariant(),
            s < self.num_seats,
        ensures
            b == (!self.complete
                && self.effects@[s as int] is None
                && self.allocation@[s as int] is Some),
    {
        !self.complete && !self.is_actuated(s) && self.is_allocated(s)
    }

    pub fn ready_to_finish_exec(&self) -> (b: bool)
        requires
            self.type_invariant(),
        ensures
            b == self.ready_to_finish(),
    {
        let len = self.allocation.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.allocation.len(),
                self.effects.len() == self.allocation.len(),
                forall|k: int| 0 <= k < i
                    ==> (self.allocation@[k] is Some ==> self.effects@[k] is Some),
            decreases len - i,
        {
            if self.is_allocated(i) && !self.is_actuated(i) {
                assert(self.allocation@[i as int] is Some);
                assert(self.effects@[i as int] is None);
                return false;
            }
            i = i + 1;
        }
        true
    }

    // -- Environment actions --------------------------------------------

    /// TLA+ `Allocate(s, r)`.
    pub fn allocate(&mut self, s: usize, resource: u64)
        requires
            old(self).invariant(),
            s < old(self).num_seats,
            !old(self).complete,
            old(self).allocation@[s as int] is None,
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).allocation@ == old(self).allocation@.update(s as int, Some(resource)),
            final(self).effects@ == old(self).effects@,
            final(self).complete == old(self).complete,
            final(self).invariant(),
    {
        assert(old(self).effects@[s as int] is None) by {
            if old(self).effects@[s as int] is Some {
                assert(old(self).effects@[s as int] == old(self).allocation@[s as int]);
            }
        }
        self.allocation.set(s, Some(resource));
        assert(self.effect_fidelity()) by {
            assert forall|i: int| 0 <= i < self.effects.len() && self.effects@[i] is Some
                implies self.effects@[i] == self.allocation@[i] by {
                if i == s as int {
                    assert(self.effects@[i] is None);
                } else {
                    assert(self.effects@[i] == old(self).effects@[i]);
                    assert(self.allocation@[i] == old(self).allocation@[i]);
                }
            }
        }
    }

    /// TLA+ `Deallocate(s)`. An already-applied seat is owned by the pass and
    /// cannot be withdrawn before closure.
    pub fn deallocate(&mut self, s: usize)
        requires
            old(self).invariant(),
            s < old(self).num_seats,
            !old(self).complete,
            old(self).allocation@[s as int] is Some,
            old(self).effects@[s as int] is None,
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).allocation@ == old(self).allocation@.update(s as int, None),
            final(self).effects@ == old(self).effects@,
            final(self).complete == old(self).complete,
            final(self).invariant(),
    {
        self.allocation.set(s, None);
        assert(self.effect_fidelity()) by {
            assert forall|i: int| 0 <= i < self.effects.len() && self.effects@[i] is Some
                implies self.effects@[i] == self.allocation@[i] by {
                if i == s as int {
                    assert(self.effects@[i] is None);
                } else {
                    assert(self.effects@[i] == old(self).effects@[i]);
                    assert(self.allocation@[i] == old(self).allocation@[i]);
                }
            }
        }
    }

    // -- Pass and closure actions ---------------------------------------

    /// TLA+ `Actuate(s)`: read the live allocation and record the applied
    /// resource in the same mutable commit.
    pub fn actuate(&mut self, s: usize)
        requires
            old(self).invariant(),
            s < old(self).num_seats,
            !old(self).complete,
            old(self).effects@[s as int] is None,
            old(self).allocation@[s as int] is Some,
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).allocation@ == old(self).allocation@,
            final(self).effects@ == old(self).effects@.update(s as int, old(self).allocation@[s as int]),
            final(self).complete == old(self).complete,
            final(self).effects@[s as int] == old(self).allocation@[s as int],
            final(self).invariant(),
    {
        let resource = match self.allocation[s] {
            Some(r) => r,
            None => {
                assert(false);
                0
            },
        };
        self.effects.set(s, Some(resource));
        assert(self.effect_fidelity()) by {
            assert forall|i: int| 0 <= i < self.effects.len() && self.effects@[i] is Some
                implies self.effects@[i] == self.allocation@[i] by {
                if i == s as int {
                    assert(self.effects@[i] == old(self).allocation@[i]);
                    assert(self.allocation@[i] == old(self).allocation@[i]);
                } else {
                    assert(self.effects@[i] == old(self).effects@[i]);
                    assert(self.allocation@[i] == old(self).allocation@[i]);
                }
            }
        }
    }

    /// TLA+ `Finish`: fuse the completeness check with the closure flag.
    pub fn finish(&mut self)
        requires
            old(self).invariant(),
            !old(self).complete,
            old(self).ready_to_finish(),
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).allocation@ == old(self).allocation@,
            final(self).effects@ == old(self).effects@,
            crate::connectives::marker::set_if(
                old(self).complete,
                final(self).complete,
                true,
            ),
            final(self).invariant(),
    {
        self.complete = true;
    }
}

}
