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
// contract clauses: EffectFidelity, ActuationScope, and PassCompleteness.
//
// The executable `can_*` methods expose admission/rejection without weakening
// the transition contracts. Rust's exclusive mutable borrow is the sequential
// commit boundary; concurrent realization remains a separate runtime rely.

use crate::connectives::counter::Counter;
use vstd::prelude::*;

verus! {

mod actuation_storage_seal { pub trait Sealed {} }

/// Physical allocation binding beneath the one allocation/effect transition owner.
pub trait ActuationAllocations: actuation_storage_seal::Sealed + View<V = Seq<Option<u64>>> {
    /// The actual retained vector, available only to erased owner projections.
    spec fn vec_spec(&self) -> Vec<Option<u64>>;
    /// The representation's joint relation to the actual effect record.
    spec fn coupled(&self, effects: Seq<Option<u64>>) -> bool;
    /// Exact retained allocation count.
    fn len(&self) -> (length: usize) ensures length == self@.len();
    /// Whether the allocation universe is empty.
    fn is_empty(&self) -> (empty: bool) ensures empty == (self@.len() == 0),
    { self.len() == 0 }
    /// Read one admitted allocation slot.
    fn value_at(&self, seat: usize) -> (value: Option<u64>)
        requires seat < self@.len(), ensures value == self@[seat as int];
    /// Borrow the original allocation storage.
    fn as_slice(&self) -> (values: &[Option<u64>]) ensures values@ == self@;
    /// Change allocation and its pending contribution in one exclusive owner commit.
    fn set_allocation(&mut self, effects: &Vec<Option<u64>>, seat: usize, value: Option<u64>)
        requires old(self).coupled(effects@), effects@.len() == old(self)@.len(),
            seat < old(self)@.len(),
        ensures final(self)@ == old(self)@.update(seat as int, value),
            final(self).vec_spec()@ == final(self)@, final(self).coupled(effects@);
    /// Change an effect and its pending contribution without changing allocation.
    fn set_effect(&mut self, effects: &mut Vec<Option<u64>>, seat: usize, value: Option<u64>)
        requires old(self).coupled(old(effects)@), old(effects)@.len() == old(self)@.len(),
            seat < old(self)@.len(),
        ensures final(self)@ == old(self)@, final(self).vec_spec()@ == final(self)@,
            final(effects)@ == old(effects)@.update(seat as int, value),
            final(self).coupled(final(effects)@);
    /// Observe the same complete-allocation predicate for this physical binding.
    fn ready(&self, effects: &Vec<Option<u64>>) -> (ready: bool)
        requires self.coupled(effects@), effects@.len() == self@.len(),
        ensures ready == (forall|i: int| 0 <= i < self@.len()
            ==> (#[trigger] self@[i] is Some ==> effects@[i] is Some));
}

impl actuation_storage_seal::Sealed for Vec<Option<u64>> {}
impl ActuationAllocations for Vec<Option<u64>> {
    open spec fn vec_spec(&self) -> Vec<Option<u64>> { *self }
    open spec fn coupled(&self, _effects: Seq<Option<u64>>) -> bool { true }
    fn len(&self) -> (length: usize) { self.len() }
    #[expect(clippy::indexing_slicing, reason = "the binding contract bounds the allocation slot")]
    fn value_at(&self, seat: usize) -> (value: Option<u64>) { self[seat] }
    fn as_slice(&self) -> (values: &[Option<u64>]) { self.as_slice() }
    fn set_allocation(&mut self, _effects: &Vec<Option<u64>>, seat: usize, value: Option<u64>) {
        vstd::pervasive::VecAdditionalExecFns::set(self, seat, value);
    }
    fn set_effect(&mut self, effects: &mut Vec<Option<u64>>, seat: usize, value: Option<u64>) {
        effects.set(seat, value);
    }
    #[expect(clippy::indexing_slicing, reason = "the closure cursor is bounded by both paired record lengths")]
    #[expect(clippy::arithmetic_side_effects, reason = "the closure cursor advances below the paired record length")]
    fn ready(&self, effects: &Vec<Option<u64>>) -> (ready: bool) {
        let mut i = 0;
        while i < self.len()
            invariant i <= self.len(), effects@.len() == self@.len(),
                forall|k: int| 0 <= k < i ==> (self@[k] is Some ==> effects@[k] is Some),
            decreases self.len() - i,
        {
            if matches!(self.value_at(i), Some(_)) && matches!(effects[i], None) {
                assert(self@[i as int] is Some && effects@[i as int] is None);
                return false;
            }
            i += 1;
        }
        true
    }
}

spec fn pending_tag(allocation: Option<u64>, effect: Option<u64>) -> nat {
    if allocation is Some && effect is None { 1 } else { 0 }
}
spec fn pending_prefix(allocation: Seq<Option<u64>>, effects: Seq<Option<u64>>, end: int) -> nat
    decreases end,
{
    if end <= 0 || end > allocation.len() || end > effects.len() { 0 }
    else { pending_prefix(allocation, effects, end - 1)
        + pending_tag(allocation[end - 1], effects[end - 1]) }
}
proof fn pending_prefix_bounds(allocation: Seq<Option<u64>>, effects: Seq<Option<u64>>, end: int)
    requires 0 <= end <= allocation.len(), end <= effects.len(),
    ensures pending_prefix(allocation, effects, end) <= end,
        (pending_prefix(allocation, effects, end) == 0) <==>
            (forall|i: int| 0 <= i < end
                ==> (#[trigger] allocation[i] is Some ==> effects[i] is Some)),
    decreases end,
{
    reveal_with_fuel(pending_prefix, 2);
    if end > 0 {
        pending_prefix_bounds(allocation, effects, end - 1);
        assert forall|i: int| 0 <= i < end && pending_prefix(allocation, effects, end) == 0
            implies (!(#[trigger] allocation[i] is Some) || effects[i] is Some) by {
            if i < end - 1 { assert(allocation[i] is Some ==> effects[i] is Some); }
        }
    }
}
proof fn pending_prefix_update(allocation: Seq<Option<u64>>, effects: Seq<Option<u64>>,
    seat: int, value: Option<u64>, effect: Option<u64>, end: int)
    requires allocation.len() == effects.len(), 0 <= seat < allocation.len(),
        0 <= end <= allocation.len(),
    ensures pending_prefix(allocation.update(seat, value), effects.update(seat, effect), end)
        + if seat < end { pending_tag(allocation[seat], effects[seat]) } else { 0 }
        == pending_prefix(allocation, effects, end)
            + if seat < end { pending_tag(value, effect) } else { 0 },
    decreases end,
{
    reveal_with_fuel(pending_prefix, 2);
    if end > 0 {
        pending_prefix_update(allocation, effects, seat, value, effect, end - 1);
        if seat == end - 1 {
        } else {
            assert(allocation.update(seat, value)[end - 1] == allocation[end - 1]);
            assert(effects.update(seat, effect)[end - 1] == effects[end - 1]);
        }
    }
}

/// Sealed counted allocation storage; the enclosing ActuationPass owns its joint effect relation.
pub struct CountedAllocations {
    values: Vec<Option<u64>>,
    pending: Counter,
}
impl View for CountedAllocations {
    type V = Seq<Option<u64>>;
    closed spec fn view(&self) -> Seq<Option<u64>> { self.values@ }
}
impl CountedAllocations {
    #[expect(clippy::ptr_arg, reason = "the joint Verus representation contract binds the retained Vec effect view")]
    #[expect(clippy::indexing_slicing, reason = "the setup cursor is bounded by both paired record lengths")]
    #[expect(clippy::arithmetic_side_effects, reason = "setup advances only below the allocation length")]
    fn new(values: Vec<Option<u64>>, effects: &Vec<Option<u64>>) -> (storage: Self)
        requires values@.len() == effects@.len(), values@.len() <= u64::MAX,
        ensures storage@ == values@, storage.vec_spec()@ == storage@, storage.coupled(effects@),
    {
        let mut pending = Counter::new(0);
        let mut i = 0;
        while i < values.len()
            invariant i <= values.len(), values@.len() == effects@.len(), values@.len() <= u64::MAX,
                pending.value_spec() == pending_prefix(values@, effects@, i as int),
            decreases values.len() - i,
        {
            proof {
                pending_prefix_bounds(values@, effects@, i as int);
                reveal_with_fuel(pending_prefix, 2);
            }
            if matches!(values[i], Some(_)) && matches!(effects[i], None) {
                let _changed = pending.try_increment();
                assert(_changed);
            }
            i += 1;
        }
        Self { values, pending }
    }
    #[expect(clippy::ptr_arg, reason = "the joint Verus update contract binds the retained Vec effect view")]
    #[expect(clippy::indexing_slicing, reason = "the joint update contract bounds both paired slot reads")]
    fn change_pending(&mut self, effects: &Vec<Option<u64>>, seat: usize,
        value: Option<u64>, effect: Option<u64>)
        requires old(self).coupled(effects@), effects@.len() == old(self)@.len(),
            seat < old(self)@.len(),
        ensures final(self)@ == old(self)@,
            final(self).pending.value_spec() == pending_prefix(
                old(self)@.update(seat as int, value), effects@.update(seat as int, effect),
                old(self)@.len() as int),
    {
        let was_pending = matches!(self.values[seat], Some(_)) && matches!(effects[seat], None);
        let becomes_pending = matches!(value, Some(_)) && matches!(effect, None);
        proof {
            pending_prefix_update(self.values@, effects@, seat as int, value, effect,
                self.values@.len() as int);
            pending_prefix_bounds(self.values@.update(seat as int, value),
                effects@.update(seat as int, effect), self.values@.len() as int);
        }
        if was_pending && !becomes_pending {
            let _changed = self.pending.try_decrement();
            assert(_changed);
        } else if !was_pending && becomes_pending {
            let _changed = self.pending.try_increment();
            assert(_changed);
        }
    }
}
impl actuation_storage_seal::Sealed for CountedAllocations {}
impl ActuationAllocations for CountedAllocations {
    closed spec fn vec_spec(&self) -> Vec<Option<u64>> { self.values }
    closed spec fn coupled(&self, effects: Seq<Option<u64>>) -> bool {
        &&& self.values@.len() == effects.len()
        &&& self.values@.len() <= u64::MAX
        &&& self.pending.value_spec() == pending_prefix(self.values@, effects, self.values@.len() as int)
    }
    fn len(&self) -> (length: usize) { self.values.len() }
    #[expect(clippy::indexing_slicing, reason = "the binding contract bounds the allocation slot")]
    fn value_at(&self, seat: usize) -> (value: Option<u64>) { self.values[seat] }
    fn as_slice(&self) -> (values: &[Option<u64>]) { self.values.as_slice() }
    #[expect(clippy::indexing_slicing, reason = "the joint update contract bounds the unchanged effect read")]
    fn set_allocation(&mut self, effects: &Vec<Option<u64>>, seat: usize, value: Option<u64>) {
        let effect = effects[seat];
        self.change_pending(effects, seat, value, effect);
        assert(effects@.update(seat as int, effect) =~= effects@);
        self.values.set(seat, value);
    }
    #[expect(clippy::indexing_slicing, reason = "the joint update contract bounds the unchanged allocation read")]
    fn set_effect(&mut self, effects: &mut Vec<Option<u64>>, seat: usize, value: Option<u64>) {
        let allocation = self.values[seat];
        let ghost before = self.values@;
        self.change_pending(effects, seat, allocation, value);
        assert(before.update(seat as int, allocation) =~= before);
        effects.set(seat, value);
    }
    fn ready(&self, _effects: &Vec<Option<u64>>) -> (ready: bool) {
        proof { pending_prefix_bounds(self.values@, _effects@, self.values@.len() as int); }
        self.pending.value() == 0
    }
}

/// Allocation-to-effect lifecycle owner.
pub struct ActuationPass<A: ActuationAllocations = Vec<Option<u64>>> {
    /// |Seats|: the seat universe is the index range `0..num_seats`.
    pub num_seats: usize,
    /// Live allocation record. `Some(r)` is resource r; `None` is TLA+ NULL.
    pub allocation: A,
    /// Resource-valued effect record. `Some(r)` means this carrier recorded the
    /// operation for resource r; `None` means the seat has not been actuated.
    /// External side-effect execution and observation remain caller-owned.
    pub effects: Vec<Option<u64>>,
    /// The pass has committed its closure transition.
    pub complete: bool,
}

impl<A: ActuationAllocations> ActuationPass<A> {
    /// Erased projection to the unchanged public raw Vec carrier.
    pub open spec fn as_raw(&self) -> ActuationPass {
        ActuationPass {
            num_seats: self.num_seats, allocation: self.allocation.vec_spec(),
            effects: self.effects, complete: self.complete,
        }
    }

    // -- State predicates -------------------------------------------------

    /// Whether allocation and effect storage have the configured seat count.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.allocation@.len() == self.num_seats
        &&& self.effects.len() == self.num_seats
        &&& self.allocation.vec_spec()@ == self.allocation@
        &&& self.allocation.coupled(self.effects@)
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
            0 <= i < self.allocation@.len()
                ==> (self.allocation@[i] is Some ==> self.effects@[i] is Some)
    }

    /// PassCompleteness: a completed pass has recorded every currently allocated seat.
    pub open spec fn pass_completeness(&self) -> bool {
        self.complete ==> self.ready_to_finish()
    }

    /// Whether all recorded allocation-to-effect lifecycle contract clauses hold.
    pub open spec fn invariant(&self) -> bool {
        &&& self.type_invariant()
        &&& self.effect_fidelity()
        &&& self.actuation_scope()
        &&& self.pass_completeness()
    }

}

impl ActuationPass {
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
        Self::initialize(allocation, num_seats, Vec::new())
    }

    /// Reserve effect storage before constructing the existing actuation owner.
    /// The raw proof API retains the allocation-length precondition.
    ///
    /// # Errors
    /// Returns the allocation error and unconsumed assignments on reservation failure.
    pub fn try_new(allocation: Vec<Option<u64>>, num_seats: usize)
        -> (result: Result<Self, (std::collections::TryReserveError, Vec<Option<u64>>)>)
        requires allocation@.len() == num_seats,
        ensures
            result is Err ==> (result->Err_0).1@ == allocation@,
            result is Ok ==> {
                let s = result.unwrap();
                &&& s.num_seats == num_seats
                &&& s.allocation@ == allocation@
                &&& s.effects@.len() == num_seats
                &&& forall|i: int| 0 <= i < num_seats ==> #[trigger] s.effects@[i] is None
                &&& !s.complete
                &&& s.invariant()
            },
    {
        let mut effects = Vec::<Option<u64>>::new();
        if let Err(error) = effects.try_reserve(num_seats) { return Err((error, allocation)); }
        Ok(Self::initialize(allocation, num_seats, effects))
    }

    #[expect(clippy::arithmetic_side_effects, reason = "the initialization cursor advances only while strictly below num_seats")]
    fn initialize(allocation: Vec<Option<u64>>, num_seats: usize, mut effects: Vec<Option<u64>>) -> (s: ActuationPass)
        requires
            effects@.len() == 0,
            allocation.len() == num_seats,
        ensures
            s.num_seats == num_seats,
            s.allocation@ == allocation@,
            s.effects.len() == num_seats,
            forall|i: int| 0 <= i < num_seats ==> s.effects@[i] is None,
            !s.complete,
            s.invariant(),
    {
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

    /// Construct the same Init with counted pending storage for the checked facade.
    pub(crate) fn new_counted(allocation: Vec<Option<u64>>, num_seats: usize)
        -> (s: ActuationPass<CountedAllocations>)
        requires allocation@.len() == num_seats,
        ensures s.num_seats == num_seats, s.allocation@ == allocation@,
            s.effects@.len() == num_seats,
            forall|i: int| 0 <= i < num_seats ==> s.effects@[i] is None,
            !s.complete, s.invariant(), s.as_raw().invariant(),
    {
        let raw = Self::new(allocation, num_seats);
        assert(raw.allocation@.len() <= u64::MAX);
        let allocation = CountedAllocations::new(raw.allocation, &raw.effects);
        let s = ActuationPass { num_seats, allocation, effects: raw.effects, complete: false };
        assert(s.as_raw().invariant());
        s
    }
}

impl<A: ActuationAllocations> ActuationPass<A> {
    // -- Executable admission predicates --------------------------------

    /// Whether an in-range seat holds an allocation.
    pub fn is_allocated(&self, s: usize) -> (b: bool)
        requires
            s < self.allocation@.len(),
        ensures
            b == (self.allocation@[s as int] is Some),
    {
        match self.allocation.value_at(s) {
            Some(_) => true,
            None => false,
        }
    }

    /// Whether an in-range seat has committed its effect.
    #[expect(clippy::indexing_slicing, reason = "the accessor requires the seat to be below the effect length")]
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

    /// Whether allocation is enabled for a seat.
    pub fn can_allocate(&self, s: usize) -> (b: bool)
        requires
            self.type_invariant(),
            s < self.num_seats,
        ensures
            b == (!self.complete && self.allocation@[s as int] is None),
    {
        !self.complete && !self.is_allocated(s)
    }

    /// Whether deallocation is enabled for a seat.
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

    /// Whether effect commitment is enabled for a seat.
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

    /// Whether every allocation has a committed effect and closure is enabled.
    pub fn ready_to_finish_exec(&self) -> (b: bool)
        requires
            self.type_invariant(),
        ensures
            b == self.ready_to_finish(),
    {
        self.allocation.ready(&self.effects)
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
        self.allocation.set_allocation(&self.effects, s, Some(resource));
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
        self.allocation.set_allocation(&self.effects, s, None);
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
        let resource = match self.allocation.value_at(s) {
            Some(r) => r,
            None => {
                assert(false);
                0
            },
        };
        self.allocation.set_effect(&mut self.effects, s, Some(resource));
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
