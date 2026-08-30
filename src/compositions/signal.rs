// Executable Signal composition corresponding to the TLA+ carrier.
//
// The TLA+ spec at formal/structures/Signal/Signal.tla models a change-detecting
// notification channel as current_value, a change_observed provenance bit, and the
// pending/notified listener sets. Init has epoch zero and empty delivery state;
// the two actions are:
//
//   SetValue(v)       — guard v /= current_value (the change-detection
//                       filter); on fire:
//                       current_value' = v, pending' = Listeners (all),
//                       notified' = {}, change_observed' = true
//                       in ONE step.
//   NotifyListener(l) — guard l ∈ pending_notifications; moves l from
//                       pending to notified in ONE step.
//
// Its .cfg checks three invariants, all discharged here as proof
// obligations under the full dynamics (Init ⇒ Inv, Inv ∧ Action ⇒ Inv'):
//
//   TypeInvariant           == current_value ∈ Values
//                              /\ pending ⊆ Listeners /\ notified ⊆ Listeners
//   PendingNotifiedDisjointness == pending_notifications ∩ notified = {}
//   NotificationProvenance == before any change there is no delivery state;
//                              afterwards pending ∪ notified = Listeners.
//
// Representation:
//   - Values is the index universe 0..num_values-1; current_value < num_values
//     is TypeInvariant's first conjunct.
//   - pending/notified ⊆ Listeners are listener-indexed bitvecs Vec<bool>
//     over 0..num_listeners-1.
//   - SetValue is realised in the Budget TryAllocate idiom (the action is
//     IF-shaped on its guard): set_value(v) returns exactly the TLA+ guard
//     condition v /= current_value; when false the state is UNCHANGED. The
//     change-detection filter is fused with the act inside the one method, so
//     the channel fires exactly once per actual change and the filter is not
//     delegated to callers.
//   - NotifyListener's guard (l ∈ pending) is a `requires`, so the action is
//     callable exactly when the TLA+ action is enabled; the pending-to-notified
//     move is one method.
//
// Evidence boundary: this is a sequential witness. Each merged TLA+ action is
// one &mut self method and Rust's exclusive mutable borrow is the atomic
// boundary. A concurrent realization must supply equivalent exclusion.

use vstd::prelude::*;

verus! {

/// A change-detecting notification channel over a value universe
/// `0..num_values` and a listener universe `0..num_listeners`.
pub struct Signal {
    /// |Values|: the value universe is the index range `0..num_values`.
    pub num_values: u64,
    /// current_value ∈ Values.
    pub current_value: u64,
    /// TLA+ change_observed. It becomes true only on a guarded actual change.
    pub change_observed: bool,
    /// |Listeners|: the listener universe is the index range `0..num_listeners`.
    pub num_listeners: usize,
    /// pending_notifications ⊆ Listeners as a listener-indexed bitvec.
    pub pending: Vec<bool>,
    /// notified ⊆ Listeners as a listener-indexed bitvec.
    pub notified: Vec<bool>,
}

impl Signal {
    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ TypeInvariant: current_value ∈ Values, and both listener sets
    /// span the listener universe (the per-listener membership is carried by
    /// the bitvec representation).
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.current_value < self.num_values
        &&& self.pending.len() == self.num_listeners
        &&& self.notified.len() == self.num_listeners
    }

    /// TLA+ `PendingNotifiedDisjointness`:
    /// no listener is simultaneously pending and notified.
    pub open spec fn pending_notified_disjointness(&self) -> bool {
        forall|i: int|
            0 <= i < self.pending.len()
                ==> !(#[trigger] self.pending@[i] && self.notified@[i])
    }

    /// TLA+ `NotificationProvenance`: no delivery state exists before the
    /// first actual change; for a positive epoch every listener is pending or
    /// notified for the latest change.
    pub open spec fn notification_provenance(&self) -> bool {
        &&& !self.change_observed ==> forall|i: int|
            0 <= i < self.pending.len()
                ==> !#[trigger] self.pending@[i] && !self.notified@[i]
        &&& self.change_observed ==> forall|i: int|
            0 <= i < self.pending.len()
                ==> #[trigger] self.pending@[i] || self.notified@[i]
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the initial state: some value from the universe, nothing
    /// pending, nothing notified. Realises the TLA+ `Init` predicate and
    /// establishes both invariants (disjointness holds vacuously
    /// since both sets are empty).
    pub fn new(initial_value: u64, num_values: u64, num_listeners: usize) -> (s: Signal)
        requires
            initial_value < num_values,
        ensures
            s.num_values == num_values,
            s.num_listeners == num_listeners,
            s.current_value == initial_value,
            !s.change_observed,
            s.pending.len() == num_listeners,
            s.notified.len() == num_listeners,
            forall|i: int| 0 <= i < num_listeners ==> !s.pending@[i],
            forall|i: int| 0 <= i < num_listeners ==> !s.notified@[i],
            s.type_invariant(),
            s.pending_notified_disjointness(),
            s.notification_provenance(),
    {
        let mut pending: Vec<bool> = Vec::new();
        let mut notified: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i < num_listeners
            invariant
                i <= num_listeners,
                pending.len() == i,
                notified.len() == i,
                forall|k: int| 0 <= k < i ==> !pending@[k],
                forall|k: int| 0 <= k < i ==> !notified@[k],
            decreases num_listeners - i,
        {
            pending.push(false);
            notified.push(false);
            i = i + 1;
        }
        Signal {
            num_values,
            current_value: initial_value,
            change_observed: false,
            num_listeners,
            pending,
            notified,
        }
    }

    // ── Membership (executable) ─────────────────────────────────────────

    /// Executable test of the `l ∈ pending_notifications` guard.
    pub fn is_pending(&self, l: usize) -> (b: bool)
        requires
            l < self.pending.len(),
        ensures
            b == self.pending@[l as int],
    {
        self.pending[l]
    }

    /// Executable test of `l ∈ notified`.
    pub fn is_notified(&self, l: usize) -> (b: bool)
        requires
            l < self.notified.len(),
        ensures
            b == self.notified@[l as int],
    {
        self.notified[l]
    }

    // ── SetValue (TLA+ SetValue) ────────────────────────────────────────

    /// Set the value, with the change-detection filter fused in: the returned
    /// bool is exactly the TLA+ guard `v /= current_value`. On a change,
    /// in the same step: current_value' = v, pending' = Listeners (every
    /// listener), notified' = {} (reset). On a non-change the state is
    /// UNCHANGED, so no notification is raised without a value change.
    pub fn set_value(&mut self, v: u64) -> (changed: bool)
        requires
            old(self).type_invariant(),
            old(self).pending_notified_disjointness(),
            old(self).notification_provenance(),
            v < old(self).num_values,
        ensures
            final(self).num_values == old(self).num_values,
            final(self).num_listeners == old(self).num_listeners,
            changed == (v != old(self).current_value),
            changed ==> final(self).current_value == v,
            changed ==> final(self).change_observed,
            changed ==> forall|i: int| 0 <= i < final(self).pending.len() ==> final(self).pending@[i],
            changed ==> forall|i: int| 0 <= i < final(self).notified.len() ==> !final(self).notified@[i],
            !changed ==> final(self).current_value == old(self).current_value,
            !changed ==> final(self).change_observed == old(self).change_observed,
            !changed ==> final(self).pending@ == old(self).pending@,
            !changed ==> final(self).notified@ == old(self).notified@,
            final(self).type_invariant(),
            final(self).pending_notified_disjointness(),
            final(self).notification_provenance(),
    {
        if v == self.current_value {
            // Guard false: the TLA+ action is not enabled; UNCHANGED.
            return false;
        }
        // Guard true: fire. pending' = Listeners, notified' = {} — walked in
        // one pass; the whole method is the one atomic step (exclusive borrow).
        let mut i: usize = 0;
        while i < self.pending.len()
            invariant
                self.num_values == old(self).num_values,
                self.num_listeners == old(self).num_listeners,
                self.current_value == old(self).current_value,
                self.pending.len() == old(self).pending.len(),
                self.notified.len() == old(self).notified.len(),
                old(self).type_invariant(),
                i <= self.pending.len(),
                forall|k: int| 0 <= k < i ==> self.pending@[k],
                forall|k: int| 0 <= k < i ==> !self.notified@[k],
            decreases self.pending.len() - i,
        {
            // notified.len() == pending.len() by TypeInvariant, so the index
            // is in range for both.
            assert(i < self.notified.len());
            self.pending.set(i, true);
            self.notified.set(i, false);
            i = i + 1;
        }
        self.current_value = v;
        self.change_observed = true;
        // Re-establish disjointness: notified is now all-false, so
        // the intersection is empty regardless of pending.
        assert(self.pending_notified_disjointness()) by {
            assert forall|j: int| 0 <= j < self.pending.len()
                implies !(self.pending@[j] && self.notified@[j]) by {
                assert(!self.notified@[j]);
            }
        }
        assert(self.notification_provenance()) by {
            assert forall|j: int| 0 <= j < self.pending.len()
                implies self.pending@[j] || self.notified@[j] by {
                assert(self.pending@[j]);
            }
        }
        true
    }

    // ── NotifyListener (TLA+ NotifyListener) ────────────────────────────

    /// Notify listener `l`. Realises the TLA+ `NotifyListener(l)` action: the
    /// guard (l ∈ pending_notifications) is a `requires`, and the move from
    /// pending to notified happens in this one step — a listener is never
    /// observable in both views; the decomposition witness splits this move
    /// and exposes the overlap.
    pub fn notify_listener(&mut self, l: usize)
        requires
            old(self).type_invariant(),
            old(self).pending_notified_disjointness(),
            old(self).notification_provenance(),
            l < old(self).pending.len(),
            old(self).pending@[l as int],   // l ∈ pending_notifications
        ensures
            final(self).num_values == old(self).num_values,
            final(self).num_listeners == old(self).num_listeners,
            final(self).current_value == old(self).current_value,   // UNCHANGED
            final(self).change_observed == old(self).change_observed,
            final(self).pending@ == old(self).pending@.update(l as int, false),
            final(self).notified@ == old(self).notified@.update(l as int, true),
            final(self).type_invariant(),
            final(self).pending_notified_disjointness(),
            final(self).notification_provenance(),
    {
        assert(self.change_observed) by {
            if !self.change_observed {
                assert(!self.pending@[l as int]);
            }
        }
        // notified.len() == pending.len() by TypeInvariant.
        assert(l < self.notified.len());
        self.pending.set(l, false);
        self.notified.set(l, true);
        // Re-establish disjointness: at l the pending side is now
        // false; every other listener is unchanged, so the old invariant
        // carries over pointwise.
        assert(self.pending_notified_disjointness()) by {
            assert forall|i: int| 0 <= i < self.pending.len()
                implies !(self.pending@[i] && self.notified@[i]) by {
                if i == l as int {
                    assert(!self.pending@[i]);
                } else {
                    assert(self.pending@[i] == old(self).pending@[i]);
                    assert(self.notified@[i] == old(self).notified@[i]);
                }
            }
        }
        assert(self.notification_provenance()) by {
            assert forall|i: int| 0 <= i < self.pending.len()
                implies self.pending@[i] || self.notified@[i] by {
                if i == l as int {
                    assert(self.notified@[i]);
                } else {
                    assert(self.pending@[i] == old(self).pending@[i]);
                    assert(self.notified@[i] == old(self).notified@[i]);
                }
            }
        }
    }
}

}
