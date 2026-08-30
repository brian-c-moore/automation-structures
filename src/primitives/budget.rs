// Executable carrier for Budget.tla.
//
// Budget bounds a consumed resource by a structural ceiling. The TLA+ spec at
// formal/structures/Budget/Budget.tla models the full reservation/eviction lifecycle with
// four Nat-valued state variables — capacity, allocated, reserved,
// pending_eviction — and six actions, and its .cfg checks two invariants:
//
//   TypeInvariant   == capacity, allocated, reserved, pending_eviction ∈ Nat
//   SafetyInvariant == allocated + reserved + pending_eviction <= capacity
//
// This module discharges the full SafetyInvariant (all three claimants summed,
// not the reserved=pending=0 restriction) across all six actions, faithful to
// the TLA+ action structure:
//
//   TryAllocate / Reserve         — IF (used + amount <= capacity) THEN grow
//                                   ELSE UNCHANGED. Modelled as bool-returning
//                                   try-operations; the returned bool is exactly
//                                   the TLA+ IF condition.
//   CommitReservation / Release /
//   MarkEviction / CompleteEviction — guarded conjunctions with an enabling
//                                   condition (amount <= reserved / allocated /
//                                   pending_eviction); modelled with that guard
//                                   as a `requires`, so the action is callable
//                                   exactly when the TLA+ action is enabled.
//
// TypeInvariant is realised at the type level: the four Nat-valued variables are
// u64 fields, so "∈ Nat" holds by construction. SafetyInvariant is the maintained
// proof obligation; the
// spec arithmetic is lifted to `int` so the bound is stated without overflow
// noise, and every executable sum is shown overflow-free from the invariant.

use vstd::prelude::*;

verus! {

/// Reusable logical form of the Budget safety obligation.
///
/// Compositions use this predicate directly when a compact representation fuses the four Budget
/// fields. The executable Budget carrier below is one realization of the same owner predicate.
pub open spec fn budget_safety(
    capacity: nat,
    allocated: nat,
    reserved: nat,
    pending_eviction: nat,
) -> bool {
    allocated + reserved + pending_eviction <= capacity
}

/// A budget: a `capacity` ceiling against three claimants — `allocated`
/// (committed), `reserved` (held but not committed), and `pending_eviction`
/// (being reclaimed).
pub struct Budget {
    pub capacity: u64,
    pub allocated: u64,
    pub reserved: u64,
    pub pending_eviction: u64,
}

impl Budget {
    // ── Specifications ──────────────────────────────────────────────────

    /// Total claimed against the budget: allocated + reserved + pending_eviction.
    /// Lifted to `int` so the sum is exact regardless of u64 range.
    pub open spec fn used(&self) -> int {
        self.allocated as int + self.reserved as int + self.pending_eviction as int
    }

    /// TLA+ `SafetyInvariant`.
    pub open spec fn safety_invariant(&self) -> bool {
        budget_safety(
            self.capacity as nat,
            self.allocated as nat,
            self.reserved as nat,
            self.pending_eviction as nat,
        )
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct an empty budget with the given capacity. Realises `Init`.
    pub fn new(capacity: u64) -> (b: Budget)
        ensures
            b.capacity == capacity,
            b.allocated == 0,
            b.reserved == 0,
            b.pending_eviction == 0,
            b.safety_invariant(),
    {
        Budget { capacity, allocated: 0, reserved: 0, pending_eviction: 0 }
    }

    /// Headroom = capacity - used, computed overflow-safely (used <= capacity by
    /// the invariant, so the subtraction never underflows). Exposed for callers
    /// and the try-operations.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves used is bounded by capacity")]
    pub fn available(&self) -> (a: u64)
        requires self.safety_invariant(),
        ensures a as int == self.capacity as int - self.used(),
    {
        // allocated + reserved <= used <= capacity, so each partial sum fits u64.
        assert(self.allocated + self.reserved <= self.capacity);
        let used: u64 = self.allocated + self.reserved + self.pending_eviction;
        self.capacity - used
    }

    // ── TryAllocate (TLA+ TryAllocate) ──────────────────────────────────

    /// Try to commit `amount`: succeeds iff it fits under the ceiling. The
    /// returned bool is exactly the TLA+ IF condition
    /// `allocated + reserved + pending_eviction + amount <= capacity`.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the guarded addition is within capacity")]
    pub fn try_allocate(&mut self, amount: u64) -> (ok: bool)
        requires old(self).safety_invariant(),
        ensures
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).pending_eviction == old(self).pending_eviction,
            final(self).safety_invariant(),
            ok == (old(self).used() + amount as int <= old(self).capacity as int),
            ok ==> final(self).allocated == old(self).allocated + amount,
            !ok ==> final(self).allocated == old(self).allocated,
    {
        let headroom = self.available();
        if amount <= headroom {
            self.allocated = self.allocated + amount;
            true
        } else {
            false
        }
    }

    // ── Reserve (TLA+ Reserve) ──────────────────────────────────────────

    /// Try to reserve `amount` (held, not yet committed). Same ceiling test as
    /// TryAllocate; on success grows `reserved`.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the guarded addition is within capacity")]
    pub fn reserve(&mut self, amount: u64) -> (ok: bool)
        requires old(self).safety_invariant(),
        ensures
            final(self).capacity == old(self).capacity,
            final(self).allocated == old(self).allocated,
            final(self).pending_eviction == old(self).pending_eviction,
            final(self).safety_invariant(),
            ok == (old(self).used() + amount as int <= old(self).capacity as int),
            ok ==> final(self).reserved == old(self).reserved + amount,
            !ok ==> final(self).reserved == old(self).reserved,
    {
        let headroom = self.available();
        if amount <= headroom {
            self.reserved = self.reserved + amount;
            true
        } else {
            false
        }
    }

    // ── CommitReservation (TLA+ CommitReservation) ──────────────────────

    /// Commit `amount` of the reservation: moves it from `reserved` to
    /// `allocated`. Enabling condition: amount <= reserved. The total `used` is
    /// unchanged, so SafetyInvariant is trivially preserved.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the transfer operands are bounded")]
    pub fn commit_reservation(&mut self, amount: u64)
        requires
            old(self).safety_invariant(),
            amount <= old(self).reserved,
        ensures
            final(self).capacity == old(self).capacity,
            final(self).pending_eviction == old(self).pending_eviction,
            final(self).allocated == old(self).allocated + amount,
            final(self).reserved == old(self).reserved - amount,
            final(self).safety_invariant(),
    {
        // allocated + amount <= allocated + reserved <= used <= capacity.
        assert(self.allocated + amount <= self.capacity);
        self.allocated = self.allocated + amount;
        self.reserved = self.reserved - amount;
    }

    // ── Release (TLA+ Release) ──────────────────────────────────────────

    /// Release `amount` of committed allocation. Enabling condition:
    /// amount <= allocated. Decreases `used`, so SafetyInvariant is preserved.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves amount does not exceed allocated")]
    pub fn release(&mut self, amount: u64)
        requires
            old(self).safety_invariant(),
            amount <= old(self).allocated,
        ensures
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).pending_eviction == old(self).pending_eviction,
            final(self).allocated == old(self).allocated - amount,
            final(self).safety_invariant(),
    {
        self.allocated = self.allocated - amount;
    }

    // ── MarkEviction (TLA+ MarkEviction) ────────────────────────────────

    /// Mark `amount` of committed allocation for eviction: moves it from
    /// `allocated` to `pending_eviction`. Enabling condition: amount <=
    /// allocated. `used` is unchanged, so SafetyInvariant is preserved.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the allocation transfer is bounded")]
    pub fn mark_eviction(&mut self, amount: u64)
        requires
            old(self).safety_invariant(),
            amount <= old(self).allocated,
        ensures
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).allocated == old(self).allocated - amount,
            final(self).pending_eviction == old(self).pending_eviction + amount,
            final(self).safety_invariant(),
    {
        // pending_eviction + amount <= pending_eviction + allocated <= used <= capacity.
        assert(self.pending_eviction + amount <= self.capacity);
        self.allocated = self.allocated - amount;
        self.pending_eviction = self.pending_eviction + amount;
    }

    // ── CompleteEviction (TLA+ CompleteEviction) ────────────────────────

    /// Complete eviction of `amount`: removes it from `pending_eviction`.
    /// Enabling condition: amount <= pending_eviction. Decreases `used`, so
    /// SafetyInvariant is preserved.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves amount does not exceed pending eviction")]
    pub fn complete_eviction(&mut self, amount: u64)
        requires
            old(self).safety_invariant(),
            amount <= old(self).pending_eviction,
        ensures
            final(self).capacity == old(self).capacity,
            final(self).allocated == old(self).allocated,
            final(self).reserved == old(self).reserved,
            final(self).pending_eviction == old(self).pending_eviction - amount,
            final(self).safety_invariant(),
    {
        self.pending_eviction = self.pending_eviction - amount;
    }
}

}
