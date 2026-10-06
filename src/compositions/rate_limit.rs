// Executable RateLimit contract. The TLA+ carrier models a per-window grant
// bound with count, window_start, and a runtime-provided clock. It has two
// actions:
//
//   TryAcquire — a three-branch atomic step:
//     (1) window expired (clock - window_start >= WindowDuration):
//         window_start' = clock and count' = 1;
//     (2) else, headroom (count < MaxPerWindow): count' = count + 1;
//     (3) else: UNCHANGED (the acquire is rejected).
//   Tick — guard clock < MaxClock; clock' = clock + 1.
//
// Maintained predicates:
//
//   TypeInvariant       == count ∈ 0..MaxPerWindow /\ window_start ∈ Nat
//                          /\ clock ∈ Nat
//   WindowCountBound     == count <= MaxPerWindow
//   WindowStartNotFuture == window_start <= clock
//
// The natural-number state is represented by u64. MaxPerWindow >= 1 is a
// constructor precondition because the rollover grants one request. TryAcquire
// returns whether the request was granted; Tick's guard is a method precondition.
//
// Evidence boundary: this is a sequential witness. Each merged TLA+ action is
// one &mut self method and Rust's exclusive mutable borrow is the atomic
// boundary. A concurrent realization must supply equivalent exclusion.

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::connectives::{counter, cursor};

verus! {

/// A per-window operation bound: at most `max_per_window` acquires per
/// `window_duration` clock units, the window re-anchored at `window_start`.
pub struct RateLimit {
    /// Budget component for operations admitted in the current window.
    pub budget: crate::primitives::budget::Budget,
    /// WindowDuration (constant): the window length in clock units.
    pub window_duration: u64,
    /// MaxClock (constant): the model's clock bound (Tick's guard).
    pub max_clock: u64,
    /// window_start ∈ Nat: when the current window was anchored.
    pub window_start: u64,
    /// clock ∈ Nat: the runtime-given clock.
    pub clock: u64,
}

impl RateLimit {
    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ TypeInvariant's range clause (count ∈ 0..MaxPerWindow; the Nat
    /// typings are carried by u64), plus the constants clause MaxPerWindow >= 1
    /// that the rollover branch's count' = 1 needs (see the header note).
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.budget.capacity >= 1
        &&& self.budget.safety_invariant()
        &&& self.budget.reserved == 0
        &&& self.budget.pending_eviction == 0
    }

    /// TLA+ `WindowCountBound == count <= MaxPerWindow` (the same bound
    /// TypeInvariant's range clause states, kept under its own name for
    /// fidelity to the .cfg's invariant list).
    pub open spec fn window_count_bound(&self) -> bool {
        self.budget.allocated <= self.budget.capacity
    }

    /// TLA+ `WindowStartNotFuture == window_start <= clock`.
    pub open spec fn window_start_not_future(&self) -> bool {
        cursor::cursor_admitted(self.window_start as nat, self.clock as nat)
    }

    /// TryAcquire's branch-1 condition: `clock - window_start >= WindowDuration`
    /// (stated over int so the subtraction is exact; WindowStartNotFuture keeps it
    /// non-negative at every reachable state).
    pub open spec fn window_expired(&self) -> bool {
        self.clock as int - self.window_start as int >= self.window_duration as int
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the initial state: count = 0, window_start = 0, clock = 0.
    /// Realises the TLA+ `Init` predicate and establishes all three invariants.
    ///
    /// This proof-facing model retains zero duration in its parameter domain:
    /// every acquisition then rolls the window and succeeds, so it provides no
    /// throttling. Operational rate limiting requires a positive duration, which
    /// the checked crate-root `RateLimit` constructor enforces.
    pub fn new(max_per_window: u64, window_duration: u64, max_clock: u64) -> (r: RateLimit)
        requires
            max_per_window >= 1,   // constants clause (header note)
        ensures
            r.budget.capacity == max_per_window,
            r.window_duration == window_duration,
            r.max_clock == max_clock,
            r.budget.allocated == 0,
            r.window_start == 0,
            r.clock == 0,
            r.type_invariant(),
            r.window_count_bound(),
            r.window_start_not_future(),
    {
        RateLimit {
            budget: crate::primitives::budget::Budget::new(max_per_window),
            window_duration,
            max_clock,
            window_start: 0,
            clock: 0,
        }
    }

    // ── TryAcquire (TLA+ TryAcquire) ────────────────────────────────────

    /// Try to acquire one operation. The whole three-branch TLA+ IF is this
    /// one method: on an expired window, re-anchor AND grant in the same step
    /// (window_start' = clock, count' = 1); on headroom, grant (count' + 1);
    /// otherwise reject (UNCHANGED). Returns whether the acquire was granted.
    #[expect(clippy::arithmetic_side_effects, reason = "WindowStartNotFuture requires window_start <= clock before computing elapsed time")]
    pub fn try_acquire(&mut self) -> (acquired: bool)
        requires
            old(self).type_invariant(),
            old(self).window_start_not_future(),
        ensures
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).window_duration == old(self).window_duration,
            final(self).max_clock == old(self).max_clock,
            final(self).clock == old(self).clock,   // TryAcquire never moves the clock
            counter::stutter(old(self).clock as int, final(self).clock as int),
            cursor::cursor_admitted(
                old(self).window_start as nat,
                final(self).window_start as nat,
            ),
            acquired == (old(self).window_expired()
                || old(self).budget.allocated < old(self).budget.capacity),
            // Branch 1: rollover — re-anchor and grant, fused.
            old(self).window_expired() ==> {
                &&& final(self).window_start == old(self).clock
                &&& final(self).budget.allocated == 1
            },
            // Branch 2: grant within the window.
            (!old(self).window_expired()
                && old(self).budget.allocated < old(self).budget.capacity) ==> {
                &&& final(self).window_start == old(self).window_start
                &&& final(self).budget.allocated == old(self).budget.allocated + 1
            },
            // Branch 3: reject — UNCHANGED vars.
            (!old(self).window_expired()
                && old(self).budget.allocated >= old(self).budget.capacity) ==> {
                &&& final(self).window_start == old(self).window_start
                &&& final(self).budget.allocated == old(self).budget.allocated
            },
            final(self).type_invariant(),
            final(self).window_count_bound(),
            final(self).window_start_not_future(),
    {
        // WindowStartNotFuture makes the subtraction safe.
        let elapsed = self.clock - self.window_start;
        if elapsed >= self.window_duration {
            // Rollover: re-anchor the window at the current clock and grant
            // the acquire, in one step. count' = 1 <= max_per_window by the
            // constants clause; window_start' = clock keeps WindowStartNotFuture.
            self.window_start = self.clock;
            let allocated = self.budget.allocated;
            self.budget.release(allocated);
            let _accepted = self.budget.try_allocate(1);
            assert(_accepted);
            true
        } else {
            self.budget.try_allocate(1)
        }
    }

    /// One exact clock-only Tick transition, including its maximum-clock guard.
    pub open spec fn tick_step(before: Self, after: Self) -> bool {
        &&& before.clock < before.max_clock
        &&& after.clock as int == before.clock as int + 1
        &&& after.budget == before.budget
        &&& after.window_start == before.window_start
        &&& after.window_duration == before.window_duration
        &&& after.max_clock == before.max_clock
    }

    /// A finite sequence of zero or more exact Tick transitions.
    pub open spec fn tick_closure(before: Self, after: Self) -> bool {
        exists|path: Seq<Self>| path.len() >= 1 && path[0] == before && path.last() == after
            && forall|i: int| 0 <= i < path.len() - 1 ==> Self::tick_step(#[trigger] path[i],path[i+1])
    }

    /// Construct the explicit finite Tick path for a bounded clock observation.
    pub proof fn lemma_clock_path(before: Self, after: Self)
        requires before.clock <= after.clock <= before.max_clock,
            after.budget == before.budget, after.window_start == before.window_start,
            after.window_duration == before.window_duration, after.max_clock == before.max_clock,
        ensures Self::tick_closure(before,after),
    {
        let path = Seq::new((after.clock - before.clock + 1) as nat, |i: int| Self {
            budget: before.budget, window_start: before.window_start,
            window_duration: before.window_duration, max_clock: before.max_clock,
            clock: (before.clock + i) as u64,
        });
        assert(path[0] == before);
        assert(path.last() == after);
        assert forall|i: int| 0 <= i < path.len() - 1 implies Self::tick_step(#[trigger] path[i],path[i+1]) by {}
        assert(Self::tick_closure(before,after));
    }

    /// Observe a bounded monotonic clock value; equivalent to zero or more Tick actions.
    /// A repeated value is an accepted stutter. Regression and overflow refuse unchanged.
    pub fn advance_clock_to(&mut self, now: u64) -> (accepted: bool)
        requires old(self).type_invariant(), old(self).window_start_not_future(),
        ensures
            accepted == (old(self).clock <= now && now <= old(self).max_clock),
            accepted ==> Self::tick_closure(*old(self),*final(self)),
            final(self).clock == if accepted { now } else { old(self).clock },
            final(self).budget == old(self).budget,
            final(self).window_duration == old(self).window_duration,
            final(self).max_clock == old(self).max_clock,
            final(self).window_start == old(self).window_start,
            final(self).type_invariant(), final(self).window_start_not_future(),
            !accepted ==> *final(self) == *old(self),
    {
        if now < self.clock || now > self.max_clock { return false; }
        self.clock = now;
        proof { Self::lemma_clock_path(*old(self),*self); }
        true
    }

    // ── Tick (TLA+ Tick) ────────────────────────────────────────────────

    /// Advance the runtime-given clock by one. Realises the TLA+ `Tick`
    /// action: its guard (clock < MaxClock) is a `requires`, so the action is
    /// callable exactly when the TLA+ action is enabled.
    #[expect(clippy::arithmetic_side_effects, reason = "the enabled Tick precondition proves clock < max_clock <= u64::MAX before the successor")]
    pub fn tick(&mut self)
        requires
            old(self).type_invariant(),
            old(self).window_start_not_future(),
            old(self).clock < old(self).max_clock,   // Tick's guard
        ensures
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).window_duration == old(self).window_duration,
            final(self).max_clock == old(self).max_clock,
            final(self).budget.allocated == old(self).budget.allocated,
            final(self).window_start == old(self).window_start,
            final(self).clock == old(self).clock + 1,
            Self::tick_step(*old(self),*final(self)),
            counter::increment(old(self).clock as int, final(self).clock as int),
            final(self).type_invariant(),
            final(self).window_count_bound(),
            final(self).window_start_not_future(),
    {
        self.clock = self.clock + 1;
    }
}

}
