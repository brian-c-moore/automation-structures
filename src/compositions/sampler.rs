// Executable carrier for Sampler.tla.
//
// Sampler selects a bounded number of items from a distribution. The TLA+ spec
// has two state variables — distribution (Items -> 0..MaxProb) and selected
// (⊆ Items) — and checks:
//
//   TypeInvariant      == distribution ∈ [Items -> 0..MaxProb] /\ selected ⊆ Items
//   BoundedSample      == Cardinality(selected) <= SampleSize
//   SupportConsistency == ∀ s ∈ selected : distribution[s] > 0
//
// with the atomic Sample action and the live Zero(i) writer, which may remove
// only an item not already owned by the selected set.
//
// Contract ceiling: selected items remain in the live support and their count
// is bounded. The carrier does not specify or verify a frequency law; that
// requires probabilistic or empirical evidence for the external draw rule.
//
// Representation:
//   - Items is the index universe 0..num_items; distribution is a Vec<u64>.
//   - selected ⊆ Items is a duplicate-free Vec<usize>, so the i ∉ selected
//     freshness of adding a new draw is an enforced precondition.

use vstd::prelude::*;

verus! {

/// A bounded sampler over a per-item distribution.
pub struct Sampler {
    /// |Items|: the item universe is the index range `0..num_items`.
    pub num_items: usize,
    /// SampleSize: the cardinality bound on `selected`.
    pub sample_size: usize,
    /// distribution ∈ [Items -> 0..MaxProb] (per-item probability weight).
    pub distribution: Vec<u64>,
    /// selected ⊆ Items, a duplicate-free Vec of item indices.
    pub selected: Vec<usize>,
}

impl Sampler {
    // ── Specifications ──────────────────────────────────────────────────

    /// Every id in `s` is a valid item index (`s ⊆ Items`).
    pub open spec fn all_valid(s: Seq<usize>, num_items: usize) -> bool {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < num_items
    }

    /// `s` is a set: no duplicate ids.
    pub open spec fn all_distinct(s: Seq<usize>) -> bool {
        forall|i: int, j: int|
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j]
    }

    /// `n ∈ selected`.
    pub open spec fn contains(&self, n: usize) -> bool {
        exists|i: int| 0 <= i < self.selected.len() && self.selected@[i] == n
    }

    /// TLA+ `TypeInvariant`: distribution spans the item universe; selected is a
    /// set of valid item ids.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.distribution.len() == self.num_items
        &&& Self::all_valid(self.selected@, self.num_items)
        &&& Self::all_distinct(self.selected@)
    }

    /// TLA+ `BoundedSample == Cardinality(selected) <= SampleSize`.
    pub open spec fn bounded_sample(&self) -> bool {
        self.selected.len() <= self.sample_size
    }

    /// TLA+ `SupportConsistency == ∀ s ∈ selected : distribution[s] > 0`.
    pub open spec fn support_consistency(&self) -> bool {
        forall|i: int|
            0 <= i < self.selected.len()
                ==> #[trigger] self.distribution@[self.selected@[i] as int] > 0
    }

    /// Full maintained invariant.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.bounded_sample() && self.support_consistency()
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct from a distribution with nothing selected yet. Realises the
    /// TLA+ `Init` predicate (selected = {}); BoundedSample and
    /// SupportConsistency hold vacuously.
    pub fn new(distribution: Vec<u64>, sample_size: usize) -> (s: Sampler)
        ensures
            s.num_items == distribution@.len(),
            s.sample_size == sample_size,
            s.distribution@ == distribution@,
            s.selected@.len() == 0,
            s.inv(),
    {
        let num_items = distribution.len();
        Sampler { num_items, sample_size, distribution, selected: Vec::new() }
    }

    // ── Membership (executable) ─────────────────────────────────────────

    /// Executable `n ∈ selected` test (discharges the freshness guard).
    pub fn contains_exec(&self, n: usize) -> (b: bool)
        ensures b == self.contains(n),
    {
        let len = self.selected.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.selected.len(),
                forall|k: int| 0 <= k < i ==> self.selected@[k] != n,
            decreases len - i,
        {
            if self.selected[i] == n {
                assert(self.selected@[i as int] == n);
                return true;
            }
            i = i + 1;
        }
        assert(!self.contains(n));
        false
    }

    // ── Sample (TLA+ Sample) ────────────────────────────────────────────

    /// Draw item `i`. Realises the TLA+ `Sample` action: guards (room remains,
    /// i is a valid item with positive probability, i not already selected) are
    /// `requires`; selected gains i and both safety invariants are re-established
    /// as `ensures` (the inductive preservation step).
    pub fn sample(&mut self, i: usize)
        requires
            old(self).inv(),
            old(self).selected.len() < old(self).sample_size,   // |selected| < SampleSize
            i < old(self).num_items,                            // i ∈ Items
            old(self).distribution@[i as int] > 0,              // i in the support
            !old(self).contains(i),                             // i ∉ selected
        ensures
            final(self).num_items == old(self).num_items,
            final(self).sample_size == old(self).sample_size,
            final(self).distribution@ == old(self).distribution@,
            final(self).selected@ == old(self).selected@.push(i),
            final(self).inv(),
    {
        let ghost os = self.selected@;
        self.selected.push(i);
        assert(self.selected@ == os.push(i));

        // selected' is still a valid set.
        assert(Self::all_valid(self.selected@, self.num_items));
        assert(Self::all_distinct(self.selected@)) by {
            assert forall|a: int, b: int|
                0 <= a < self.selected@.len() && 0 <= b < self.selected@.len() && a != b
                implies self.selected@[a] != self.selected@[b] by {
                if a < os.len() && b < os.len() {
                    // old distinctness
                } else if a == os.len() && b < os.len() {
                    assert(self.selected@[b] == os[b]);
                    assert(os[b] != i);   // i ∉ os
                } else if b == os.len() && a < os.len() {
                    assert(self.selected@[a] == os[a]);
                    assert(os[a] != i);
                }
            }
        };

        // SupportConsistency': old members keep positive probability; i is in the
        // support by the precondition.
        assert(self.support_consistency()) by {
            assert forall|a: int| 0 <= a < self.selected@.len()
                implies #[trigger] self.distribution@[self.selected@[a] as int] > 0 by {
                if a < os.len() {
                    assert(self.selected@[a] == os[a]);   // old invariant at a
                } else {
                    assert(self.selected@[a] == i);       // the pushed draw
                }
            }
        };
    }

    // ── Zero (Sampler environment action) ──────────────────────────

    /// Remove an unselected item from the live support. This is the exact
    /// `Zero(i)` writer: selected items are
    /// owned by the completed draw and cannot be zeroed afterward.
    pub fn zero(&mut self, i: usize) -> (ok: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).num_items == old(self).num_items,
            final(self).sample_size == old(self).sample_size,
            ok == (i < old(self).num_items && !old(self).contains(i)),
            ok ==> final(self).distribution@ == old(self).distribution@.update(i as int, 0),
            !ok ==> final(self).distribution@ == old(self).distribution@,
            final(self).selected@ == old(self).selected@,
    {
        if i >= self.num_items || self.contains_exec(i) {
            false
        } else {
            self.distribution.set(i, 0);
            true
        }
    }

    // ── Draw rules and empirical distribution boundary ─────────────────
    //
    // `sample` is an acceptor: the caller chooses the item and `sample`
    // checks that the choice landed in the support and inside the bound. That
    // is a faithful realization of the TLA+ `Sample` action, which is also an
    // acceptor (it picks `i` under a guard). A separate generator is required
    // before a statistical harness can measure a distribution.
    //
    // Both draw rules preserve BoundedSample and SupportConsistency. Their
    // different proposal-admission rules are outside those state predicates,
    // so no frequency result transfers from `self.inv()` alone.

    /// Weighted draw by rejection sampling. `i` is an externally proposed item
    /// index and `r` is uniform entropy in `0..max_prob`; the proposal is
    /// accepted with probability `distribution[i] / max_prob`, so over uniform
    /// `(i, r)` the accepted items occur with frequency proportional to their
    /// weight. Uniformity of those inputs is an external rely and the frequency
    /// result is not part of this function's postconditions.
    pub fn draw_weighted(&mut self, i: usize, r: u64) -> (accepted: bool)
        requires
            old(self).inv(),
            i < old(self).num_items,
        ensures
            final(self).inv(),
            final(self).num_items == old(self).num_items,
            final(self).sample_size == old(self).sample_size,
            final(self).distribution@ == old(self).distribution@,
            accepted ==> final(self).selected@ == old(self).selected@.push(i),
            !accepted ==> final(self).selected@ == old(self).selected@,
    {
        if self.selected.len() >= self.sample_size {
            return false;                       // the bound is exhausted
        }
        if r >= self.distribution[i] {
            return false;                       // REJECTED: this is the weighting
        }
        if self.contains_exec(i) {
            return false;                       // already drawn (without replacement)
        }
        self.sample(i);
        true
    }

    /// Uniform-support draw: accept any externally proposed supported item,
    /// ignoring its weight magnitude. This re-establishes the same state
    /// invariant as `draw_weighted` but supplies no weighted-frequency result.
    pub fn draw_uniform(&mut self, i: usize) -> (accepted: bool)
        requires
            old(self).inv(),
            i < old(self).num_items,
        ensures
            final(self).inv(),
            final(self).num_items == old(self).num_items,
            final(self).sample_size == old(self).sample_size,
            final(self).distribution@ == old(self).distribution@,
            accepted ==> final(self).selected@ == old(self).selected@.push(i),
            !accepted ==> final(self).selected@ == old(self).selected@,
    {
        if self.selected.len() >= self.sample_size {
            return false;
        }
        if self.distribution[i] == 0 {
            return false;                       // outside the support
        }
        if self.contains_exec(i) {
            return false;
        }
        self.sample(i);
        true
    }
}

}
