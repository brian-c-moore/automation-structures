// CompetitiveSelection executable correspondence boundary.
//
// CompetitiveSelection allocates scored candidates in three registered modes:
// hard, soft, and ranked. This module exposes two hard carriers for different
// consuming boundaries, plus one carrier for each other mode:
//
//   HardExclusive (CompetitiveSelectionHardExclusive) — multi-seat allocation
//     with no candidate held twice; each seat receives the lowest-position
//     argmax from its currently available pool. A score update invalidates the
//     whole coupled assignment.
//   Hard (CompetitiveSelectionHard) — the single-seat hard transition embedded
//     in SelectThenActuate. Allocation typing, winner optimality, and the
//     deterministic tie rule are stated separately.
//
//   Soft (CompetitiveSelectionSoft) — reserved-floor sequential Webster weights.
//     BoundedTotal, terminal Normalization, UniversalContribution,
//     ScoreOrderPreservation, and TieBoundedness are maintained explicitly.
//
//   Ranked (CompetitiveSelectionRanked) — top-K selection.
//     BoundedMultiplicity : |selected| <= K
//     ThresholdOptimality : every selected scores >= every non-selected
//
// Each mode discharges its checked invariants under its TLA+ actions.

use vstd::prelude::*;

verus! {

// ── shared recursive sum (for Soft's Normalization) ─────────────────────

/// Sum of `s[0..n]`, lifted to int (the SumWeights replacement).
pub open spec fn sum_to(s: Seq<u64>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else if n > s.len() as int { 0 } else { s[n - 1] as int + sum_to(s, n - 1) }
}

/// Updating index k shifts the sum by (nv - s[k]).
pub proof fn lemma_sum_update(s: Seq<u64>, k: int, nv: u64, n: int)
    requires 0 <= k < n <= s.len(),
    ensures sum_to(s.update(k, nv), n) == sum_to(s, n) - s[k] as int + nv as int,
    decreases n,
{
    if n == k + 1 {
        lemma_sum_unaffected(s, k, nv, k);
    } else {
        lemma_sum_update(s, k, nv, n - 1);
    }
}

/// Updating index k does not change the sum of a prefix that stops at or before k.
pub proof fn lemma_sum_unaffected(s: Seq<u64>, k: int, nv: u64, m: int)
    requires 0 <= m <= k < s.len(),
    ensures sum_to(s.update(k, nv), m) == sum_to(s, m),
    decreases m,
{
    if m > 0 {
        lemma_sum_unaffected(s, k, nv, m - 1);
    }
}

/// The prefix sum is non-negative.
pub proof fn lemma_sum_nonneg(s: Seq<u64>, n: int)
    requires 0 <= n <= s.len(),
    ensures sum_to(s, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_sum_nonneg(s, n - 1);
    }
}

/// The whole sum is at least the sum of any two distinct elements.
pub proof fn lemma_sum_ge_two(s: Seq<u64>, i: int, j: int, n: int)
    requires 0 <= i < n <= s.len(), 0 <= j < n, i != j,
    ensures sum_to(s, n) >= s[i] as int + s[j] as int,
    decreases n,
{
    if n - 1 == i {
        lemma_sum_ge_one(s, j, n - 1);
        lemma_sum_nonneg(s, n - 1);
    } else if n - 1 == j {
        lemma_sum_ge_one(s, i, n - 1);
        lemma_sum_nonneg(s, n - 1);
    } else {
        lemma_sum_ge_two(s, i, j, n - 1);
    }
}

/// The whole sum is at least any single element.
pub proof fn lemma_sum_ge_one(s: Seq<u64>, i: int, n: int)
    requires 0 <= i < n <= s.len(),
    ensures sum_to(s, n) >= s[i] as int,
    decreases n,
{
    if n - 1 == i {
        lemma_sum_nonneg(s, n - 1);
    } else {
        lemma_sum_ge_one(s, i, n - 1);
    }
}

/// A prefix of a non-negative sequence cannot exceed a longer prefix.
pub proof fn lemma_sum_prefix_le(s: Seq<u64>, prefix: int, end: int)
    requires 0 <= prefix <= end <= s.len(),
    ensures sum_to(s, prefix) <= sum_to(s, end),
    decreases end - prefix,
{
    if prefix < end {
        lemma_sum_prefix_le(s, prefix, end - 1);
        assert(sum_to(s, end) == s[end - 1] as int + sum_to(s, end - 1));
    }
}

/// Pushing onto a sequence does not change the sum of any existing prefix.
pub proof fn lemma_sum_push_prefix(s: Seq<u64>, v: u64, m: int)
    requires 0 <= m <= s.len(),
    ensures sum_to(s.push(v), m) == sum_to(s, m),
    decreases m,
{
    if m > 0 {
        lemma_sum_push_prefix(s, v, m - 1);
    }
}

/// An all-zero prefix has sum zero.
pub proof fn lemma_sum_zero(s: Seq<u64>, n: int)
    requires 0 <= n <= s.len(), forall|k: int| 0 <= k < n ==> s[k] == 0,
    ensures sum_to(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_sum_zero(s, n - 1);
    }
}

// ── Hard mode: one winner per seat (argmax) ─────────────────────────────

/// Hard competitive selection over one seat's candidate scores.
pub struct CompetitiveSelectionHard {
    /// Candidate scores by candidate index.
    pub scores: Vec<u64>,
    /// The winner's index, or None for NULL (no allocation).
    pub allocation: Option<usize>,
}

impl CompetitiveSelectionHard {
    /// TLA+ `AllocationTyping`: a seat's allocation is a candidate or
    /// NULL, captured by Option<usize> with an in-range winner. `winner_optimality`
    /// entails it (that clause also requires `w < self.scores.len()`), so stating it
    /// separately leaves the strength of `inv()` unchanged.
    pub open spec fn allocation_typing(&self) -> bool {
        self.allocation matches Option::Some(w) ==> w < self.scores.len()
    }

    /// TLA+ `WinnerOptimality`: a non-NULL winner scores at least as high as
    /// every candidate.
    pub open spec fn winner_optimality(&self) -> bool {
        self.allocation matches Option::Some(w) ==>
            (w < self.scores.len()
                && forall|c: int| 0 <= c < self.scores.len() ==> #[trigger] self.scores@[c] <= self.scores@[w as int])
    }

    /// TLA+ `WinnerTieBreak`: among candidates tied with the winner on score,
    /// the winner has the lowest index.
    ///
    /// `Evaluate` chooses the lowest-index argmax. Winner
    /// optimality alone permits any argmax, so this separate contract carries
    /// deterministic tie correspondence for all inputs.
    pub open spec fn winner_tie_break(&self) -> bool {
        self.allocation matches Option::Some(w) ==>
            (w < self.scores.len()
                && forall|c: int| 0 <= c < self.scores.len() ==>
                        (#[trigger] self.scores@[c] == self.scores@[w as int] ==> w <= c))
    }

    /// Whether allocation typing, optimality, and deterministic tie-breaking hold.
    pub open spec fn inv(&self) -> bool {
        self.allocation_typing() && self.winner_optimality() && self.winner_tie_break()
    }

    /// Empty allocation, all scores 0 (TLA+ Init).
    pub fn new(num_candidates: usize) -> (h: CompetitiveSelectionHard)
        ensures
            h.scores@.len() == num_candidates,
            forall|c: int| 0 <= c < num_candidates ==> h.scores@[c] == 0,
            h.allocation is None,
            h.inv(),
    {
        let mut scores: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < num_candidates
            invariant
                i <= num_candidates,
                scores.len() == i,
                forall|k: int| 0 <= k < i ==> scores@[k] == 0,
            decreases num_candidates - i,
        {
            scores.push(0);
            i = i + 1;
        }
        CompetitiveSelectionHard { scores, allocation: None }
    }

    /// Evaluate: allocate the seat to the highest-scoring candidate (argmax).
    /// Realises the TLA+ Evaluate action; re-establishes WinnerOptimality.
    pub fn evaluate(&mut self)
        requires old(self).scores.len() >= 1,
        ensures
            final(self).scores@ == old(self).scores@,
            final(self).allocation is Some,
            final(self).inv(),
    {
        let n = self.scores.len();
        let mut best: usize = 0;
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                best < i,
                n == self.scores.len(),
                forall|c: int| 0 <= c < i ==> #[trigger] self.scores@[c] <= self.scores@[best as int],
                // Tie-break preservation: among the candidates seen so far that
                // tie with `best`, `best` has the lowest index. Maintained by the
                // strict `>` in the body: a `>=` would take the later index.
                forall|c: int| 0 <= c < i ==>
                    (#[trigger] self.scores@[c] == self.scores@[best as int] ==> best <= c),
            decreases n - i,
        {
            if self.scores[i] > self.scores[best] {
                best = i;
            }
            i = i + 1;
        }
        self.allocation = Some(best);
    }

    /// Update one candidate's score; invalidate the allocation (TLA+ UpdateScore).
    pub fn update_score(&mut self, c: usize, v: u64)
        requires c < old(self).scores.len(),
        ensures
            final(self).scores@ == old(self).scores@.update(c as int, v),
            final(self).allocation is None,
            final(self).inv(),
    {
        self.scores.set(c, v);
        self.allocation = None;
    }
}

// ── Hard-exclusive mode: multi-seat available-pool argmax ──────────────

/// CompetitiveSelectionHardExclusive carrier. Candidate indices
/// are the executable WEnum order, so numeric order is exactly Pos order for
/// deterministic ties. The carrier applies the cross-seat availability filter
/// during argmax selection and globally invalidates the coupled assignment on
/// a score update.
pub struct CompetitiveSelectionHardExclusive {
    /// Number of independently allocated seats.
    pub num_seats: usize,
    /// Number of candidates shared by every seat.
    pub num_candidates: usize,
    /// Inclusive score ceiling.
    pub max_score: u64,
    /// Selected candidate by seat, encoded as `u64`.
    pub allocation: Vec<Option<u64>>,
    /// Candidate scores indexed by seat and candidate.
    pub scores: Vec<Vec<u64>>,
}

impl CompetitiveSelectionHardExclusive {
    /// Whether seat allocations and score rows have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.num_candidates >= 1
        &&& self.allocation.len() == self.num_seats
        &&& self.scores.len() == self.num_seats
        &&& (forall|s: int|
            0 <= s < self.num_seats ==> (#[trigger] self.scores@[s]).len() == self.num_candidates)
        &&& (forall|s: int|
            #![trigger self.allocation@[s]]
            0 <= s < self.num_seats ==> (self.allocation@[s] matches Some(w) ==>
                (w as int) < self.num_candidates as int))
        &&& (forall|s: int, c: int|
            0 <= s < self.num_seats && 0 <= c < self.num_candidates as int ==>
                #[trigger] self.scores@[s]@[c] <= self.max_score)
    }

    /// TLA+ Available(s), with Candidates represented by index order.
    pub open spec fn available(&self, s: int, c: int) -> bool {
        &&& 0 <= s < self.num_seats
        &&& 0 <= c < self.num_candidates as int
        &&& forall|t: int|
            0 <= t < self.num_seats && t != s ==>
                #[trigger] self.allocation@[t] != Some(c as u64)
    }

    /// Whether two seats never hold the same candidate.
    pub open spec fn mutual_exclusion(&self) -> bool {
        forall|s: int, t: int|
            #![trigger self.allocation@[s], self.allocation@[t]]
            0 <= s < self.num_seats && 0 <= t < self.num_seats && s != t
                && self.allocation@[s] is Some ==>
                    self.allocation@[s] != self.allocation@[t]
    }

    /// Whether every retained winner has maximal available score for its seat.
    pub open spec fn winner_optimality(&self) -> bool {
        forall|s: int|
            #![trigger self.allocation@[s]]
            0 <= s < self.num_seats ==> (self.allocation@[s] matches Some(w) ==>
                forall|c: int| self.available(s, c) ==>
                    #[trigger] self.scores@[s]@[c] <= self.scores@[s]@[w as int])
    }

    /// Whether equal-score winners use the lowest available candidate index.
    pub open spec fn winner_tie_break(&self) -> bool {
        forall|s: int|
            #![trigger self.allocation@[s]]
            0 <= s < self.num_seats ==> (self.allocation@[s] matches Some(w) ==>
                forall|c: int| self.available(s, c) &&
                    #[trigger] self.scores@[s]@[c] == self.scores@[s]@[w as int]
                        ==> (w as int) <= c)
    }

    /// Whether all hard-exclusive selection obligations hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.mutual_exclusion()
            && self.winner_optimality() && self.winner_tie_break()
    }

    /// Construct empty allocations and zero scores for every seat.
    pub fn new(
        num_seats: usize,
        num_candidates: usize,
        max_score: u64,
    ) -> (r: CompetitiveSelectionHardExclusive)
        requires num_candidates >= 1,
        ensures
            r.num_seats == num_seats,
            r.num_candidates == num_candidates,
            r.max_score == max_score,
            r.allocation.len() == num_seats,
            r.scores.len() == num_seats,
            forall|s: int| 0 <= s < num_seats ==> r.allocation@[s] is None,
            forall|s: int| 0 <= s < num_seats ==>
                (#[trigger] r.scores@[s]).len() == num_candidates,
            forall|s: int, c: int|
                0 <= s < num_seats && 0 <= c < num_candidates ==>
                    #[trigger] r.scores@[s]@[c] == 0,
            r.inv(),
    {
        let mut allocation: Vec<Option<u64>> = Vec::new();
        let mut scores: Vec<Vec<u64>> = Vec::new();
        let mut s: usize = 0;
        while s < num_seats
            invariant
                s <= num_seats,
                allocation.len() == s,
                scores.len() == s,
                forall|i: int| 0 <= i < s ==> allocation@[i] is None,
                forall|i: int| 0 <= i < s ==>
                    (#[trigger] scores@[i]).len() == num_candidates,
                forall|i: int, j: int|
                    0 <= i < s && 0 <= j < num_candidates ==>
                        #[trigger] scores@[i]@[j] == 0,
            decreases num_seats - s,
        {
            let mut row: Vec<u64> = Vec::new();
            let mut c: usize = 0;
            while c < num_candidates
                invariant
                    c <= num_candidates,
                    row.len() == c,
                    forall|j: int| 0 <= j < c ==> #[trigger] row@[j] == 0,
                decreases num_candidates - c,
            {
                row.push(0);
                c = c + 1;
            }
            allocation.push(None);
            scores.push(row);
            s = s + 1;
        }
        CompetitiveSelectionHardExclusive {
            num_seats,
            num_candidates,
            max_score,
            allocation,
            scores,
        }
    }

    /// Read one in-range seat-candidate score.
    pub fn score_at(&self, s: usize, c: usize) -> (v: u64)
        requires
            s < self.scores.len(),
            c < self.scores@[s as int].len(),
        ensures v == self.scores@[s as int]@[c as int],
    {
        self.scores[s][c]
    }

    /// Executable Available(s) membership check.
    pub fn candidate_available(&self, s: usize, c: usize) -> (available: bool)
        requires
            self.type_invariant(),
            s < self.num_seats,
            c < self.num_candidates,
        ensures available == self.available(s as int, c as int),
    {
        let mut t: usize = 0;
        while t < self.num_seats
            invariant
                t <= self.num_seats,
                s < self.num_seats,
                c < self.num_candidates,
                self.type_invariant(),
                forall|j: int| 0 <= j < t && j != s as int ==>
                    #[trigger] self.allocation@[j] != Some(c as u64),
            decreases self.num_seats - t,
        {
            if t != s && self.allocation[t] == Some(c as u64) {
                return false;
            }
            t = t + 1;
        }
        true
    }

    /// Executable guard for `Available(s) /= {}`.
    pub fn has_available(&self, s: usize) -> (available: bool)
        requires
            self.type_invariant(),
            s < self.num_seats,
        ensures available == (exists|c: int| self.available(s as int, c)),
    {
        let mut c: usize = 0;
        while c < self.num_candidates
            invariant
                c <= self.num_candidates,
                s < self.num_seats,
                self.type_invariant(),
                forall|j: int| 0 <= j < c ==>
                    !self.available(s as int, j),
            decreases self.num_candidates - c,
        {
            if self.candidate_available(s, c) {
                return true;
            }
            c = c + 1;
        }
        false
    }

    /// TLA+ Evaluate(s): atomically select the lowest-index argmax from the
    /// candidates not held by another seat.
    pub fn evaluate(&mut self, s: usize)
        requires
            old(self).inv(),
            s < old(self).num_seats,
            old(self).allocation@[s as int] is None,
            exists|c: int| old(self).available(s as int, c),
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).num_candidates == old(self).num_candidates,
            final(self).max_score == old(self).max_score,
            final(self).scores@ == old(self).scores@,
            final(self).allocation.len() == old(self).allocation.len(),
            forall|t: int| 0 <= t < final(self).num_seats && t != s as int ==>
                final(self).allocation@[t] == old(self).allocation@[t],
            final(self).allocation@[s as int] is Some,
            final(self).inv(),
    {
        let n = self.num_candidates;
        let mut best: usize = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.num_candidates,
                s < self.num_seats,
                self.inv(),
                self.scores@ == old(self).scores@,
                self.allocation@ == old(self).allocation@,
                self.num_seats == old(self).num_seats,
                self.num_candidates == old(self).num_candidates,
                self.max_score == old(self).max_score,
                found == (exists|c: int| 0 <= c < i && self.available(s as int, c)),
                found ==> best < i,
                found ==> self.available(s as int, best as int),
                found ==> forall|c: int| 0 <= c < i && self.available(s as int, c) ==>
                    #[trigger] self.scores@[s as int]@[c]
                        <= self.scores@[s as int]@[best as int],
                found ==> forall|c: int| 0 <= c < i && self.available(s as int, c)
                    && #[trigger] self.scores@[s as int]@[c]
                        == self.scores@[s as int]@[best as int] ==> best as int <= c,
            decreases n - i,
        {
            if self.candidate_available(s, i) {
                if !found {
                    best = i;
                    found = true;
                } else {
                    let vi = self.score_at(s, i);
                    let vb = self.score_at(s, best);
                    if vi > vb {
                        best = i;
                    }
                }
            }
            i = i + 1;
        }
        assert(found);
        assert(self.available(s as int, best as int));
        assert(forall|c: int| self.available(s as int, c) ==>
            #[trigger] self.scores@[s as int]@[c]
                <= self.scores@[s as int]@[best as int]);
        assert(forall|c: int| self.available(s as int, c)
            && #[trigger] self.scores@[s as int]@[c]
                == self.scores@[s as int]@[best as int] ==> best as int <= c);
        assert((best as u64) as int == best as int);
        self.allocation.set(s, Some(best as u64));

        assert(self.type_invariant()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==>
                    (w as int) < self.num_candidates as int) by {
                if t != s as int {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                }
            }
        }
        assert(self.mutual_exclusion()) by {
            assert forall|a: int, b: int|
                #![trigger self.allocation@[a], self.allocation@[b]]
                0 <= a < self.num_seats && 0 <= b < self.num_seats && a != b
                    && self.allocation@[a] is Some implies
                        self.allocation@[a] != self.allocation@[b] by {
                if a == s as int {
                    assert(self.allocation@[a] == Some(best as u64));
                    assert(old(self).available(s as int, best as int));
                    assert(self.allocation@[b] == old(self).allocation@[b]);
                } else if b == s as int {
                    assert(self.allocation@[b] == Some(best as u64));
                    assert(old(self).available(s as int, best as int));
                    assert(self.allocation@[a] == old(self).allocation@[a]);
                } else {
                    assert(self.allocation@[a] == old(self).allocation@[a]);
                    assert(self.allocation@[b] == old(self).allocation@[b]);
                }
            }
        }
        assert(self.winner_optimality()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==>
                    forall|c: int| self.available(t, c) ==>
                        #[trigger] self.scores@[t]@[c] <= self.scores@[t]@[w as int]) by {
                if t == s as int {
                    assert(self.allocation@[t] == Some(best as u64));
                    assert forall|c: int| self.available(t, c) implies
                        old(self).available(t, c) by {
                        assert forall|r: int|
                            0 <= r < self.num_seats && r != t implies
                                old(self).allocation@[r] != Some(c as u64) by {
                            assert(r != s as int);
                            assert(self.allocation@[r] == old(self).allocation@[r]);
                        }
                    }
                } else {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                    assert forall|c: int| self.available(t, c) implies
                        old(self).available(t, c) by {
                        assert forall|r: int|
                            0 <= r < self.num_seats && r != t implies
                                old(self).allocation@[r] != Some(c as u64) by {
                            if r == s as int {
                                assert(old(self).allocation@[r] is None);
                            } else {
                                assert(self.allocation@[r] == old(self).allocation@[r]);
                            }
                        }
                    }
                }
            }
        }
        assert(self.winner_tie_break()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==>
                    forall|c: int| self.available(t, c)
                        && #[trigger] self.scores@[t]@[c] == self.scores@[t]@[w as int]
                            ==> (w as int) <= c) by {
                if t == s as int {
                    assert(self.allocation@[t] == Some(best as u64));
                    assert forall|c: int| self.available(t, c) implies
                        old(self).available(t, c) by {
                        assert forall|r: int|
                            0 <= r < self.num_seats && r != t implies
                                old(self).allocation@[r] != Some(c as u64) by {
                            assert(r != s as int);
                            assert(self.allocation@[r] == old(self).allocation@[r]);
                        }
                    }
                } else {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                    assert forall|c: int| self.available(t, c) implies
                        old(self).available(t, c) by {
                        assert forall|r: int|
                            0 <= r < self.num_seats && r != t implies
                                old(self).allocation@[r] != Some(c as u64) by {
                            if r == s as int {
                                assert(old(self).allocation@[r] is None);
                            } else {
                                assert(self.allocation@[r] == old(self).allocation@[r]);
                            }
                        }
                    }
                }
            }
        }
    }

    /// TLA+ UpdateScore(s,c,v): update one score and invalidate every seat in
    /// the same commit because availability couples their optimality.
    pub fn update_score(&mut self, s: usize, c: usize, v: u64)
        requires
            old(self).inv(),
            s < old(self).num_seats,
            c < old(self).num_candidates,
            v <= old(self).max_score,
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).num_candidates == old(self).num_candidates,
            final(self).max_score == old(self).max_score,
            final(self).scores.len() == old(self).scores.len(),
            forall|t: int| 0 <= t < final(self).num_seats && t != s as int ==>
                final(self).scores@[t]@ == old(self).scores@[t]@,
            final(self).scores@[s as int]@
                == old(self).scores@[s as int]@.update(c as int, v),
            forall|t: int| 0 <= t < final(self).num_seats ==>
                final(self).allocation@[t] is None,
            final(self).inv(),
    {
        let ghost old_row = self.scores@[s as int]@;
        let row_len = self.scores[s].len();
        let mut new_row: Vec<u64> = Vec::new();
        let mut k: usize = 0;
        while k < row_len
            invariant
                k <= row_len,
                row_len == self.scores@[s as int].len(),
                row_len == self.num_candidates,
                c < row_len,
                s < self.num_seats,
                self.scores.len() == self.num_seats,
                new_row.len() == k,
                old_row == old(self).scores@[s as int]@,
                old_row.len() == row_len,
                forall|j: int| 0 <= j < k ==>
                    new_row@[j] == (if j == c as int { v } else { old_row[j] }),
                self.scores@ == old(self).scores@,
                self.allocation@ == old(self).allocation@,
                self.num_seats == old(self).num_seats,
                self.num_candidates == old(self).num_candidates,
                self.max_score == old(self).max_score,
            decreases row_len - k,
        {
            if k == c {
                new_row.push(v);
            } else {
                let x = self.score_at(s, k);
                new_row.push(x);
            }
            k = k + 1;
        }
        assert(new_row@ == old_row.update(c as int, v)) by {
            assert(new_row.len() == old_row.len());
            assert forall|j: int| 0 <= j < new_row.len() implies
                new_row@[j] == old_row.update(c as int, v)[j] by {
                if j == c as int {
                } else {
                }
            }
        }
        self.scores.set(s, new_row);
        let ghost updated_scores = self.scores@;
        assert(updated_scores.len() == old(self).scores@.len());
        assert(updated_scores[s as int]@ == old(self).scores@[s as int]@.update(c as int, v));
        assert forall|j: int| 0 <= j < self.num_seats && j != s as int implies
            updated_scores[j]@ == old(self).scores@[j]@ by {
        }

        let mut t: usize = 0;
        while t < self.num_seats
            invariant
                t <= self.num_seats,
                self.num_seats == old(self).num_seats,
                self.num_candidates == old(self).num_candidates,
                self.max_score == old(self).max_score,
                self.allocation.len() == self.num_seats,
                forall|j: int| 0 <= j < t ==> self.allocation@[j] is None,
                forall|j: int| t <= j < self.num_seats ==>
                    self.allocation@[j] == old(self).allocation@[j],
                self.scores@ == updated_scores,
                updated_scores.len() == old(self).scores@.len(),
                updated_scores[s as int]@
                    == old(self).scores@[s as int]@.update(c as int, v),
                forall|j: int| 0 <= j < self.num_seats && j != s as int ==>
                    updated_scores[j]@ == old(self).scores@[j]@,
            decreases self.num_seats - t,
        {
            self.allocation.set(t, None);
            t = t + 1;
        }

        assert(self.type_invariant()) by {
            assert forall|i: int| 0 <= i < self.num_seats implies
                (#[trigger] self.scores@[i]).len() == self.num_candidates by {
                if i != s as int {
                    assert(self.scores@[i]@ == old(self).scores@[i]@);
                }
            }
            assert forall|i: int, j: int|
                0 <= i < self.num_seats && 0 <= j < self.num_candidates as int implies
                    #[trigger] self.scores@[i]@[j] <= self.max_score by {
                if i == s as int && j == c as int {
                } else if i == s as int {
                } else {
                    assert(self.scores@[i]@ == old(self).scores@[i]@);
                }
            }
        }
    }
}

// ── Soft mode: reserved-floor sequential Sainte-Lague (Webster) ─────────
//
// Weights are derived from evolving `extra` state: one reserved unit per
// candidate, followed by Pool awards to the current highest-priority candidate.
// Priority is `scores[c] / (2*extra[c]+1)` and is compared by cross-
// multiplication to avoid division and reals.

/// Cross-multiplied priority comparison: priority(a) >= priority(b), i.e.
/// scores[a]/(2*extra[a]+1) >= scores[b]/(2*extra[b]+1) without division.
pub open spec fn priority_ge(scores: Seq<u64>, extra: Seq<u64>, a: int, b: int) -> bool {
    scores[a] as int * (2 * extra[b] as int + 1) >= scores[b] as int * (2 * extra[a] as int + 1)
}

/// Strict and equal forms of the same priority comparison. Equality is the
/// seam at which the WEnum/Pos rule chooses the lowest index.
pub open spec fn priority_gt(scores: Seq<u64>, extra: Seq<u64>, a: int, b: int) -> bool {
    scores[a] as int * (2 * extra[b] as int + 1) > scores[b] as int * (2 * extra[a] as int + 1)
}

/// Whether two candidates have equal cross-multiplied priority.
pub open spec fn priority_equal(scores: Seq<u64>, extra: Seq<u64>, a: int, b: int) -> bool {
    scores[a] as int * (2 * extra[b] as int + 1) == scores[b] as int * (2 * extra[a] as int + 1)
}

/// A strict priority step followed by a non-strict one remains strict. This
/// is the discriminator needed to preserve the lowest-index tie fact when a
/// later scan element displaces the running winner.
pub proof fn lemma_priority_gt_ge_not_equal(
    scores: Seq<u64>, extra: Seq<u64>, a: int, b: int, c: int,
)
    requires
        priority_gt(scores, extra, a, b),
        priority_ge(scores, extra, b, c),
    ensures
        !priority_equal(scores, extra, a, c),
{
    let sa = scores[a] as int;
    let sb = scores[b] as int;
    let sc = scores[c] as int;
    let a_den = 2 * extra[a] as int + 1;
    let b_den = 2 * extra[b] as int + 1;
    let c_den = 2 * extra[c] as int + 1;
    assert(sa * b_den * c_den > sb * a_den * c_den) by (nonlinear_arith)
        requires sa * b_den > sb * a_den, c_den > 0;
    assert(sb * c_den * a_den >= sc * b_den * a_den) by (nonlinear_arith)
        requires sb * c_den >= sc * b_den, a_den > 0;
    assert(sa * b_den * c_den > sc * b_den * a_den) by (nonlinear_arith)
        requires
            sa * b_den * c_den > sb * a_den * c_den,
            sb * c_den * a_den >= sc * b_den * a_den;
    assert(sa * c_den > sc * a_den) by (nonlinear_arith)
        requires sa * b_den * c_den > sc * b_den * a_den, b_den > 0;
}

/// Winner predicate for one `AssignNext` action, including the lowest-index tie.
pub open spec fn priority_winner(scores: Seq<u64>, extra: Seq<u64>, w: int) -> bool {
    0 <= w < scores.len()
        && scores.len() == extra.len()
        && (forall|c: int| 0 <= c < scores.len() ==> priority_ge(scores, extra, w, c))
        && (forall|c: int| 0 <= c < scores.len() && priority_equal(scores, extra, w, c)
            ==> w <= c)
}

/// Sainte-Lague's catch-up property: if a's priority dominates b's and a's
/// score is strictly lower, a's extra must already be strictly lower too.
/// This is what keeps a strictly-lower-scored candidate from ever catching
/// up to or passing a strictly-higher-scored one (ScoreOrderPreservation).
pub proof fn lemma_priority_strict(scores: Seq<u64>, extra: Seq<u64>, a: int, b: int)
    requires
        priority_ge(scores, extra, a, b),
        scores[a] < scores[b],
    ensures
        extra[a] < extra[b],
{
    if extra[a] >= extra[b] {
        assert(scores[b] as int * (2 * extra[a] as int + 1)
            > scores[a] as int * (2 * extra[b] as int + 1)) by (nonlinear_arith)
            requires scores[a] < scores[b], extra[a] >= extra[b], scores[a] >= 0, scores[b] >= 0,
                extra[a] >= 0, extra[b] >= 0;
        assert(false);
    }
}

/// Sainte-Lague's tie-bound property: if a's priority dominates b's and the
/// two scores are equal, a's extra is at most b's (TieBoundedness).
pub proof fn lemma_priority_tie(scores: Seq<u64>, extra: Seq<u64>, a: int, b: int)
    requires
        priority_ge(scores, extra, a, b),
        scores[a] == scores[b],
        scores[a] > 0,
    ensures
        extra[a] <= extra[b],
{
    if extra[a] > extra[b] {
        assert(scores[b] as int * (2 * extra[a] as int + 1)
            > scores[a] as int * (2 * extra[b] as int + 1)) by (nonlinear_arith)
            requires scores[a] == scores[b], scores[a] > 0, extra[a] > extra[b],
                extra[a] >= 0, extra[b] >= 0;
        assert(false);
    }
}

/// Transitivity of the cross-multiplied priority order: needed because the
/// linear scan for the current highest-priority candidate only ever compares
/// the running best against one new candidate at a time, so replacing the
/// running best requires knowing it still dominates everyone scanned so far,
/// not just the candidate that just displaced it.  The three-term product
/// argument: multiply each hypothesis by the missing denominator, chain the
/// two resulting inequalities through their shared middle term, then cancel
/// the common positive factor (2*extra[b]+1).
pub proof fn lemma_priority_ge_trans(scores: Seq<u64>, extra: Seq<u64>, a: int, b: int, c: int)
    requires
        priority_ge(scores, extra, a, b),
        priority_ge(scores, extra, b, c),
    ensures
        priority_ge(scores, extra, a, c),
{
    let sa = scores[a] as int;
    let sb = scores[b] as int;
    let sc = scores[c] as int;
    let a_den = 2 * extra[a] as int + 1;
    let b_den = 2 * extra[b] as int + 1;
    let c_den = 2 * extra[c] as int + 1;
    assert(sa * b_den * c_den >= sb * a_den * c_den) by (nonlinear_arith)
        requires sa * b_den >= sb * a_den, c_den >= 0;
    assert(sb * c_den * a_den >= sc * b_den * a_den) by (nonlinear_arith)
        requires sb * c_den >= sc * b_den, a_den >= 0;
    assert(sa * b_den * c_den >= sc * b_den * a_den) by (nonlinear_arith)
        requires
            sa * b_den * c_den >= sb * a_den * c_den,
            sb * c_den * a_den >= sc * b_den * a_den;
    assert(sa * c_den >= sc * a_den) by (nonlinear_arith)
        requires
            sa * b_den * c_den >= sc * b_den * a_den,
            b_den > 0;
}

/// Monotonicity of the priority product in `extra`: needed by the Webster
/// no-transfer invariant's preservation step, where an award to `best`
/// raises the odd multiplier on the left side of every retained inequality.
pub proof fn lemma_priority_lhs_monotone(s: int, e: int, f: int)
    requires s >= 0, e <= f,
    ensures s * (2 * e + 1) <= s * (2 * f + 1),
{
    assert(s * (2 * e + 1) <= s * (2 * f + 1)) by (nonlinear_arith)
        requires s >= 0, e <= f;
}

/// Soft competitive selection: weights derived from an evolving `extra` via
/// the reserved-floor sequential Webster award process, not chosen freely.
pub struct CompetitiveSelectionSoft {
    /// Extra Webster awards by candidate index.
    pub extra: Vec<u64>,
    /// Candidate scores by candidate index.
    pub scores: Vec<u64>,
    /// Total weight available for assignment.
    pub weight_total: u64,
    /// MaxScore for this refinement profile.
    pub max_score: u64,
}

impl CompetitiveSelectionSoft {
    /// extra and scores share the Candidates domain, at least one candidate.
    pub open spec fn well_formed(&self) -> bool {
        self.extra.len() == self.scores.len() && self.extra.len() > 0
    }

    /// Executable instance of TLA+ `scores \in [Candidates -> 1..MaxScore]`.
    pub open spec fn score_bounds(&self) -> bool {
        forall|i: int| 0 <= i < self.scores.len() ==>
            #[trigger] self.scores@[i] >= 1 && self.scores@[i] <= self.max_score
    }

    /// The reserved unit plus whatever extra units this candidate has been
    /// awarded so far -- derived, not a state variable in its own right.
    pub open spec fn weight(&self, i: int) -> int {
        1 + self.extra@[i] as int
    }

    /// TLA+ `UniversalContribution`: holds unconditionally, weight >= 1.
    pub open spec fn universal_contribution(&self) -> bool {
        forall|i: int| 0 <= i < self.extra.len() ==> #[trigger] self.weight(i) > 0
    }

    /// TLA+ `ScoreOrderPreservation`: a strictly higher score never receives a
    /// lower weight.
    pub open spec fn score_order_preservation(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < self.scores.len() && 0 <= j < self.scores.len()
                && self.scores@[i] < self.scores@[j]
                ==> #[trigger] self.weight(i) <= #[trigger] self.weight(j)
    }

    /// TLA+ `TieBoundedness`: tied candidates' weights differ by at most one.
    pub open spec fn tie_boundedness(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < self.scores.len() && 0 <= j < self.scores.len()
                && self.scores@[i] == self.scores@[j]
                ==> #[trigger] self.weight(i) <= #[trigger] self.weight(j) + 1
    }

    /// TLA+ `Normalization`: weights sum to the fixed total, Reserved + Pool.
    pub open spec fn normalization(&self) -> bool {
        sum_to(self.extra@, self.extra@.len() as int) + self.extra@.len() as int
            == self.weight_total as int
    }

    /// TLA+ `BoundedTotal`: partial award states never exceed WeightTotal.
    pub open spec fn bounded_total(&self) -> bool {
        sum_to(self.extra@, self.extra@.len() as int) + self.extra@.len() as int
            <= self.weight_total as int
    }

    /// TLA+ `Terminal`, stated independently in terms of awarded extra units.
    pub open spec fn terminal(&self) -> bool {
        sum_to(self.extra@, self.extra@.len() as int)
            == self.weight_total as int - self.extra@.len() as int
    }

    /// TLA+ `Normalization`: exact total is required only at Terminal.
    pub open spec fn normalization_when_terminal(&self) -> bool {
        self.terminal() ==> self.normalization()
    }

    /// Proof-only overflow bound: every candidate's extra is at most
    /// weight_total, so the cross-multiplied priority comparison and the
    /// derived weight never overflow u64.
    pub open spec fn bounded(&self) -> bool {
        self.weight_total <= 1_000_000_000
            && self.max_score <= 1_000_000_000
            && forall|k: int| 0 <= k < self.extra.len() ==> #[trigger] self.extra@[k] <= self.weight_total
    }

    /// The invariant of every reachable CompetitiveSelectionSoftMutableScores state,
    /// including the reserved-floor state after a mutable score update.
    pub open spec fn mutable_score_inv(&self) -> bool {
        self.well_formed()
            && self.weight_total as int >= self.extra.len() as int
            && self.score_bounds()
            && self.bounded()
            && self.bounded_total()
            && self.normalization_when_terminal()
            && self.universal_contribution()
            && self.score_order_preservation()
            && self.tie_boundedness()
    }

    /// The finished apportionment is a Webster (Sainte-Lague) one: no candidate
    /// holding an awarded unit could have been passed over for it -- the
    /// no-transfer characterization. With `normalization()` fixing the total it
    /// characterizes the returned Webster allocation as a set. It does not by
    /// itself select the unique tie-broken sequence produced by `Init` and
    /// `AssignNext` because this clause contains no tie-order premise.
    pub open spec fn webster_allocation(&self) -> bool {
        forall|i: int, j: int| #![trigger self.extra@[i], self.extra@[j]]
            0 <= i < self.extra.len() && 0 <= j < self.extra.len()
                && self.extra@[i] >= 1
                ==> self.scores@[i] as int * (2 * self.extra@[j] as int + 1)
                        >= self.scores@[j] as int * (2 * self.extra@[i] as int - 1)
    }

    /// Whether mutable-score safety and terminal normalization hold.
    pub open spec fn inv(&self) -> bool {
        self.mutable_score_inv() && self.normalization()
    }

    /// Executable accessor for the derived weight (`1 + extra[i]`).
    pub fn weight_at(&self, i: usize) -> (w: u64)
        requires i < self.extra.len(), self.bounded(),
        ensures w as int == self.weight(i as int),
    {
        self.extra[i] + 1
    }

    /// Number of units currently assigned, including one reserved unit per candidate.
    pub fn assigned_weight(&self) -> (total: u64)
        requires self.mutable_score_inv(),
        ensures
            total as int
                == sum_to(self.extra@, self.extra@.len() as int) + self.extra@.len() as int,
            total <= self.weight_total,
    {
        let len = self.extra.len();
        let mut total = len as u64;
        let mut index: usize = 0;
        proof {
            assert(self.bounded_total());
        }
        while index < len
            invariant
                index <= len,
                len == self.extra.len(),
                total as int == sum_to(self.extra@, index as int) + len as int,
                total <= self.weight_total,
                sum_to(self.extra@, len as int) + len as int <= self.weight_total as int,
            decreases len - index,
        {
            proof {
                assert(sum_to(self.extra@, index as int + 1)
                    == self.extra@[index as int] as int
                        + sum_to(self.extra@, index as int));
                lemma_sum_prefix_le(self.extra@, index as int + 1, len as int);
                assert(sum_to(self.extra@, index as int + 1) + len as int
                    <= self.weight_total as int);
                assert(total as int + self.extra@[index as int] as int
                    <= self.weight_total as int);
            }
            total = total + self.extra[index];
            index += 1;
        }
        total
    }

    /// TLA+ `Init`: scores are mutable state and every candidate begins with only
    /// its reserved unit. Unlike `new`, this does not run the award process to
    /// Terminal; it exposes the action-level carrier state.
    pub fn init(scores: Vec<u64>, weight_total: u64, max_score: u64) -> (s: CompetitiveSelectionSoft)
        requires
            scores.len() >= 1,
            weight_total >= scores.len() as u64,
            weight_total <= 1_000_000_000,
            max_score <= 1_000_000_000,
            forall|i: int| 0 <= i < scores.len() ==>
                #[trigger] scores@[i] >= 1 && scores@[i] <= max_score,
        ensures
            s.scores@ == scores@,
            s.weight_total == weight_total,
            s.max_score == max_score,
            s.extra@.len() == scores@.len(),
            forall|i: int| 0 <= i < s.extra.len() ==> s.extra@[i] == 0,
            s.mutable_score_inv(),
    {
        let n = scores.len();
        let mut extra: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                extra.len() == i,
                forall|k: int| 0 <= k < i ==> extra@[k] == 0,
                sum_to(extra@, i as int) == 0,
            decreases n - i,
        {
            let ghost eold = extra@;
            extra.push(0);
            proof {
                lemma_sum_push_prefix(eold, 0, i as int);
                assert(sum_to(extra@, i as int + 1)
                    == extra@[i as int] as int + sum_to(extra@, i as int));
            }
            i = i + 1;
        }
        proof {
            assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n
                && scores@[a] < scores@[b]
                implies 1 + extra@[a] as int <= 1 + extra@[b] as int by {}
            assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n
                && scores@[a] == scores@[b]
                implies 1 + extra@[a] as int <= 1 + extra@[b] as int + 1 by {}
        }
        CompetitiveSelectionSoft { extra, scores, weight_total, max_score }
    }

    /// Construct the reserved-floor sequential Webster allocation over
    /// `scores`: one guaranteed unit per candidate, then Pool further units
    /// awarded one at a time to the current highest-priority candidate.
    /// Mirrors CompetitiveSelectionSoft.tla's Init + AssignNext exactly.
    pub fn new(scores: Vec<u64>, weight_total: u64, max_score: u64) -> (s: CompetitiveSelectionSoft)
        requires
            scores.len() >= 1,
            weight_total >= scores.len() as u64,
            weight_total <= 1_000_000_000,
            max_score <= 1_000_000_000,
            forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores@[i] >= 1 && scores@[i] <= max_score,
        ensures
            s.scores@ == scores@,
            s.weight_total == weight_total,
            s.max_score == max_score,
            s.mutable_score_inv(),
            s.inv(),
            s.webster_allocation(),
    {
        let n = scores.len();
        let pool: u64 = weight_total - (n as u64);
        let mut extra: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                extra.len() == i,
                forall|k: int| 0 <= k < i ==> extra@[k] == 0,
                sum_to(extra@, i as int) == 0,
            decreases n - i,
        {
            let ghost eold = extra@;
            extra.push(0);
            proof {
                lemma_sum_push_prefix(eold, 0, i as int);
                assert(sum_to(extra@, i as int + 1) == extra@[i as int] as int + sum_to(extra@, i as int));
            }
            i = i + 1;
        }

        let mut awarded: u64 = 0;
        while awarded < pool
            invariant
                extra.len() == n,
                n == scores.len(),
                n >= 1,
                weight_total >= n as u64,
                weight_total <= 1_000_000_000,
                pool == weight_total - (n as u64),
                awarded <= pool,
                forall|k: int| 0 <= k < n ==> #[trigger] scores@[k] >= 1 && scores@[k] <= 1_000_000_000,
                sum_to(extra@, n as int) == awarded as int,
                forall|k: int| 0 <= k < n ==> #[trigger] extra@[k] <= awarded,
                forall|c: int, d: int|
                    0 <= c < n && 0 <= d < n && scores@[c] < scores@[d]
                        ==> 1 + extra@[c] as int <= 1 + extra@[d] as int,
                forall|c: int, d: int|
                    0 <= c < n && 0 <= d < n && scores@[c] == scores@[d]
                        ==> 1 + extra@[c] as int <= 1 + extra@[d] as int + 1,
                // The Webster no-transfer invariant: every candidate
                // holding an awarded unit had priority at least everyone's at
                // the moment of its last award. Vacuous at the all-zero entry
                // state; preserved because each award goes to the scan's
                // priority-maximal index.
                forall|c: int, d: int|
                    0 <= c < n && 0 <= d < n && extra@[c] >= 1
                        ==> scores@[c] as int * (2 * extra@[d] as int + 1)
                                >= scores@[d] as int * (2 * extra@[c] as int - 1),
            decreases pool - awarded,
        {
            let mut best: usize = 0;
            let mut j: usize = 1;
            while j < n
                invariant
                    1 <= j <= n,
                    best < j,
                    extra.len() == n,
                    n == scores.len(),
                    weight_total <= 1_000_000_000,
                    pool == weight_total - (n as u64),
                    awarded <= pool,
                    forall|k: int| 0 <= k < n ==> #[trigger] scores@[k] <= 1_000_000_000,
                    forall|k: int| 0 <= k < n ==> #[trigger] extra@[k] <= awarded,
                    forall|c: int| 0 <= c < j ==> priority_ge(scores@, extra@, best as int, c),
                decreases n - j,
            {
                proof {
                    assert((scores@[j as int] as int) * (2 * (extra@[best as int] as int) + 1)
                        <= 1_000_000_000 * (2 * 1_000_000_000 + 1)) by (nonlinear_arith)
                        requires
                            scores@[j as int] as int <= 1_000_000_000,
                            extra@[best as int] as int <= 1_000_000_000;
                    assert((scores@[best as int] as int) * (2 * (extra@[j as int] as int) + 1)
                        <= 1_000_000_000 * (2 * 1_000_000_000 + 1)) by (nonlinear_arith)
                        requires
                            scores@[best as int] as int <= 1_000_000_000,
                            extra@[j as int] as int <= 1_000_000_000;
                }
                let lhs: u128 = (scores[j] as u128) * (2 * (extra[best] as u128) + 1);
                let rhs: u128 = (scores[best] as u128) * (2 * (extra[j] as u128) + 1);
                proof {
                    assert(lhs as int == scores@[j as int] as int * (2 * extra@[best as int] as int + 1));
                    assert(rhs as int == scores@[best as int] as int * (2 * extra@[j as int] as int + 1));
                }
                let old_best: usize = best;
                let old_j: usize = j;
                let _ = (old_best, old_j);
                if lhs > rhs {
                    best = j;
                    proof {
                        assert(priority_ge(scores@, extra@, old_j as int, old_best as int));
                        assert forall|c: int| 0 <= c < old_j as int + 1
                            implies priority_ge(scores@, extra@, best as int, c)
                        by {
                            if c == old_best as int {
                                assert(priority_ge(scores@, extra@, old_j as int, old_best as int));
                            } else if c < old_j as int {
                                lemma_priority_ge_trans(scores@, extra@, old_j as int, old_best as int, c);
                            } else {
                                // c == old_j as int == best as int, reflexive
                            }
                        }
                    }
                } else {
                    proof {
                        assert(priority_ge(scores@, extra@, old_best as int, old_j as int));
                        assert forall|c: int| 0 <= c < old_j as int + 1
                            implies priority_ge(scores@, extra@, best as int, c)
                        by {
                            if c == old_j as int {
                                assert(priority_ge(scores@, extra@, old_best as int, old_j as int));
                            } else {
                                // c < old_j: unchanged from the pre-iteration invariant
                            }
                        }
                    }
                }
                j = j + 1;
            }
            let ghost extra_old: Seq<u64> = extra@;
            let ghost best_g: int = best as int;
            // Capture the pre-award invariant explicitly, in terms of extra_old:
            // once extra is mutated below, the loop invariant clauses (stated in
            // terms of the current extra@) stop referring to this snapshot, so
            // the facts needed for the case split have to be pinned down first.
            proof {
                assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && scores@[c] < scores@[d]
                    implies 1 + extra_old[c] as int <= 1 + extra_old[d] as int
                by {}
                assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && scores@[c] == scores@[d]
                    implies 1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1
                by {}
                assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && extra_old[c] >= 1
                    implies scores@[c] as int * (2 * extra_old[d] as int + 1)
                        >= scores@[d] as int * (2 * extra_old[c] as int - 1)
                by {}
                assert forall|c: int| 0 <= c < n
                    implies priority_ge(scores@, extra_old, best_g, c)
                by {}
            }
            extra.set(best, extra[best] + 1);
            proof {
                assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && scores@[c] < scores@[d]
                    implies 1 + extra@[c] as int <= 1 + extra@[d] as int
                by {
                    if c == best_g && d == best_g {
                        assert(false);
                    } else if c == best_g {
                        lemma_priority_strict(scores@, extra_old, best_g, d);
                    } else if d == best_g {
                        assert(1 + extra_old[c] as int <= 1 + extra_old[best_g] as int);
                    } else {
                        assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int);
                    }
                }
                assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && scores@[c] == scores@[d]
                    implies 1 + extra@[c] as int <= 1 + extra@[d] as int + 1
                by {
                    if c == best_g && d == best_g {
                        assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                    } else if c == best_g {
                        if scores@[best_g] > 0 {
                            lemma_priority_tie(scores@, extra_old, best_g, d);
                        } else {
                            assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                        }
                    } else if d == best_g {
                        assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                    } else {
                        assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                    }
                }
                // Preservation of the Webster no-transfer invariant.
                assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && extra@[c] >= 1
                    implies scores@[c] as int * (2 * extra@[d] as int + 1)
                        >= scores@[d] as int * (2 * extra@[c] as int - 1)
                by {
                    if c == best_g && d == best_g {
                        lemma_priority_lhs_monotone(scores@[best_g] as int,
                            extra@[best_g] as int - 1, extra@[best_g] as int);
                    } else if c == best_g {
                        // extra@[best] - 1 == extra_old[best]: the scan's exit
                        // fact at d is literally the needed inequality.
                        assert(priority_ge(scores@, extra_old, best_g, d));
                        assert(extra@[d] == extra_old[d]);
                        assert(extra@[best_g] as int == extra_old[best_g] as int + 1);
                    } else if d == best_g {
                        // The old invariant instance at (c, best) plus the left
                        // side growing with best's award.
                        assert(scores@[c] as int * (2 * extra_old[best_g] as int + 1)
                            >= scores@[best_g] as int * (2 * extra_old[c] as int - 1));
                        lemma_priority_lhs_monotone(scores@[c] as int,
                            extra_old[best_g] as int, extra@[best_g] as int);
                        assert(extra@[c] == extra_old[c]);
                    } else {
                        assert(scores@[c] as int * (2 * extra_old[d] as int + 1)
                            >= scores@[d] as int * (2 * extra_old[c] as int - 1));
                        assert(extra@[c] == extra_old[c] && extra@[d] == extra_old[d]);
                    }
                }
                let nv: u64 = (extra_old[best_g] + 1) as u64;
                lemma_sum_update(extra_old, best_g, nv, n as int);
            }
            awarded = awarded + 1;
        }

        proof {
            assert(sum_to(extra@, n as int) + n as int == weight_total as int) by {
                assert(sum_to(extra@, n as int) == pool as int);
            }
        }
        CompetitiveSelectionSoft { extra, scores, weight_total, max_score }
    }

    /// Award one further pool unit (TLA+ AssignNext, one step): re-establishes
    /// every invariant that holds at every reachable state (ScoreOrderPreservation,
    /// TieBoundedness, UniversalContribution); Normalization only holds once
    /// the pool is exhausted, matching the TLA+ construction exactly.
    pub fn assign_next(&mut self) -> (winner: usize)
        requires
            old(self).mutable_score_inv(),
            (sum_to(old(self).extra@, old(self).extra@.len() as int) + old(self).extra@.len() as int)
                < (old(self).weight_total as int),
        ensures
            winner < old(self).scores.len(),
            priority_winner(old(self).scores@, old(self).extra@, winner as int),
            final(self).scores@ == old(self).scores@,
            final(self).weight_total == old(self).weight_total,
            final(self).max_score == old(self).max_score,
            final(self).extra@
                == old(self).extra@.update(
                    winner as int,
                    (old(self).extra@[winner as int] + 1) as u64,
                ),
            final(self).mutable_score_inv(),
    {
        let n = self.scores.len();
        let wtot = self.weight_total;
        let _ = wtot;
        let mut best: usize = 0;
        let mut j: usize = 1;
        while j < n
            invariant
                1 <= j <= n,
                best < j,
                n == self.scores.len(),
                self.extra.len() == n,
                self.mutable_score_inv(),
                wtot <= 1_000_000_000,
                forall|k: int| 0 <= k < n ==> #[trigger] self.scores@[k] <= 1_000_000_000,
                forall|k: int| 0 <= k < n ==> #[trigger] self.extra@[k] <= wtot,
                forall|c: int| 0 <= c < j ==> priority_ge(self.scores@, self.extra@, best as int, c),
                forall|c: int| 0 <= c < j
                    && priority_equal(self.scores@, self.extra@, best as int, c)
                    ==> best as int <= c,
            decreases n - j,
        {
            proof {
                assert((self.scores@[j as int] as int) * (2 * (self.extra@[best as int] as int) + 1)
                    <= 1_000_000_000 * (2 * 1_000_000_000 + 1)) by (nonlinear_arith)
                    requires
                        self.scores@[j as int] as int <= 1_000_000_000,
                        self.extra@[best as int] as int <= 1_000_000_000;
                assert((self.scores@[best as int] as int) * (2 * (self.extra@[j as int] as int) + 1)
                    <= 1_000_000_000 * (2 * 1_000_000_000 + 1)) by (nonlinear_arith)
                    requires
                        self.scores@[best as int] as int <= 1_000_000_000,
                        self.extra@[j as int] as int <= 1_000_000_000;
            }
            let lhs: u128 = (self.scores[j] as u128) * (2 * (self.extra[best] as u128) + 1);
            let rhs: u128 = (self.scores[best] as u128) * (2 * (self.extra[j] as u128) + 1);
            proof {
                assert(lhs as int == self.scores@[j as int] as int * (2 * self.extra@[best as int] as int + 1));
                assert(rhs as int == self.scores@[best as int] as int * (2 * self.extra@[j as int] as int + 1));
            }
            let old_best: usize = best;
            let old_j: usize = j;
            let _ = (old_best, old_j);
            if lhs > rhs {
                best = j;
                proof {
                    assert(priority_ge(self.scores@, self.extra@, old_j as int, old_best as int));
                    assert(priority_gt(self.scores@, self.extra@, old_j as int, old_best as int));
                    assert forall|c: int| 0 <= c < old_j as int + 1
                        implies priority_ge(self.scores@, self.extra@, best as int, c)
                    by {
                        if c == old_best as int {
                            assert(priority_ge(self.scores@, self.extra@, old_j as int, old_best as int));
                        } else if c < old_j as int {
                            lemma_priority_ge_trans(self.scores@, self.extra@, old_j as int, old_best as int, c);
                        } else {
                            // c == old_j as int == best as int, reflexive
                        }
                    }
                    assert forall|c: int| 0 <= c < old_j as int + 1
                        && priority_equal(self.scores@, self.extra@, best as int, c)
                        implies best as int <= c
                    by {
                        if c < old_j as int {
                            lemma_priority_gt_ge_not_equal(
                                self.scores@, self.extra@,
                                old_j as int, old_best as int, c,
                            );
                            assert(false);
                        }
                    }
                }
            } else {
                proof {
                    assert(priority_ge(self.scores@, self.extra@, old_best as int, old_j as int));
                    assert forall|c: int| 0 <= c < old_j as int + 1
                        implies priority_ge(self.scores@, self.extra@, best as int, c)
                    by {
                        if c == old_j as int {
                            assert(priority_ge(self.scores@, self.extra@, old_best as int, old_j as int));
                        } else {
                            // c < old_j: unchanged from the pre-iteration invariant
                        }
                    }
                    assert forall|c: int| 0 <= c < old_j as int + 1
                        && priority_equal(self.scores@, self.extra@, best as int, c)
                        implies best as int <= c
                    by {
                        if c == old_j as int {
                            assert(best < old_j);
                        }
                    }
                }
            }
            j = j + 1;
        }
        let ghost extra_old: Seq<u64> = self.extra@;
        let ghost best_g: int = best as int;
        proof {
            assert(self.scores@ == old(self).scores@);
            assert(extra_old == old(self).extra@);
            assert(priority_winner(self.scores@, extra_old, best_g));
            assert(old(self).score_order_preservation());
            assert(old(self).tie_boundedness());
            assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && self.scores@[c] < self.scores@[d]
                implies 1 + extra_old[c] as int <= 1 + extra_old[d] as int
            by {
                assert(old(self).weight(c) <= old(self).weight(d));
            }
            assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && self.scores@[c] == self.scores@[d]
                implies 1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1
            by {
                assert(old(self).weight(c) <= old(self).weight(d) + 1);
            }
        }
        self.extra.set(best, self.extra[best] + 1);
        proof {
            assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && self.scores@[c] < self.scores@[d]
                implies 1 + self.extra@[c] as int <= 1 + self.extra@[d] as int
            by {
                if c == best_g && d == best_g {
                    assert(false);
                } else if c == best_g {
                    lemma_priority_strict(self.scores@, extra_old, best_g, d);
                } else if d == best_g {
                    assert(1 + extra_old[c] as int <= 1 + extra_old[best_g] as int);
                } else {
                    assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int);
                }
            }
            assert forall|c: int, d: int| 0 <= c < n && 0 <= d < n && self.scores@[c] == self.scores@[d]
                implies 1 + self.extra@[c] as int <= 1 + self.extra@[d] as int + 1
            by {
                if c == best_g && d == best_g {
                    assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                } else if c == best_g {
                    if self.scores@[best_g] > 0 {
                        lemma_priority_tie(self.scores@, extra_old, best_g, d);
                    } else {
                        assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                    }
                } else if d == best_g {
                    assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                } else {
                    assert(1 + extra_old[c] as int <= 1 + extra_old[d] as int + 1);
                }
            }
            let old_sum = sum_to(extra_old, n as int);
            lemma_sum_ge_one(extra_old, best_g, n as int);
            lemma_sum_update(extra_old, best_g, (extra_old[best_g] + 1) as u64, n as int);
            assert(sum_to(self.extra@, n as int) == old_sum + 1);
            assert(sum_to(self.extra@, n as int) + n as int <= self.weight_total as int);
            assert forall|k: int| 0 <= k < n
                implies self.extra@[k] <= self.weight_total by {
                if k == best_g {
                    assert(extra_old[k] <= old_sum);
                }
            }
            assert(self.normalization_when_terminal()) by {
                if self.terminal() {
                    assert(self.normalization());
                }
            }
            assert(self.mutable_score_inv());
        }
        best
    }

    /// CompetitiveSelectionSoftMutableScores `UpdateScore(c,v)`: update one mutable score
    /// and invalidate the partial apportionment in the same commit by resetting
    /// every extra award to the reserved floor.
    pub fn update_score(&mut self, c: usize, v: u64)
        requires
            old(self).mutable_score_inv(),
            c < old(self).scores.len(),
            1 <= v <= old(self).max_score,
        ensures
            final(self).weight_total == old(self).weight_total,
            final(self).max_score == old(self).max_score,
            final(self).scores@
                == old(self).scores@.update(c as int, v),
            final(self).extra@.len() == old(self).extra@.len(),
            forall|i: int| 0 <= i < final(self).extra.len() ==> final(self).extra@[i] == 0,
            final(self).mutable_score_inv(),
    {
        let ghost old_scores = self.scores@;
        self.scores.set(c, v);
        let ghost updated_scores = self.scores@;
        let n = self.extra.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.extra.len(),
                n == self.scores.len(),
                self.scores@ == updated_scores,
                updated_scores == old_scores.update(c as int, v),
                self.weight_total == old(self).weight_total,
                self.max_score == old(self).max_score,
                forall|k: int| 0 <= k < i ==> self.extra@[k] == 0,
                forall|k: int| i <= k < n ==> self.extra@[k] == old(self).extra@[k],
            decreases n - i,
        {
            self.extra.set(i, 0);
            i = i + 1;
        }
        proof {
            lemma_sum_zero(self.extra@, n as int);
            assert(self.score_bounds()) by {
                assert forall|k: int| 0 <= k < n implies
                    self.scores@[k] >= 1 && self.scores@[k] <= 1_000_000_000 by {
                    if k != c as int {
                        assert(self.scores@[k] == old(self).scores@[k]);
                    }
                }
            }
            assert(self.score_order_preservation()) by {
                assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n
                    && self.scores@[a] < self.scores@[b]
                    implies self.weight(a) <= self.weight(b) by {}
            }
            assert(self.tie_boundedness()) by {
                assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n
                    && self.scores@[a] == self.scores@[b]
                    implies self.weight(a) <= self.weight(b) + 1 by {}
            }
            assert(self.normalization_when_terminal()) by {
                if self.terminal() {
                    assert(self.normalization());
                }
            }
            assert(self.mutable_score_inv());
        }
    }
}

// ── Ranked mode: top-K selection ────────────────────────────────────────

/// Count of `true` entries among `s[0..n]`.
pub open spec fn count_true(s: Seq<bool>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else if n > s.len() as int { 0 }
    else { (if s[n - 1] { 1int } else { 0int }) + count_true(s, n - 1) }
}

/// Setting a `false` entry to `true` raises the count by one.
pub proof fn lemma_count_set(s: Seq<bool>, m: int, n: int)
    requires 0 <= m < n <= s.len(), !s[m],
    ensures count_true(s.update(m, true), n) == count_true(s, n) + 1,
    decreases n,
{
    if n == m + 1 {
        lemma_count_unaffected(s, m, n - 1);
    } else {
        lemma_count_set(s, m, n - 1);
    }
}

/// Updating index m does not change the count of a prefix stopping at or before m.
pub proof fn lemma_count_unaffected(s: Seq<bool>, m: int, p: int)
    requires 0 <= p <= m < s.len(),
    ensures count_true(s.update(m, true), p) == count_true(s, p),
    decreases p,
{
    if p > 0 {
        lemma_count_unaffected(s, m, p - 1);
    }
}

/// An all-false prefix has count zero.
pub proof fn lemma_count_zero(s: Seq<bool>, n: int)
    requires 0 <= n <= s.len(), forall|k: int| 0 <= k < n ==> !s[k],
    ensures count_true(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_count_zero(s, n - 1);
    }
}

/// An all-true prefix has count equal to its length.
pub proof fn lemma_count_all_true(s: Seq<bool>, n: int)
    requires 0 <= n <= s.len(), forall|k: int| 0 <= k < n ==> s[k],
    ensures count_true(s, n) == n,
    decreases n,
{
    if n > 0 {
        lemma_count_all_true(s, n - 1);
    }
}

/// A boolean prefix contains at most one true entry per position.
pub proof fn lemma_count_upper(s: Seq<bool>, n: int)
    requires 0 <= n <= s.len(),
    ensures count_true(s, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_upper(s, n - 1);
    }
}

/// Ranked competitive selection: pick the top-K candidates by score.
pub struct CompetitiveSelectionRanked {
    /// Candidate scores by candidate index.
    pub scores: Vec<u64>,
    /// Current selected membership by candidate index.
    pub selected: Vec<bool>,
    /// Maximum selected cardinality.
    pub k: usize,
    /// MaxScore for this refinement profile.
    pub max_score: u64,
}

impl CompetitiveSelectionRanked {
    /// selected and scores share the Candidates domain.
    pub open spec fn type_invariant(&self) -> bool {
        self.selected.len() == self.scores.len()
            && forall|i: int| 0 <= i < self.scores.len() ==>
                #[trigger] self.scores@[i] <= self.max_score
    }

    /// TLA+ `BoundedMultiplicity`: at most K winners.
    pub open spec fn bounded_multiplicity(&self) -> bool {
        count_true(self.selected@, self.selected@.len() as int) <= self.k
    }

    /// TLA+ `ThresholdOptimality`: every selected scores >= every non-selected.
    pub open spec fn threshold_optimality(&self) -> bool {
        forall|s: int, c: int|
            #![trigger self.selected@[s], self.selected@[c]]
            0 <= s < self.selected.len() && 0 <= c < self.selected.len()
                && self.selected@[s] && !self.selected@[c]
                ==> self.scores@[s] >= self.scores@[c]
    }

    /// TLA+ `RankedTieBreak`: every selected candidate is strictly better
    /// than every unselected candidate under score-then-lowest-index order.
    /// The vector index is the executable realization of the fixed WEnum/Pos
    /// order used by the formal model.
    pub open spec fn ranked_tie_break(&self) -> bool {
        forall|s: int, c: int|
            #![trigger self.selected@[s], self.selected@[c]]
            0 <= s < self.selected.len() && 0 <= c < self.selected.len()
                && self.selected@[s] && !self.selected@[c]
                ==> (self.scores@[s] > self.scores@[c]
                    || (self.scores@[s] == self.scores@[c] && s < c))
    }

    /// Whether all ranked-selection obligations hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.bounded_multiplicity()
            && self.threshold_optimality() && self.ranked_tie_break()
    }

    /// Construct from scores; nothing selected yet (TLA+ Init).
    pub fn new(scores: Vec<u64>, k: usize, max_score: u64) -> (r: CompetitiveSelectionRanked)
        requires
            forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores@[i] <= max_score,
        ensures
            r.scores@ == scores@,
            r.k == k,
            r.max_score == max_score,
            r.selected@.len() == scores@.len(),
            forall|j: int| 0 <= j < r.selected@.len() ==> !r.selected@[j],
            r.inv(),
    {
        let n = scores.len();
        let mut selected: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                selected.len() == i,
                forall|j: int| 0 <= j < i ==> !selected@[j],
            decreases n - i,
        {
            selected.push(false);
            i = i + 1;
        }
        proof { lemma_count_zero(selected@, selected@.len() as int); }
        CompetitiveSelectionRanked { scores, selected, k, max_score }
    }

    /// The unselected candidate with the highest score, or None if all selected.
    fn find_max_unselected(&self) -> (r: Option<usize>)
        requires self.type_invariant(),
        ensures
            r is None ==> (forall|c: int| 0 <= c < self.selected.len() ==> self.selected@[c]),
            r matches Option::Some(m) ==> (m < self.scores.len() && !self.selected@[m as int]
                && (forall|c: int| 0 <= c < self.scores.len() && !self.selected@[c]
                    ==> #[trigger] self.scores@[c] <= self.scores@[m as int])
                && (forall|c: int| 0 <= c < self.scores.len() && !self.selected@[c]
                    && #[trigger] self.scores@[c] == self.scores@[m as int]
                    ==> m as int <= c)),
    {
        let n = self.scores.len();
        let mut best: Option<usize> = None;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.scores.len(),
                self.selected.len() == n,
                best is None ==> (forall|c: int| 0 <= c < i ==> self.selected@[c]),
                best matches Option::Some(m) ==> (m < i && !self.selected@[m as int]
                    && (forall|c: int| 0 <= c < i && !self.selected@[c]
                        ==> #[trigger] self.scores@[c] <= self.scores@[m as int])
                    && (forall|c: int| 0 <= c < i && !self.selected@[c]
                        && #[trigger] self.scores@[c] == self.scores@[m as int]
                        ==> m as int <= c)),
            decreases n - i,
        {
            if !self.selected[i] {
                match best {
                    Option::Some(m) => {
                        if self.scores[i] > self.scores[m] {
                            best = Some(i);
                        }
                    }
                    Option::None => {
                        best = Some(i);
                    }
                }
            }
            i = i + 1;
        }
        best
    }

    /// Select the top-K (TLA+ Select): mark up to K highest-scoring candidates,
    /// re-establishing BoundedMultiplicity and ThresholdOptimality.
    pub fn select(&mut self)
        requires old(self).type_invariant(),
        ensures
            final(self).scores@ == old(self).scores@,
            final(self).k == old(self).k,
            final(self).max_score == old(self).max_score,
            count_true(final(self).selected@, final(self).selected@.len() as int)
                == if final(self).k < final(self).selected.len() {
                    final(self).k as int
                } else {
                    final(self).selected.len() as int
                },
            final(self).inv(),
    {
        let n = self.scores.len();
        let original_len = self.selected.len();
        let original_k = self.k;
        let _ = (original_len, original_k);
        assert(original_len == n);
        // Reset selection to empty.
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.scores.len(),
                self.selected.len() == n,
                self.type_invariant(),
                self.scores@ == old(self).scores@,
                self.k == old(self).k,
                self.max_score == old(self).max_score,
                original_len == n,
                original_k == self.k,
                forall|j: int| 0 <= j < i ==> !self.selected@[j],
            decreases n - i,
        {
            self.selected.set(i, false);
            i = i + 1;
        }
        proof { lemma_count_zero(self.selected@, n as int); }
        // Greedily mark the highest unselected, up to K rounds.
        let mut round: usize = 0;
        while round < self.k
            invariant
                n == self.scores.len(),
                self.selected.len() == n,
                self.type_invariant(),
                self.scores@ == old(self).scores@,
                self.k == old(self).k,
                self.max_score == old(self).max_score,
                original_len == n,
                original_k == self.k,
                round <= self.k,
                count_true(self.selected@, n as int) == round,
                self.threshold_optimality(),
                self.ranked_tie_break(),
            decreases self.k - round,
        {
            let m_opt = self.find_max_unselected();
            match m_opt {
                Option::Some(m) => {
                    let ghost s0 = self.selected@;
                    assert forall|c: int| 0 <= c < n && !s0[c]
                        implies self.scores@[c] <= self.scores@[m as int] by {}
                    assert forall|c: int| 0 <= c < n && !s0[c]
                        && self.scores@[c] == self.scores@[m as int]
                        implies m as int <= c by {}
                    proof { lemma_count_set(s0, m as int, n as int); }
                    self.selected.set(m, true);
                    proof {
                        assert(self.threshold_optimality()) by {
                            assert forall|s: int, c: int|
                                #![trigger self.selected@[s], self.selected@[c]]
                                0 <= s < n && 0 <= c < n && self.selected@[s] && !self.selected@[c]
                                implies self.scores@[s] >= self.scores@[c] by {
                                if s != m as int {
                                    assert(s0[s]);
                                }
                            }
                        }
                        assert(self.ranked_tie_break()) by {
                            assert forall|s: int, c: int|
                                #![trigger self.selected@[s], self.selected@[c]]
                                0 <= s < n && 0 <= c < n
                                    && self.selected@[s] && !self.selected@[c]
                                implies self.scores@[s] > self.scores@[c]
                                    || (self.scores@[s] == self.scores@[c] && s < c) by {
                                if s != m as int {
                                    assert(s0[s]);
                                    assert(!s0[c]);
                                } else {
                                    assert(!s0[c]);
                                    assert(c != m as int);
                                    if self.scores@[m as int] == self.scores@[c] {
                                        assert(m as int <= c);
                                        assert((m as int) < c);
                                    }
                                }
                            }
                        }
                    }
                }
                Option::None => {
                    proof {
                        lemma_count_all_true(self.selected@, n as int);
                        assert(count_true(self.selected@, n as int) == n as int);
                        assert(round as int == n as int);
                        assert(round < self.k);
                        assert(n < self.k);
                        assert(original_len == n);
                        assert(original_k == self.k);
                        assert(!(original_k < original_len));
                    }
                    return;
                }
            }
            round = round + 1;
        }
        proof {
            lemma_count_upper(self.selected@, n as int);
            assert(round == self.k);
            assert(count_true(self.selected@, n as int) == self.k as int);
            assert(self.k <= n);
        }
    }

    /// Replace the scores and clear the selection (TLA+ UpdateScores).
    pub fn update_scores(&mut self, new_scores: Vec<u64>)
        requires
            old(self).type_invariant(),
            new_scores.len() == old(self).scores.len(),
            forall|i: int| 0 <= i < new_scores.len() ==>
                #[trigger] new_scores@[i] <= old(self).max_score,
        ensures
            final(self).scores@ == new_scores@,
            final(self).k == old(self).k,
            final(self).max_score == old(self).max_score,
            forall|i: int| 0 <= i < final(self).selected.len() ==>
                !final(self).selected@[i],
            final(self).inv(),
    {
        let ghost ns = new_scores@;
        let n = new_scores.len();
        self.scores = new_scores;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.scores.len(),
                self.selected.len() == n,
                self.scores@ == ns,
                self.k == old(self).k,
                self.max_score == old(self).max_score,
                forall|j: int| 0 <= j < i ==> !self.selected@[j],
            decreases n - i,
        {
            self.selected.set(i, false);
            i = i + 1;
        }
        proof { lemma_count_zero(self.selected@, n as int); }
    }
}

}
