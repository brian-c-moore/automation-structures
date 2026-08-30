// Executable witness for formal/composition/structure-compositions/SelectThenActuate.tla.
//
// Seats and candidates are half-open index ranges. allocation uses Some(c) for
// a candidate and None for NULL, making the sentinel disjoint from candidates.
// Evaluate assigns the lowest-index argmax. UpdateScore changes one score,
// invalidates that seat's allocation, and retracts its actuation in one method.
// Actuate requires a non-NULL allocation and leaves allocation and scores
// unchanged. These transitions preserve WinnerOptimality and ActuationScope.
//
// This is a sequential witness: each TLA+ action is one &mut self method. A
// concurrent implementation must provide an equivalent atomic boundary.

use vstd::prelude::*;

verus! {

/// A per-seat select-then-actuate machine over a seat universe `[0, num_seats)`
/// and a candidate universe `[0, num_candidates)`: each seat holds an argmax
/// allocation (Some(candidate) or None=NULL), per-candidate scores, and an
/// actuated flag. The merged actions enforce the coupling: an allocation is
/// invalidated when its scores change, and actuation is confined to allocated
/// seats.
pub struct SelectThenActuate {
    /// |Seats|: the seat universe is the index range `[0, num_seats)`.
    pub num_seats: usize,
    /// |Candidates|: the candidate universe is `[0, num_candidates)`.
    pub num_candidates: usize,
    /// allocation ∈ [Seats -> Candidates ∪ {NULL}]: Some(c) is the winning
    /// candidate index, None is NULL.
    pub allocation: Vec<Option<u64>>,
    /// scores ∈ [Seats -> [Candidates -> Nat]]: per-seat, per-candidate scores.
    pub scores: Vec<Vec<u64>>,
    /// actuated ⊆ Seats as a seat-indexed bitvec.
    pub actuated: Vec<bool>,
}

impl SelectThenActuate {
    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ TypeInvariant: allocation ∈ [Seats -> Candidates ∪ {NULL}] (every
    /// entry is a candidate index or NULL), scores ∈ [Seats -> [Candidates ->
    /// Nat]] (every row spans the candidate universe), actuated ⊆ Seats. Plus
    /// the CandidatesNonEmpty constants clause num_candidates >= 1 (header note).
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.num_candidates >= 1
        &&& self.allocation.len() == self.num_seats
        &&& self.scores.len() == self.num_seats
        &&& self.actuated.len() == self.num_seats
        &&& (forall|s: int|
            0 <= s < self.num_seats ==> (#[trigger] self.scores@[s]).len() == self.num_candidates)
        &&& (forall|s: int|
            #![trigger self.allocation@[s]]
            0 <= s < self.num_seats ==> (self.allocation@[s] matches Some(w) ==> (w as int)
                < self.num_candidates as int))
    }

    /// TLA+ `ActuationScope == \A s ∈ actuated : allocation[s] /= NULL`:
    /// every actuated seat holds a (non-NULL) allocation.
    pub open spec fn actuation_scope(&self) -> bool {
        forall|s: int|
            0 <= s < self.actuated.len() ==> (#[trigger] self.actuated@[s]
                ==> self.allocation@[s] is Some)
    }

    /// TLA+ `WinnerOptimality`: a non-NULL allocation is an argmax — the
    /// winner scores at least as high as every candidate for that seat.
    pub open spec fn winner_optimality(&self) -> bool {
        forall|s: int|
            #![trigger self.allocation@[s]]
            0 <= s < self.num_seats ==> (self.allocation@[s] matches Some(w) ==> forall|c: int|
                #![trigger self.scores@[s]@[c]]
                0 <= c < self.num_candidates as int ==> self.scores@[s]@[c]
                    <= self.scores@[s]@[w as int])
    }

    /// The tie conjunct of `Evaluate`'s CHOOSE at one seat: among the
    /// candidates tied with the seat's winner on score, the winner has the
    /// lowest index. Per-seat because it is ACTION content -- `evaluate(s)`
    /// establishes it at the seat it evaluates and touches no other seat.
    pub open spec fn winner_tie_break_at(&self, s: int) -> bool {
        self.allocation@[s] matches Some(w) ==> forall|c: int|
            #![trigger self.scores@[s]@[c]]
            0 <= c < self.num_candidates as int ==> (self.scores@[s]@[c]
                == self.scores@[s]@[w as int] ==> w as int <= c)
    }

    /// TLA+ `CompositionInvariant == ActuationScope /\ WinnerOptimality`.
    pub open spec fn composition_invariant(&self) -> bool {
        self.actuation_scope() && self.winner_optimality()
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the initial state: every allocation NULL, every score 0,
    /// nothing actuated. Realises the TLA+ `Init` predicate and establishes all
    /// four invariants (ActuationScope and WinnerOptimality hold vacuously since
    /// every allocation is None).
    pub fn new(num_seats: usize, num_candidates: usize) -> (r: SelectThenActuate)
        requires
            num_candidates >= 1,   // CandidatesNonEmpty (header note)
        ensures
            r.num_seats == num_seats,
            r.num_candidates == num_candidates,
            r.allocation.len() == num_seats,
            r.scores.len() == num_seats,
            r.actuated.len() == num_seats,
            forall|i: int| 0 <= i < num_seats ==> r.allocation@[i] is None,
            forall|i: int| 0 <= i < num_seats ==> r.actuated@[i] == false,
            forall|i: int| 0 <= i < num_seats ==> (#[trigger] r.scores@[i]).len() == num_candidates,
            forall|i: int, j: int|
                0 <= i < num_seats && 0 <= j < num_candidates
                    ==> #[trigger] r.scores@[i]@[j] == 0,
            r.type_invariant(),
            r.actuation_scope(),
            r.winner_optimality(),
            r.composition_invariant(),
    {
        let mut allocation: Vec<Option<u64>> = Vec::new();
        let mut scores: Vec<Vec<u64>> = Vec::new();
        let mut actuated: Vec<bool> = Vec::new();
        let mut s: usize = 0;
        while s < num_seats
            invariant
                s <= num_seats,
                allocation.len() == s,
                scores.len() == s,
                actuated.len() == s,
                forall|i: int| 0 <= i < s ==> allocation@[i] is None,
                forall|i: int| 0 <= i < s ==> actuated@[i] == false,
                forall|i: int| 0 <= i < s ==> (#[trigger] scores@[i]).len() == num_candidates,
                forall|i: int, j: int|
                    0 <= i < s && 0 <= j < num_candidates ==> #[trigger] scores@[i]@[j] == 0,
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
            actuated.push(false);
            s = s + 1;
        }
        SelectThenActuate { num_seats, num_candidates, allocation, scores, actuated }
    }

    // ── Executable accessors ────────────────────────────────────────────

    /// Executable read of `scores[s][c]`.
    pub fn score_at(&self, s: usize, c: usize) -> (r: u64)
        requires
            s < self.scores.len(),
            c < self.scores@[s as int].len(),
        ensures
            r == self.scores@[s as int]@[c as int],
    {
        self.scores[s][c]
    }

    /// Executable test of the `allocation[s] /= NULL` guard.
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

    /// Executable test of the `s ∈ actuated` guard.
    pub fn is_actuated(&self, s: usize) -> (b: bool)
        requires
            s < self.actuated.len(),
        ensures
            b == self.actuated@[s as int],
    {
        self.actuated[s]
    }

    // ── Evaluate (TLA+ Evaluate) ────────────────────────────────────────

    /// Evaluate seat `s`: set its allocation to the argmax candidate over that
    /// seat's scores; scores and actuated UNCHANGED. Realises the TLA+
    /// `Evaluate(s)` action. The selected winner is always a candidate
    /// (Some, never None) — the NullNotCandidate fact, structural in the Option
    /// representation — so ActuationScope is preserved even when `s` is already
    /// actuated; WinnerOptimality is re-established for `s` from the argmax scan.
    pub fn evaluate(&mut self, s: usize)
        requires
            old(self).type_invariant(),
            old(self).actuation_scope(),
            old(self).winner_optimality(),
            s < old(self).num_seats,
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).num_candidates == old(self).num_candidates,
            final(self).scores@ == old(self).scores@,      // UNCHANGED scores
            final(self).actuated@ == old(self).actuated@,  // UNCHANGED actuated
            final(self).allocation.len() == old(self).allocation.len(),
            forall|t: int|
                0 <= t < final(self).num_seats && t != s as int
                    ==> final(self).allocation@[t] == old(self).allocation@[t],
            final(self).allocation@[s as int] is Some,     // a candidate, never NULL (NullNotCandidate)
            final(self).type_invariant(),
            final(self).actuation_scope(),
            final(self).winner_optimality(),
            final(self).winner_tie_break_at(s as int),
            final(self).composition_invariant(),
    {
        let n = self.scores[s].len();
        let mut best: usize = 0;
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                best < i,
                s < self.num_seats,
                self.scores.len() == self.num_seats,
                n == self.num_candidates,
                self.scores@[s as int].len() == self.num_candidates,
                forall|c: int|
                    0 <= c < i as int ==> #[trigger] self.scores@[s as int]@[c]
                        <= self.scores@[s as int]@[best as int],
                // Tie-break preservation: among the candidates seen so far that
                // tie with `best`, `best` has the lowest index. Maintained by the
                // strict `>` in the body: a `>=` would take the later index.
                forall|c: int|
                    0 <= c < i as int ==> (#[trigger] self.scores@[s as int]@[c]
                        == self.scores@[s as int]@[best as int] ==> best as int <= c),
                self.scores@ == old(self).scores@,
                self.allocation@ == old(self).allocation@,
                self.actuated@ == old(self).actuated@,
                self.num_seats == old(self).num_seats,
                self.num_candidates == old(self).num_candidates,
            decreases n - i,
        {
            let vi = self.score_at(s, i);
            let vb = self.score_at(s, best);
            if vi > vb {
                best = i;
            }
            i = i + 1;
        }
        // Argmax established for seat s over the whole candidate universe.
        assert(forall|c: int|
            0 <= c < self.num_candidates as int ==> #[trigger] self.scores@[s as int]@[c]
                <= self.scores@[s as int]@[best as int]);
        // Tie-break established for seat s over the whole candidate universe.
        assert(forall|c: int|
            0 <= c < self.num_candidates as int ==> (#[trigger] self.scores@[s as int]@[c]
                == self.scores@[s as int]@[best as int] ==> best as int <= c));
        assert((best as u64) as int == best as int);
        self.allocation.set(s, Some(best as u64));
        // Re-establish TypeInvariant: allocation@[s] = Some(best), best < num_candidates.
        assert(self.type_invariant()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==> (w as int)
                    < self.num_candidates as int) by {
                if t != s as int {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                }
            }
        }
        // Re-establish ActuationScope: allocation@[s] is now Some (regardless of
        // whether s is actuated); every other seat is unchanged.
        assert(self.actuation_scope()) by {
            assert forall|t: int| 0 <= t < self.actuated.len() && self.actuated@[t]
                implies self.allocation@[t] is Some by {
                if t != s as int {
                    assert(self.actuated@[t] == old(self).actuated@[t]);
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                }
            }
        }
        // Re-establish WinnerOptimality: seat s from the argmax scan (winner
        // best), every other seat from the unchanged old invariant.
        assert(self.winner_optimality()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==> forall|c: int|
                    0 <= c < self.num_candidates as int ==> self.scores@[t]@[c]
                        <= self.scores@[t]@[w as int]) by {
                if t == s as int {
                    assert(self.allocation@[t] == Some(best as u64));
                    assert(self.scores@[t]@ == self.scores@[s as int]@);
                } else {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                    assert(self.scores@[t]@ == old(self).scores@[t]@);
                }
            }
        }
        // Establish the tie-break at seat s: the winner is Some(best), and
        // the post-loop tie assertion is exactly best's property at this seat.
        assert(self.winner_tie_break_at(s as int)) by {
            assert(self.allocation@[s as int] == Some(best as u64));
        }
    }

    // ── UpdateScore (TLA+ UpdateScore) — the interaction step ────────────

    /// Update `scores[s][c] = v`, and in the SAME step invalidate the seat's
    /// allocation (to NULL) and drop it from `actuated`. Realises the TLA+
    /// `UpdateScore(s,c,v)` action — the composition's interaction step, all
    /// three updates fused in one method. Nulling the allocation keeps
    /// WinnerOptimality (a stale winner can never survive a score change);
    /// retracting `actuated` in the same step keeps ActuationScope (the seat's
    /// allocation just went NULL, so it must not remain actuated).
    pub fn update_score(&mut self, s: usize, c: usize, v: u64)
        requires
            old(self).type_invariant(),
            old(self).actuation_scope(),
            old(self).winner_optimality(),
            s < old(self).num_seats,
            c < old(self).num_candidates,
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).num_candidates == old(self).num_candidates,
            // allocation' = [allocation EXCEPT ![s] = NULL]
            final(self).allocation@ == old(self).allocation@.update(s as int, None),
            final(self).allocation@[s as int] is None,
            // actuated' = actuated \ {s}
            final(self).actuated@ == old(self).actuated@.update(s as int, false),
            final(self).actuated@[s as int] == false,
            // scores' = [scores EXCEPT ![s][c] = v]
            final(self).scores.len() == old(self).scores.len(),
            forall|t: int|
                0 <= t < final(self).num_seats && t != s as int
                    ==> final(self).scores@[t]@ == old(self).scores@[t]@,
            final(self).scores@[s as int]@ == old(self).scores@[s as int]@.update(c as int, v),
            forall|t: int|
                0 <= t < final(self).num_seats ==> (#[trigger] final(self).scores@[t]).len()
                    == final(self).num_candidates,
            final(self).type_invariant(),
            final(self).actuation_scope(),
            final(self).winner_optimality(),
            final(self).composition_invariant(),
    {
        // scores[s][c] = v via rebuild-of-row (vstd Vec has no nested set):
        // build new_row = old row with index c set to v, then one outer set.
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
                forall|j: int|
                    0 <= j < k as int ==> new_row@[j] == (if j == c as int { v } else { old_row[j] }),
                self.scores@ == old(self).scores@,
                self.allocation@ == old(self).allocation@,
                self.actuated@ == old(self).actuated@,
                self.num_seats == old(self).num_seats,
                self.num_candidates == old(self).num_candidates,
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
            assert forall|j: int| 0 <= j < new_row.len() implies new_row@[j] == old_row.update(
                c as int,
                v,
            )[j] by {
                if j == c as int {
                } else {
                }
            }
        }
        self.scores.set(s, new_row);
        self.allocation.set(s, None);
        self.actuated.set(s, false);
        // Re-establish TypeInvariant.
        assert(self.type_invariant()) by {
            assert forall|t: int|
                0 <= t < self.num_seats implies (#[trigger] self.scores@[t]).len()
                    == self.num_candidates by {
                if t != s as int {
                    assert(self.scores@[t] == old(self).scores@[t]);
                }
            }
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==> (w as int)
                    < self.num_candidates as int) by {
                if t != s as int {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                }
            }
        }
        // Re-establish ActuationScope — the interaction step: actuated@[s] is
        // now false so s drops out; for t != s both actuated@[t] and
        // allocation@[t] are unchanged, so the old invariant carries.
        assert(self.actuation_scope()) by {
            assert forall|t: int| 0 <= t < self.actuated.len() && self.actuated@[t]
                implies self.allocation@[t] is Some by {
                if t != s as int {
                    assert(self.actuated@[t] == old(self).actuated@[t]);
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                }
            }
        }
        // Re-establish WinnerOptimality: seat s has allocation None (vacuous);
        // for t != s allocation and scores are unchanged, so the old invariant
        // carries — the score change at s cannot break any seat's winner.
        assert(self.winner_optimality()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==> forall|cc: int|
                    0 <= cc < self.num_candidates as int ==> self.scores@[t]@[cc]
                        <= self.scores@[t]@[w as int]) by {
                if t != s as int {
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                    assert(self.scores@[t]@ == old(self).scores@[t]@);
                }
            }
        }
    }

    // ── Actuate (TLA+ Actuate) ──────────────────────────────────────────

    /// Actuate seat `s`. Realises the TLA+ `Actuate(s)` action: its two guards
    /// (`allocation[s] /= NULL`, `s` not in `actuated`) are `requires`; `actuated'` =
    /// actuated ∪ {s}; allocation and scores UNCHANGED. ActuationScope is
    /// re-established (s now actuated but its allocation is Some, unchanged);
    /// WinnerOptimality is untouched (it reads only allocation and scores).
    pub fn actuate(&mut self, s: usize)
        requires
            old(self).type_invariant(),
            old(self).actuation_scope(),
            old(self).winner_optimality(),
            s < old(self).num_seats,
            old(self).allocation@[s as int] is Some,   // allocation[s] /= NULL
            !old(self).actuated@[s as int],             // s ∉ actuated
        ensures
            final(self).num_seats == old(self).num_seats,
            final(self).num_candidates == old(self).num_candidates,
            final(self).allocation@ == old(self).allocation@,   // UNCHANGED
            final(self).scores@ == old(self).scores@,           // UNCHANGED
            final(self).actuated@ == old(self).actuated@.update(s as int, true),
            final(self).actuated@[s as int] == true,
            final(self).type_invariant(),
            final(self).actuation_scope(),
            final(self).winner_optimality(),
            final(self).composition_invariant(),
    {
        self.actuated.set(s, true);
        // Re-establish ActuationScope: seat s now actuated but allocation[s] is
        // Some (precondition, allocation unchanged); every other seat unchanged.
        assert(self.actuation_scope()) by {
            assert forall|t: int| 0 <= t < self.actuated.len() && self.actuated@[t]
                implies self.allocation@[t] is Some by {
                if t == s as int {
                    assert(self.allocation@[t] is Some);
                } else {
                    assert(self.actuated@[t] == old(self).actuated@[t]);
                    assert(self.allocation@[t] == old(self).allocation@[t]);
                }
            }
        }
        // WinnerOptimality: allocation and scores are unchanged, so the old
        // invariant carries verbatim.
        assert(self.winner_optimality()) by {
            assert forall|t: int|
                #![trigger self.allocation@[t]]
                0 <= t < self.num_seats implies (self.allocation@[t] matches Some(w) ==> forall|cc: int|
                    0 <= cc < self.num_candidates as int ==> self.scores@[t]@[cc]
                        <= self.scores@[t]@[w as int]) by {
                assert(self.allocation@[t] == old(self).allocation@[t]);
                assert(self.scores@[t]@ == old(self).scores@[t]@);
            }
        }
    }
}

}
