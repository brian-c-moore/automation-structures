// Executable carrier for Bisection.tla.
//
// Bisection maintains a candidate interval [lo, hi] over an ordered domain with a
// monotone boundary (the threshold) and halves the interval per probe. The TLA+
// spec is the lo/hi/probes machine and checks:
//
//   MonotonicityPreservation (INVARIANT) -- lo <= threshold <= hi
//   Halving (PROPERTY)        -- per-probe contraction: hi' - lo' <= (hi - lo) / 2
//   ProbeBound (INVARIANT)    -- probes_taken <= MaxProbes, with
//                                EventualConvergence (<>(hi - lo < 2)) the liveness companion.
//
//   - `Bisection { domain_size, max_probes, lo, hi, threshold, probes_taken }`
//     mirrors the TLA+ constants and variables. The counter is executable so
//     the budget boundary is observable rather than only a ghost assertion.
//   - `monotonicity()` is the MonotonicityPreservation invariant.
//   - `probe()` is the TLA+ ProbeLeft/ProbeRight action — one atomic step that
//     maintains monotonicity and ensures hi'-lo' <= (hi-lo)/2.
//   - `bisect()` drives probe() to convergence; `decreases hi - lo` is the
//     loop-termination witness.
//   - `bisection_find()` is a binary-search realization: the search-level view.
//
// Monotonicity, halving, and the termination measure do not
// determine the post-state selected by ProbeLeft/ProbeRight. `probe` therefore
// also ensures the specified midpoint endpoint update and frames the other
// endpoint; this action correspondence is stronger than the checked invariants.

use vstd::prelude::*;

verus! {

// Local power-of-two definition used by the probe-budget proof. It is local to
// this module so the bound does not depend on another carrier's specification.
pub open spec fn pow2(k: u64) -> int
    decreases k,
{
    if k == 0 { 1 } else { 2 * pow2((k - 1) as u64) }
}

pub proof fn lemma_pow2_positive(k: u64)
    ensures pow2(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_positive((k - 1) as u64);
    }
}

pub proof fn lemma_pow2_step(k: u64)
    requires k > 0,
    ensures pow2(k) == 2 * pow2((k - 1) as u64),
{
}

// ── The Bisection machine (TLA+ Bisection.tla: lo/hi/probes) ──────────────

pub struct Bisection {
    pub domain_size: u64,
    pub max_probes: u64,
    pub lo: u64,
    pub hi: u64,
    pub threshold: u64,
    pub probes_taken: u64,
}

impl Bisection {
    /// TLA+ constant assumptions and TypeInvariant, including the finite
    /// ordered-domain bounds represented by executable u64 values.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.domain_size >= 2
        &&& 1 <= self.threshold < self.domain_size
        &&& self.lo <= self.hi
        &&& self.hi <= self.domain_size
    }

    /// TLA+ MonotonicityPreservation: the threshold always lies in [lo, hi].
    pub open spec fn monotonicity(&self) -> bool {
        self.lo <= self.threshold && self.threshold <= self.hi
    }

    /// TLA+ DomainFitsProbes constant assumption.
    pub open spec fn domain_fits_probes(&self) -> bool {
        self.domain_size as int <= pow2(self.max_probes)
    }

    /// TLA+ ProbeBound safety invariant.
    pub open spec fn probe_bound(&self) -> bool {
        self.probes_taken <= self.max_probes
    }

    /// The TLAPS proof's exact inductive strengthening. ProbeBound alone is
    /// not inductive at the budget edge; this relates the remaining width to
    /// the remaining power-of-two probe capacity.
    pub open spec fn width_exp_bound(&self) -> bool {
        &&& self.probe_bound()
        &&& self.hi as int - self.lo as int
            <= pow2((self.max_probes - self.probes_taken) as u64)
    }

    pub open spec fn invariant(&self) -> bool {
        &&& self.type_invariant()
        &&& self.monotonicity()
        &&& self.domain_fits_probes()
        &&& self.width_exp_bound()
    }

    /// The probe point: the TLA+ `Mid == (lo + hi) \div 2`, written in the
    /// overflow-avoiding form the executable uses. The two are equal for
    /// lo <= hi; the form here exists only so the sum cannot overflow u64.
    pub open spec fn mid(&self) -> int {
        self.lo as int + (self.hi as int - self.lo as int) / 2
    }

    /// Init (TLA+ Init): a candidate interval straddling the threshold, no
    /// probes taken yet.
    pub fn new(
        lo: u64,
        hi: u64,
        threshold: u64,
        domain_size: u64,
        max_probes: u64,
    ) -> (b: Bisection)
        requires
            domain_size >= 2,
            1 <= threshold < domain_size,
            lo <= threshold,
            threshold <= hi,
            hi <= domain_size,
            domain_size as int <= pow2(max_probes),
        ensures
            b.domain_size == domain_size,
            b.max_probes == max_probes,
            b.lo == lo,
            b.hi == hi,
            b.threshold == threshold,
            b.probes_taken == 0,
            b.invariant(),
    {
        proof {
            lemma_pow2_positive(max_probes);
            assert(hi as int - lo as int <= domain_size as int);
        }
        Bisection {
            domain_size,
            max_probes,
            lo,
            hi,
            threshold,
            probes_taken: 0,
        }
    }

    /// Whether the interval has been narrowed to a point (TLA+ Converged guard).
    pub fn converged(&self) -> (c: bool)
        requires
            self.invariant(),
        ensures
            c == (self.hi - self.lo < 2),
    {
        self.hi - self.lo < 2
    }

    /// Probe the midpoint and narrow the interval -- one atomic step (TLA+
    /// ProbeLeft / ProbeRight). Maintains MonotonicityPreservation, at least
    /// halves the interval (the Halving property), and strictly decreases its
    /// width (the loop-termination measure).
    pub fn probe(&mut self)
        requires
            old(self).hi - old(self).lo >= 2,
            old(self).invariant(),
        ensures
            final(self).invariant(),
            // Halving: the probe at least halves the interval.
            final(self).hi - final(self).lo <= (old(self).hi - old(self).lo) / 2,
            // Loop-termination measure: the width strictly decreases.
            final(self).hi - final(self).lo < old(self).hi - old(self).lo,
            final(self).domain_size == old(self).domain_size,
            final(self).max_probes == old(self).max_probes,
            final(self).threshold == old(self).threshold,
            crate::connectives::cursor::cursor_admitted(
                old(self).lo as nat,
                final(self).lo as nat,
            ),
            final(self).probes_taken == old(self).probes_taken + 1,
            // The probe lands on the midpoint and frames the endpoint
            // that does not move. The five clauses above are properties of the
            // post-state interval's width and position -- including all three
            // that Bisection.cfg checks -- and they do NOT pin the interval: the
            // spec's ProbeLeft/ProbeRight are deterministic, and without this
            // clause the contract admits post-states that are not steps of the
            // spec. It does not state which side is taken because monotonicity
            // already decides that branch.
            (final(self).hi as int == old(self).mid() && final(self).lo == old(self).lo)
                || (final(self).lo as int == old(self).mid() + 1
                        && final(self).hi == old(self).hi),
    {
        let old_lo = self.lo;
        let old_hi = self.hi;
        let old_width = self.hi - self.lo;
        let old_probes = self.probes_taken;
        let remaining = self.max_probes - self.probes_taken;
        let _ = (old_lo, old_hi, old_width, remaining);
        proof {
            if self.probes_taken == self.max_probes {
                assert(remaining == 0);
                assert(pow2(remaining) == 1);
                assert(self.hi as int - self.lo as int <= 1);
                assert(false);
            }
            assert(self.probes_taken < self.max_probes);
            assert(remaining > 0);
            lemma_pow2_step(remaining);
            lemma_pow2_positive((remaining - 1) as u64);
        }
        let mid = self.lo + (self.hi - self.lo) / 2;
        if mid >= self.threshold {
            // P(mid) = FALSE: threshold in [lo, mid] -> hi' = mid
            self.hi = mid;
        } else {
            // P(mid) = TRUE: threshold in [mid+1, hi] -> lo' = mid + 1
            self.lo = mid + 1;
        }
        self.probes_taken = old_probes + 1;
        proof {
            assert(self.hi - self.lo <= old_width / 2);
            assert(old_width as int <= pow2(remaining));
            assert(old_width as int / 2 <= pow2((remaining - 1) as u64));
            assert(self.hi as int - self.lo as int <= old_width as int / 2);
            assert(self.max_probes - self.probes_taken == remaining - 1);
            assert(self.hi as int - self.lo as int
                <= pow2((self.max_probes - self.probes_taken) as u64));
            assert(old_lo <= old_hi);
        }
    }

    /// Drive probes to convergence (the TLA+ EventualConvergence under fairness).
    /// The `decreases hi - lo` is the loop-termination witness: the loop
    /// halts, and on exit the interval is a point (hi - lo < 2) that still
    /// straddles the threshold.
    pub fn bisect(&mut self)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).hi - final(self).lo < 2,
            final(self).domain_size == old(self).domain_size,
            final(self).max_probes == old(self).max_probes,
            final(self).threshold == old(self).threshold,
    {
        while self.hi - self.lo >= 2
            invariant
                self.invariant(),
                self.domain_size == old(self).domain_size,
                self.max_probes == old(self).max_probes,
                self.threshold == old(self).threshold,
            decreases self.hi - self.lo,
        {
            self.probe();
        }
    }
}

// ── Applied realization: binary search (a Bisection instance) ─────────────

/// A slice is sorted (non-strictly ascending) over its index range.
pub open spec fn is_sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

/// Binary search: the search-level view of Bisection -- halve [lo, hi) until the
/// target index is found, or return `sorted.len()` if absent. The interval
/// invariants are carried by the `Bisection` machine above. `decreases hi - lo`
/// states that each probe strictly shrinks the interval.
pub fn bisection_find(sorted: &[u64], target: u64) -> (idx: usize)
    requires
        is_sorted(sorted@),
    ensures
        idx as int <= sorted@.len() as int,
        idx < sorted@.len() ==> sorted@[idx as int] == target,
{
    let n: usize = sorted.len();
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant
            lo <= hi,
            hi <= n,
            n == sorted@.len(),
            is_sorted(sorted@),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let mid_val = sorted[mid];
        if mid_val == target {
            return mid;
        } else if mid_val < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    n  // not present
}

}
