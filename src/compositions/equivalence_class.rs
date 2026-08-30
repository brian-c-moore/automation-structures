// EquivalenceClass executable correspondence boundary.
//
// EquivalenceClass is a union-find structure with union-by-rank. The TLA+ spec
// at formal/structures/EquivalenceClass/EquivalenceClass.tla has state parent (Elements -> Elements),
// rnk (Elements -> Nat), ops_done, with Rep(e) the root of e under parent, and
// states six safety formulas:
//
//   TypeInvariant     — parent : Elements->Elements, rnk : Elements->Nat
//   RepresentativeIdempotence — Rep(e) = Rep(Rep(e))
//   Symmetry          — Rep(a)=Rep(b) => Rep(b)=Rep(a)
//   Transitivity      — Rep(a)=Rep(b) /\ Rep(b)=Rep(c) => Rep(a)=Rep(c)
//   RankMonotonicity  — parent[e] /= e => rnk[e] <= rnk[parent[e]]
//   RepresentativeRootedness  — parent[Rep(e)] = Rep(e)
//
// The TLC configuration checks type safety and the three structural formulas.
// Symmetry and Transitivity are properties of `=` and hold for any Rep.
// RepresentativeIdempotence and RepresentativeRootedness need Rep(e) to be a root; RankMonotonicity is
// the local rank constraint. `rep` (the root finder) terminates: the
// recursion measure is `max_rank - rank[e]`, justified by the union-by-rank
// strengthening rank[e] < rank[parent[e]] for non-roots (STRICT — the .cfg's
// RankMonotonicity is the non-strict weakening). All six follow from a single
// maintained invariant `inv`; the equality properties require no executable
// state preservation beyond a well-defined representative.
//
// To keep the rank counter overflow-free, this module carries the standard
// union-by-rank size bound: subtree sizes with `2^rank[e] <= size[e]` and a
// partition invariant `sum of root sizes == n`. Together they give `2^rank <= n`,
// so every rank is <= 63 for any usize-sized element set, and the equal-rank
// increment never overflows (and the doubling `2^(r+1) <= size[ra]+size[rb]`
// re-establishes the size bound).
//
// Elements is the index universe 0..n; Rep follows TLA+ semantics (no path
// compression in the spec).

use vstd::prelude::*;

verus! {

// ── pow2 and the rank bound ─────────────────────────────────────────────

/// 2^k, lifted to int.
pub open spec fn pow2(k: u64) -> int
    decreases k,
{
    if k == 0 { 1 } else { 2 * pow2((k - 1) as u64) }
}

/// pow2 is monotone non-decreasing.
pub proof fn lemma_pow2_mono(a: u64, b: u64)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a < b {
        lemma_pow2_mono(a, (b - 1) as u64);
        lemma_pow2_pos((b - 1) as u64);
    }
}

/// pow2 is positive.
pub proof fn lemma_pow2_pos(k: u64)
    ensures pow2(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos((k - 1) as u64);
    }
}

/// 2^64 exceeds u64::MAX, which is what bounds ranks below 64.
pub proof fn lemma_pow2_64_huge()
    ensures pow2(64) > u64::MAX as int,
{
    assert(pow2(64) == 0x1_0000_0000_0000_0000) by (compute_only);
}

/// If 2^rank <= n <= u64::MAX, then rank <= 63.
pub proof fn lemma_rank_le_63(rank: u64, n: int)
    requires
        pow2(rank) <= n,
        n <= u64::MAX as int,
    ensures rank <= 63,
{
    lemma_pow2_64_huge();
    if rank >= 64 {
        lemma_pow2_mono(64, rank);
    }
}

// ── Rep: the root finder (TLA+ Rep) ─────────────────────────────────────

/// The representative (root) of `e` under `parent`. Terminates because each
/// hop to `parent[e]` strictly raises the rank (toward `mr`), so `mr - rank[e]`
/// strictly decreases. Defensive outside the valid/strict region.
pub open spec fn rep(parent: Seq<usize>, rank: Seq<u64>, mr: u64, e: int) -> int
    decreases mr - rank[e],
{
    if !(0 <= e < parent.len()) {
        e
    } else if parent[e] == e {
        e
    } else if rank[e] < rank[parent[e] as int] && rank[parent[e] as int] <= mr {
        rep(parent, rank, mr, parent[e] as int)
    } else {
        e
    }
}

/// Under the structural invariant, `rep(e)` is a valid root: in range and a
/// fixed point of `parent`.
pub proof fn lemma_rep_root(parent: Seq<usize>, rank: Seq<u64>, mr: u64, e: int)
    requires
        rank.len() == parent.len(),
        0 <= e < parent.len(),
        forall|x: int| 0 <= x < parent.len() ==> #[trigger] parent[x] < parent.len(),
        forall|x: int| 0 <= x < parent.len() ==> rank[x] <= mr,
        forall|x: int|
            0 <= x < parent.len() && parent[x] != x ==> #[trigger] rank[x] < rank[parent[x] as int],
    ensures
        0 <= rep(parent, rank, mr, e) < parent.len(),
        parent[rep(parent, rank, mr, e) as int] == rep(parent, rank, mr, e),
    decreases mr - rank[e],
{
    if parent[e] == e {
    } else {
        lemma_rep_root(parent, rank, mr, parent[e] as int);
    }
}

/// Under the structural invariant, following one parent pointer preserves the
/// representative: rep(e) = rep(parent[e]). Used by the iterative `find`.
pub proof fn lemma_rep_step(parent: Seq<usize>, rank: Seq<u64>, mr: u64, e: int)
    requires
        rank.len() == parent.len(),
        0 <= e < parent.len(),
        parent[e] != e,
        forall|x: int| 0 <= x < parent.len() ==> #[trigger] parent[x] < parent.len(),
        forall|x: int| 0 <= x < parent.len() ==> rank[x] <= mr,
        forall|x: int|
            0 <= x < parent.len() && parent[x] != x ==> #[trigger] rank[x] < rank[parent[x] as int],
    ensures
        rep(parent, rank, mr, e) == rep(parent, rank, mr, parent[e] as int),
{
}

// ── root_sum: partition of the n elements over the trees ────────────────

/// Sum of `size[e]` over the roots among indices 0..k.
pub open spec fn root_sum(parent: Seq<usize>, size: Seq<u64>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if k > parent.len() || k > size.len() {
        0
    } else {
        (if parent[k - 1] == (k - 1) as usize { size[k - 1] as int } else { 0 })
            + root_sum(parent, size, k - 1)
    }
}

/// The partition sum is at least the sizes of any two distinct roots.
pub proof fn lemma_root_sum_ge_two(parent: Seq<usize>, size: Seq<u64>, lo: int, hi: int, k: int)
    requires
        parent.len() == size.len(),
        0 <= lo < k <= parent.len(),
        0 <= hi < k,
        lo != hi,
        parent[lo] == lo,
        parent[hi] == hi,
    ensures
        root_sum(parent, size, k) >= size[lo] as int + size[hi] as int,
    decreases k,
{
    if k - 1 == lo {
        lemma_root_sum_ge_one(parent, size, hi, k - 1);
        lemma_root_sum_nonneg(parent, size, k - 1);
    } else if k - 1 == hi {
        lemma_root_sum_ge_one(parent, size, lo, k - 1);
        lemma_root_sum_nonneg(parent, size, k - 1);
    } else {
        lemma_root_sum_ge_two(parent, size, lo, hi, k - 1);
    }
}

/// The partition sum is at least the size of any single root.
pub proof fn lemma_root_sum_ge_one(parent: Seq<usize>, size: Seq<u64>, j: int, k: int)
    requires
        parent.len() == size.len(),
        0 <= j < k <= parent.len(),
        parent[j] == j,
    ensures
        root_sum(parent, size, k) >= size[j] as int,
    decreases k,
{
    if k - 1 == j {
        lemma_root_sum_nonneg(parent, size, k - 1);
    } else {
        lemma_root_sum_ge_one(parent, size, j, k - 1);
    }
}

/// The partition sum is non-negative.
pub proof fn lemma_root_sum_nonneg(parent: Seq<usize>, size: Seq<u64>, k: int)
    requires parent.len() == size.len(),
    ensures root_sum(parent, size, k) >= 0,
    decreases k,
{
    if 0 < k <= parent.len() {
        lemma_root_sum_nonneg(parent, size, k - 1);
    }
}

/// Merging root `lo` under root `hi` (parent[lo]:=hi) and adding lo's size to
/// hi's preserves the partition sum.
pub proof fn lemma_root_sum_merge(parent: Seq<usize>, size: Seq<u64>, lo: int, hi: int, k: int)
    requires
        parent.len() == size.len(),
        0 <= lo < parent.len(),
        0 <= hi < parent.len(),
        lo != hi,
        parent[lo] == lo,
        parent[hi] == hi,
        size[hi] as int + size[lo] as int <= u64::MAX as int,
        0 <= k <= parent.len(),
    ensures
        root_sum(parent.update(lo, hi as usize), size.update(hi, (size[hi] + size[lo]) as u64), k)
            == root_sum(parent, size, k)
                + (if lo < k { -(size[lo] as int) } else { 0 })
                + (if hi < k { size[lo] as int } else { 0 }),
    decreases k,
{
    if 0 < k <= parent.len() {
        lemma_root_sum_merge(parent, size, lo, hi, k - 1);
        let np = parent.update(lo, hi as usize);
        let ns = size.update(hi, (size[hi] + size[lo]) as u64);
        assert(np[k - 1] == if (k - 1) == lo { hi as usize } else { parent[k - 1] });
        assert(ns[k - 1] == if (k - 1) == hi { (size[hi] + size[lo]) as u64 } else { size[k - 1] });
    }
}

/// A union-find structure with union-by-rank.
pub struct EquivalenceClass {
    pub n: usize,
    pub parent: Vec<usize>,
    pub rank: Vec<u64>,
    pub size: Vec<u64>,
    pub ops_done: u64,
    pub max_ops: u64,
    /// An upper bound on all ranks (the recursion measure ceiling for `rep`).
    pub max_rank: u64,
}

impl EquivalenceClass {
    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ `TypeInvariant`: parent and rank are functions over Elements and
    /// parent stays within Elements.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.parent.len() == self.n
        &&& self.rank.len() == self.n
        &&& self.size.len() == self.n
        &&& (forall|x: int| 0 <= x < self.n ==> #[trigger] self.parent@[x] < self.n)
    }

    /// Every rank is bounded by max_rank (keeps `rep`'s measure non-negative).
    pub open spec fn rank_bound(&self) -> bool {
        forall|x: int| 0 <= x < self.n ==> #[trigger] self.rank@[x] <= self.max_rank
    }

    /// Canonical operation/rank strengthening used by the TLAPS carrier.
    pub open spec fn operation_bound(&self) -> bool {
        self.ops_done <= self.max_ops && self.max_rank <= self.ops_done
    }

    /// A non-root has strictly smaller rank than its parent.
    pub open spec fn strict_rank(&self) -> bool {
        forall|x: int|
            0 <= x < self.n && self.parent@[x] != x
                ==> #[trigger] self.rank@[x] < self.rank@[self.parent@[x] as int]
    }

    /// Union-by-rank size bound: a node of rank r heads a subtree of >= 2^r
    /// nodes; the root sizes partition the n elements. Together: 2^rank <= n.
    pub open spec fn size_bound(&self) -> bool {
        &&& (forall|x: int| 0 <= x < self.n ==> #[trigger] pow2(self.rank@[x]) <= self.size@[x])
        &&& root_sum(self.parent@, self.size@, self.n as int) == self.n as int
    }

    /// Full maintained invariant for the executable union-find state.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.rank_bound() && self.strict_rank()
            && self.size_bound() && self.operation_bound()
    }

    /// rep(e) over this structure.
    pub open spec fn rep_of(&self, e: int) -> int {
        rep(self.parent@, self.rank@, self.max_rank, e)
    }

    // ── Structural obligations derived from inv ─────────────────────────

    pub open spec fn rank_monotonicity(&self) -> bool {
        forall|e: int|
            0 <= e < self.n && self.parent@[e] != e
                ==> #[trigger] self.rank@[e] <= self.rank@[self.parent@[e] as int]
    }

    pub open spec fn representative_rootedness(&self) -> bool {
        forall|e: int| 0 <= e < self.n ==> #[trigger] self.parent@[self.rep_of(e) as int] == self.rep_of(e)
    }

    pub open spec fn representative_idempotence(&self) -> bool {
        forall|e: int| 0 <= e < self.n ==> #[trigger] self.rep_of(self.rep_of(e)) == self.rep_of(e)
    }

    /// Proof that the rep-based checked invariants hold whenever `inv` holds.
    pub proof fn lemma_inv_implies_structural_obligations(&self)
        requires self.inv(),
        ensures
            self.rank_monotonicity(),
            self.representative_rootedness(),
            self.representative_idempotence(),
    {
        assert forall|e: int| 0 <= e < self.n implies
            (#[trigger] self.parent@[self.rep_of(e) as int] == self.rep_of(e)
                && self.rep_of(self.rep_of(e)) == self.rep_of(e)) by {
            lemma_rep_root(self.parent@, self.rank@, self.max_rank, e);
            lemma_rep_root(self.parent@, self.rank@, self.max_rank, self.rep_of(e));
        }
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Each element its own root, rank 0, size 1. Realises the TLA+ `Init`.
    pub fn new(n: usize, max_ops: u64) -> (uf: EquivalenceClass)
        ensures
            uf.n == n,
            uf.max_ops == max_ops,
            uf.ops_done == 0,
            uf.inv(),
            forall|e: int| 0 <= e < n ==> #[trigger] uf.parent@[e] == e,
    {
        let mut parent: Vec<usize> = Vec::new();
        let mut rank: Vec<u64> = Vec::new();
        let mut size: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                parent.len() == i,
                rank.len() == i,
                size.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] parent@[k] == k,
                forall|k: int| 0 <= k < i ==> rank@[k] == 0,
                forall|k: int| 0 <= k < i ==> size@[k] == 1,
                root_sum(parent@, size@, i as int) == i as int,
            decreases n - i,
        {
            proof {
                lemma_root_sum_push_root(parent@, size@, i as int);
            }
            parent.push(i);
            rank.push(0);
            size.push(1);
            i = i + 1;
        }
        let uf = EquivalenceClass { n, parent, rank, size, ops_done: 0, max_ops, max_rank: 0 };
        assert(uf.size_bound()) by {
            assert forall|x: int| 0 <= x < uf.n implies #[trigger] pow2(uf.rank@[x]) <= uf.size@[x] by {
            }
        }
        uf
    }

    // ── find: representative (iterative, TLA+ Rep) ──────────────────────

    /// Find the representative of `e` by following parent pointers to the root.
    /// Returns rep(e); no path compression (matching the TLA+ Rep semantics).
    pub fn find(&self, e: usize) -> (r: usize)
        requires self.inv(), e < self.n,
        ensures
            r == self.rep_of(e as int),
            r < self.n,
            self.parent@[r as int] == r,
    {
        let mut x = e;
        proof { lemma_rep_root(self.parent@, self.rank@, self.max_rank, e as int); }
        while self.parent[x] != x
            invariant
                self.inv(),
                x < self.n,
                self.rep_of(x as int) == self.rep_of(e as int),
            decreases self.max_rank - self.rank@[x as int],
        {
            proof { lemma_rep_step(self.parent@, self.rank@, self.max_rank, x as int); }
            x = self.parent[x];
        }
        x
    }

    // ── Union (TLA+ Union) ──────────────────────────────────────────────

    /// Merge the classes of `a` and `b` by rank. Returns false if they were
    /// already in the same class. Preserves `inv` (hence all six invariants).
    pub fn union(&mut self, a: usize, b: usize) -> (merged: bool)
        requires
            old(self).inv(),
            a < old(self).n,
            b < old(self).n,
        ensures
            final(self).inv(),
            final(self).n == old(self).n,
            final(self).max_ops == old(self).max_ops,
            merged == (old(self).ops_done < old(self).max_ops
                && old(self).rep_of(a as int) != old(self).rep_of(b as int)),
            !merged ==> {
                &&& final(self).parent@ == old(self).parent@
                &&& final(self).rank@ == old(self).rank@
                &&& final(self).size@ == old(self).size@
                &&& final(self).ops_done == old(self).ops_done
                &&& final(self).max_rank == old(self).max_rank
            },
            merged ==> final(self).ops_done == old(self).ops_done + 1,
            merged && old(self).rank@[old(self).rep_of(a as int)]
                    < old(self).rank@[old(self).rep_of(b as int)] ==> {
                &&& final(self).parent@ == old(self).parent@.update(
                    old(self).rep_of(a as int), old(self).rep_of(b as int) as usize)
                &&& final(self).rank@ == old(self).rank@
                &&& final(self).size@ == old(self).size@.update(
                    old(self).rep_of(b as int),
                    (old(self).size@[old(self).rep_of(b as int)]
                        + old(self).size@[old(self).rep_of(a as int)]) as u64)
                &&& final(self).max_rank == old(self).max_rank
            },
            merged && old(self).rank@[old(self).rep_of(a as int)]
                    > old(self).rank@[old(self).rep_of(b as int)] ==> {
                &&& final(self).parent@ == old(self).parent@.update(
                    old(self).rep_of(b as int), old(self).rep_of(a as int) as usize)
                &&& final(self).rank@ == old(self).rank@
                &&& final(self).size@ == old(self).size@.update(
                    old(self).rep_of(a as int),
                    (old(self).size@[old(self).rep_of(a as int)]
                        + old(self).size@[old(self).rep_of(b as int)]) as u64)
                &&& final(self).max_rank == old(self).max_rank
            },
            merged && old(self).rank@[old(self).rep_of(a as int)]
                    == old(self).rank@[old(self).rep_of(b as int)] ==> {
                &&& final(self).parent@ == old(self).parent@.update(
                    old(self).rep_of(b as int), old(self).rep_of(a as int) as usize)
                &&& final(self).rank@ == old(self).rank@.update(
                    old(self).rep_of(a as int),
                    (old(self).rank@[old(self).rep_of(a as int)] + 1) as u64)
                &&& final(self).size@ == old(self).size@.update(
                    old(self).rep_of(a as int),
                    (old(self).size@[old(self).rep_of(a as int)]
                        + old(self).size@[old(self).rep_of(b as int)]) as u64)
                &&& final(self).max_rank == if (old(self).rank@[old(self).rep_of(a as int)] + 1) as u64
                        > old(self).max_rank
                    { (old(self).rank@[old(self).rep_of(a as int)] + 1) as u64 }
                    else { old(self).max_rank }
            },
    {
        if self.ops_done >= self.max_ops {
            return false;
        }
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        // ra, rb are distinct roots: parent[ra]=ra, parent[rb]=rb.
        self.ops_done = self.ops_done + 1;
        if self.rank[ra] < self.rank[rb] {
            self.merge(ra, rb);
        } else if self.rank[ra] > self.rank[rb] {
            self.merge(rb, ra);
        } else {
            // TLA+ equal case: attach rb under ra, bump ra's rank.
            self.merge_equal(rb, ra);
        }
        true
    }

    /// Attach root `lo` under root `hi` where rank[lo] < rank[hi]. Sizes add;
    /// ranks unchanged.
    fn merge(&mut self, lo: usize, hi: usize)
        requires
            old(self).inv(),
            lo < old(self).n,
            hi < old(self).n,
            lo != hi,
            old(self).parent@[lo as int] == lo,
            old(self).parent@[hi as int] == hi,
            old(self).rank@[lo as int] < old(self).rank@[hi as int],
        ensures
            final(self).inv(),
            final(self).n == old(self).n,
            final(self).max_ops == old(self).max_ops,
            final(self).max_rank == old(self).max_rank,
            final(self).ops_done == old(self).ops_done,
            final(self).parent@ == old(self).parent@.update(lo as int, hi),
            final(self).rank@ == old(self).rank@,
            final(self).size@ == old(self).size@.update(
                hi as int, (old(self).size@[hi as int] + old(self).size@[lo as int]) as u64),
    {
        proof {
            lemma_root_sum_ge_two(self.parent@, self.size@, lo as int, hi as int, self.n as int);
            lemma_root_sum_merge(self.parent@, self.size@, lo as int, hi as int, self.n as int);
        }
        let new_size = self.size[hi] + self.size[lo];
        self.parent.set(lo, hi);
        self.size.set(hi, new_size);
    }

    /// Attach root `lo` (rank r) under root `hi` (rank r) and bump hi's rank to
    /// r+1. Sizes add; the doubling re-establishes 2^(r+1) <= size[hi].
    fn merge_equal(&mut self, lo: usize, hi: usize)
        requires
            old(self).inv(),
            lo < old(self).n,
            hi < old(self).n,
            lo != hi,
            old(self).parent@[lo as int] == lo,
            old(self).parent@[hi as int] == hi,
            old(self).rank@[lo as int] == old(self).rank@[hi as int],
            old(self).max_rank < old(self).ops_done,
        ensures
            final(self).inv(),
            final(self).n == old(self).n,
            final(self).max_ops == old(self).max_ops,
            final(self).ops_done == old(self).ops_done,
            final(self).parent@ == old(self).parent@.update(lo as int, hi),
            final(self).rank@ == old(self).rank@.update(
                hi as int, (old(self).rank@[hi as int] + 1) as u64),
            final(self).size@ == old(self).size@.update(
                hi as int, (old(self).size@[hi as int] + old(self).size@[lo as int]) as u64),
            final(self).max_rank == if (old(self).rank@[hi as int] + 1) as u64 > old(self).max_rank
                { (old(self).rank@[hi as int] + 1) as u64 } else { old(self).max_rank },
    {
        proof {
            lemma_root_sum_ge_two(self.parent@, self.size@, lo as int, hi as int, self.n as int);
            lemma_root_sum_merge(self.parent@, self.size@, lo as int, hi as int, self.n as int);
            // rank[hi] <= 63, so the increment does not overflow.
            lemma_rank_le_63(self.rank@[hi as int], self.n as int);
            lemma_root_sum_ge_one(self.parent@, self.size@, hi as int, self.n as int);
        }
        let new_size = self.size[hi] + self.size[lo];
        let new_rank = self.rank[hi] + 1;
        self.parent.set(lo, hi);
        self.size.set(hi, new_size);
        self.rank.set(hi, new_rank);
        if new_rank > self.max_rank {
            self.max_rank = new_rank;
        }
        proof {
            // strict_rank: lo now points to hi (rank[lo] < rank[hi]+1); hi's old
            // children e keep rank[e] < rank[hi] < rank[hi]+1; all else unchanged.
            assert forall|x: int| 0 <= x < self.n && self.parent@[x] != x
                implies #[trigger] self.rank@[x] < self.rank@[self.parent@[x] as int] by {
                if x == lo as int {
                } else if old(self).parent@[x] == hi as int {
                    assert(old(self).rank@[x] < old(self).rank@[hi as int]);
                } else {
                    assert(old(self).parent@[x] != x);
                    assert(old(self).rank@[x] < old(self).rank@[old(self).parent@[x] as int]);
                }
            }
            // pow_size: at hi, 2^(r+1) = 2*2^r <= size[hi] + size[lo] (both >= 2^r
            // since rank[lo] = rank[hi] = r); elsewhere unchanged.
            assert forall|x: int| 0 <= x < self.n
                implies #[trigger] pow2(self.rank@[x]) <= self.size@[x] by {
                if x == hi as int {
                    assert(self.rank@[hi as int] == old(self).rank@[hi as int] + 1);
                    assert(pow2(self.rank@[hi as int]) == 2 * pow2(old(self).rank@[hi as int]));
                    assert(pow2(old(self).rank@[hi as int]) <= old(self).size@[hi as int]);
                    assert(pow2(old(self).rank@[lo as int]) <= old(self).size@[lo as int]);
                } else {
                    assert(pow2(old(self).rank@[x]) <= old(self).size@[x]);
                }
            }
        }
    }

    /// Whether a and b are in the same class.
    pub fn same(&self, a: usize, b: usize) -> (yes: bool)
        requires self.inv(), a < self.n, b < self.n,
        ensures yes == (self.rep_of(a as int) == self.rep_of(b as int)),
    {
        self.find(a) == self.find(b)
    }
}

/// Pushing a fresh root with size 1 at index k extends the partition sum by 1.
pub proof fn lemma_root_sum_push_root(parent: Seq<usize>, size: Seq<u64>, k: int)
    requires
        parent.len() == k,
        size.len() == k,
        0 <= k,
    ensures
        root_sum(parent.push(k as usize), size.push(1), k + 1) == root_sum(parent, size, k) + 1,
{
    assert(root_sum(parent.push(k as usize), size.push(1), k)
        == root_sum(parent, size, k)) by {
        lemma_root_sum_prefix(parent, size, k as usize, 1, k);
    }
}

/// Pushing onto parent/size does not change the partition sum over the prefix.
pub proof fn lemma_root_sum_prefix(parent: Seq<usize>, size: Seq<u64>, pv: usize, sv: u64, k: int)
    requires
        0 <= k <= parent.len(),
        k <= size.len(),
    ensures
        root_sum(parent.push(pv), size.push(sv), k) == root_sum(parent, size, k),
    decreases k,
{
    if 0 < k {
        lemma_root_sum_prefix(parent, size, pv, sv, k - 1);
    }
}

}
