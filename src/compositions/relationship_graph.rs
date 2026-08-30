// RelationshipGraph executable correspondence boundary.
//
// RelationshipGraph is a weighted directed graph kept with a redundant
// adjacency view that must stay consistent with the edge set. The TLA+ spec at
// formal/structures/RelationshipGraph/RelationshipGraph.tla has two state variables — edges (a set of
// <<src, dst, weight>> triples) and adjacency (Nodes -> SUBSET Nodes) — and
// checks three invariants:
//
//   TypeInvariant        == edges ⊆ Nodes × Nodes × (0..MaxWeight)
//                            /\ adjacency ∈ [Nodes -> SUBSET Nodes]
//   AdjacencyConsistency == ∀ src: adjacency[src] =
//                              {dst : ∃ w: <<src,dst,w>> ∈ edges}
//   NoSelfLoops          == ∀ n: n ∉ adjacency[n]
//
// AdjacencyConsistency is an exact set equality between the independent
// adjacency view and the edge-set projection: the TLA+ keeps both variables and
// updates them in lockstep, so the invariant is maintained rather than
// definitional. This module carries the same separation: `edges` is a weighted
// edge list, carrying TypeInvariant's weight clause, and `adjacency` is an
// independent (src, dst) pair list; AdjacencyConsistency is discharged as the
// projection-equivalence has_pair(adjacency) <=> has_edge(edges) over every node
// pair, under both actions (AddEdge, RemoveEdge). RemoveEdge drops every
// (src,dst,*) edge, and its projection-preservation is the central proof
// obligation.
//
// Nodes is the index universe 0..num_nodes-1 (usize ids).

use vstd::prelude::*;

verus! {

/// has_edge over the first `n` entries: some edge among edges[0..n] goes s -> d.
pub open spec fn has_edge(edges: Seq<(usize, usize, u64)>, n: int, s: usize, d: usize) -> bool {
    exists|i: int| 0 <= i < n && edges[i].0 == s && edges[i].1 == d
}

/// Exact weighted-edge membership over a prefix.
pub open spec fn has_exact_edge(
    edges: Seq<(usize, usize, u64)>, n: int, s: usize, d: usize, w: u64,
) -> bool {
    exists|i: int| 0 <= i < n && edges[i].0 == s && edges[i].1 == d && edges[i].2 == w
}

/// has_pair over the first `n` entries: some pair among pairs[0..n] is (s, d).
pub open spec fn has_pair(pairs: Seq<(usize, usize)>, n: int, s: usize, d: usize) -> bool {
    exists|i: int| 0 <= i < n && pairs[i].0 == s && pairs[i].1 == d
}

// ── projection-extension lemmas ─────────────────────────────────────────

/// Extending the considered prefix by one edge: has_edge over [0..n+1] holds iff
/// it held over [0..n] or the n-th edge itself goes s -> d.
pub proof fn lemma_has_edge_extend(edges: Seq<(usize, usize, u64)>, n: int, s: usize, d: usize)
    requires 0 <= n < edges.len(),
    ensures
        has_edge(edges, n + 1, s, d)
            == (has_edge(edges, n, s, d) || (edges[n].0 == s && edges[n].1 == d)),
{
    if has_edge(edges, n + 1, s, d) {
        let i = choose|i: int| 0 <= i < n + 1 && edges[i].0 == s && edges[i].1 == d;
        assert(i < n || i == n);
    }
    if has_edge(edges, n, s, d) {
        let i = choose|i: int| 0 <= i < n && edges[i].0 == s && edges[i].1 == d;
        assert(0 <= i < n + 1 && edges[i].0 == s && edges[i].1 == d);
    }
    if edges[n].0 == s && edges[n].1 == d {
        assert(0 <= n < n + 1 && edges[n].0 == s && edges[n].1 == d);
    }
}

pub proof fn lemma_has_exact_edge_extend(
    edges: Seq<(usize, usize, u64)>, n: int, s: usize, d: usize, w: u64,
)
    requires 0 <= n < edges.len(),
    ensures has_exact_edge(edges, n + 1, s, d, w)
        == (has_exact_edge(edges, n, s, d, w)
            || (edges[n].0 == s && edges[n].1 == d && edges[n].2 == w)),
{
    if has_exact_edge(edges, n + 1, s, d, w) {
        let i = choose|i: int| 0 <= i < n + 1 && edges[i].0 == s
            && edges[i].1 == d && edges[i].2 == w;
        assert(i < n || i == n);
    }
    if has_exact_edge(edges, n, s, d, w) {
        let i = choose|i: int| 0 <= i < n && edges[i].0 == s
            && edges[i].1 == d && edges[i].2 == w;
        assert(0 <= i < n + 1);
    }
    if edges[n].0 == s && edges[n].1 == d && edges[n].2 == w {
        assert(0 <= n < n + 1);
    }
}

/// has_pair analogue of lemma_has_edge_extend.
pub proof fn lemma_has_pair_extend(pairs: Seq<(usize, usize)>, n: int, s: usize, d: usize)
    requires 0 <= n < pairs.len(),
    ensures
        has_pair(pairs, n + 1, s, d)
            == (has_pair(pairs, n, s, d) || (pairs[n].0 == s && pairs[n].1 == d)),
{
    if has_pair(pairs, n + 1, s, d) {
        let i = choose|i: int| 0 <= i < n + 1 && pairs[i].0 == s && pairs[i].1 == d;
        assert(i < n || i == n);
    }
    if has_pair(pairs, n, s, d) {
        let i = choose|i: int| 0 <= i < n && pairs[i].0 == s && pairs[i].1 == d;
        assert(0 <= i < n + 1 && pairs[i].0 == s && pairs[i].1 == d);
    }
    if pairs[n].0 == s && pairs[n].1 == d {
        assert(0 <= n < n + 1 && pairs[n].0 == s && pairs[n].1 == d);
    }
}

/// Pushing (a,b,w) makes has_edge at (s,d) hold iff it already held or
/// (s,d) == (a,b).
pub proof fn lemma_push_proj_edge(
    edges: Seq<(usize, usize, u64)>, a: usize, b: usize, w: u64, s: usize, d: usize,
)
    ensures
        has_edge(edges.push((a, b, w)), edges.len() as int + 1, s, d)
            == (has_edge(edges, edges.len() as int, s, d) || (s == a && d == b)),
{
    let pushed = edges.push((a, b, w));
    if has_edge(edges, edges.len() as int, s, d) {
        let i = choose|i: int| 0 <= i < edges.len() && edges[i].0 == s && edges[i].1 == d;
        assert(pushed[i] == edges[i]);
    }
    if s == a && d == b {
        assert(pushed[edges.len() as int].0 == s && pushed[edges.len() as int].1 == d);
    }
    if has_edge(pushed, edges.len() as int + 1, s, d) {
        let i = choose|i: int| 0 <= i < edges.len() as int + 1 && pushed[i].0 == s && pushed[i].1 == d;
        if i < edges.len() {
            assert(edges[i] == pushed[i]);
        }
    }
}

pub proof fn lemma_push_exact_edge(
    edges: Seq<(usize, usize, u64)>, a: usize, b: usize, x: u64,
    s: usize, d: usize, w: u64,
)
    ensures has_exact_edge(edges.push((a, b, x)), edges.len() as int + 1, s, d, w)
        == (has_exact_edge(edges, edges.len() as int, s, d, w)
            || (s == a && d == b && w == x)),
{
    let pushed = edges.push((a, b, x));
    if has_exact_edge(edges, edges.len() as int, s, d, w) {
        let i = choose|i: int| 0 <= i < edges.len() && edges[i].0 == s
            && edges[i].1 == d && edges[i].2 == w;
        assert(pushed[i] == edges[i]);
    }
    if s == a && d == b && w == x {
        assert(pushed[edges.len() as int] == (a, b, x));
    }
    if has_exact_edge(pushed, edges.len() as int + 1, s, d, w) {
        let i = choose|i: int| 0 <= i < edges.len() as int + 1
            && pushed[i].0 == s && pushed[i].1 == d && pushed[i].2 == w;
        if i < edges.len() { assert(edges[i] == pushed[i]); }
    }
}

/// Pushing (a,b) makes has_pair at (s,d) hold iff it already held or
/// (s,d) == (a,b).
pub proof fn lemma_push_proj_pair(
    pairs: Seq<(usize, usize)>, a: usize, b: usize, s: usize, d: usize,
)
    ensures
        has_pair(pairs.push((a, b)), pairs.len() as int + 1, s, d)
            == (has_pair(pairs, pairs.len() as int, s, d) || (s == a && d == b)),
{
    let pushed = pairs.push((a, b));
    if has_pair(pairs, pairs.len() as int, s, d) {
        let i = choose|i: int| 0 <= i < pairs.len() && pairs[i].0 == s && pairs[i].1 == d;
        assert(pushed[i] == pairs[i]);
    }
    if s == a && d == b {
        assert(pushed[pairs.len() as int].0 == s && pushed[pairs.len() as int].1 == d);
    }
    if has_pair(pushed, pairs.len() as int + 1, s, d) {
        let i = choose|i: int| 0 <= i < pairs.len() as int + 1 && pushed[i].0 == s && pushed[i].1 == d;
        if i < pairs.len() {
            assert(pairs[i] == pushed[i]);
        }
    }
}

/// A weighted directed graph with a consistent adjacency view.
pub struct RelationshipGraph {
    pub num_nodes: usize,
    pub max_weight: u64,
    /// The edge set as a weighted list of (src, dst, weight).
    pub edges: Vec<(usize, usize, u64)>,
    /// The adjacency relation as an independent list of (src, dst) pairs.
    pub adjacency: Vec<(usize, usize)>,
}

impl RelationshipGraph {
    // ── Specifications ──────────────────────────────────────────────────

    /// `has_edge` over the whole edge list.
    pub open spec fn edge_proj(&self, s: usize, d: usize) -> bool {
        has_edge(self.edges@, self.edges@.len() as int, s, d)
    }

    pub open spec fn exact_edge(&self, s: usize, d: usize, w: u64) -> bool {
        has_exact_edge(self.edges@, self.edges@.len() as int, s, d, w)
    }

    /// `has_pair` over the whole adjacency list.
    pub open spec fn adj_proj(&self, s: usize, d: usize) -> bool {
        has_pair(self.adjacency@, self.adjacency@.len() as int, s, d)
    }

    /// TLA+ `TypeInvariant`: edges and adjacency entries are well-typed.
    pub open spec fn type_invariant(&self) -> bool {
        &&& (forall|i: int|
                #![trigger self.edges@[i]]
                0 <= i < self.edges.len() ==>
                    self.edges@[i].0 < self.num_nodes && self.edges@[i].1 < self.num_nodes
                        && self.edges@[i].2 <= self.max_weight)
        &&& (forall|i: int|
                #![trigger self.adjacency@[i]]
                0 <= i < self.adjacency.len() ==>
                    self.adjacency@[i].0 < self.num_nodes && self.adjacency@[i].1 < self.num_nodes)
    }

    /// TLA+ `AdjacencyConsistency`: the adjacency projection equals the edge
    /// projection at every node pair.
    pub open spec fn adjacency_consistency(&self) -> bool {
        forall|s: usize, d: usize|
            s < self.num_nodes && d < self.num_nodes ==>
                crate::connectives::projection::membership_consistent(
                    #[trigger] self.adj_proj(s, d),
                    self.edge_proj(s, d),
                )
    }

    /// TLA+ `NoSelfLoops`: no adjacency pair is a self-loop (so n ∉ adjacency[n]).
    pub open spec fn no_self_loops(&self) -> bool {
        forall|i: int|
            #![trigger self.adjacency@[i]]
            0 <= i < self.adjacency.len() ==> self.adjacency@[i].0 != self.adjacency@[i].1
    }

    /// Full maintained invariant.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.adjacency_consistency()
        &&& self.no_self_loops()
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Empty graph: no edges, no adjacency. Realises the TLA+ `Init` predicate.
    pub fn new(num_nodes: usize, max_weight: u64) -> (g: RelationshipGraph)
        ensures
            g.num_nodes == num_nodes,
            g.max_weight == max_weight,
            g.edges@.len() == 0,
            g.adjacency@.len() == 0,
            g.inv(),
    {
        RelationshipGraph { num_nodes, max_weight, edges: Vec::new(), adjacency: Vec::new() }
    }

    pub fn can_add_edge(&self, src: usize, dst: usize, weight: u64) -> (b: bool)
        ensures b == (src < self.num_nodes && dst < self.num_nodes
            && weight <= self.max_weight && src != dst),
    {
        src < self.num_nodes && dst < self.num_nodes
            && weight <= self.max_weight && src != dst
    }

    pub fn contains_exact_edge(&self, src: usize, dst: usize, weight: u64) -> (b: bool)
        ensures b == self.exact_edge(src, dst, weight),
    {
        let len = self.edges.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.edges.len(),
                !has_exact_edge(self.edges@, i as int, src, dst, weight),
            decreases len - i,
        {
            if self.edges[i].0 == src && self.edges[i].1 == dst && self.edges[i].2 == weight {
                return true;
            }
            proof { lemma_has_exact_edge_extend(self.edges@, i as int, src, dst, weight); }
            i = i + 1;
        }
        false
    }

    pub fn contains_pair(&self, src: usize, dst: usize) -> (b: bool)
        ensures b == self.adj_proj(src, dst),
    {
        let len = self.adjacency.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.adjacency.len(),
                !has_pair(self.adjacency@, i as int, src, dst),
            decreases len - i,
        {
            if self.adjacency[i].0 == src && self.adjacency[i].1 == dst {
                return true;
            }
            proof { lemma_has_pair_extend(self.adjacency@, i as int, src, dst); }
            i = i + 1;
        }
        false
    }

    // ── AddEdge (TLA+ AddEdge) ──────────────────────────────────────────

    /// Add the weighted edge src -> dst. Guard src != dst (the TLA+ AddEdge
    /// enabling condition). Both the edge list and the adjacency list gain the
    /// pair, so the projections grow together and stay equivalent.
    pub fn add_edge(&mut self, src: usize, dst: usize, weight: u64) -> (added: bool)
        requires
            old(self).inv(),
            src < old(self).num_nodes,
            dst < old(self).num_nodes,
            weight <= old(self).max_weight,
            src != dst,
        ensures
            final(self).inv(),
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_weight == old(self).max_weight,
            added == !old(self).exact_edge(src, dst, weight),
            !added ==> final(self).edges@ == old(self).edges@
                && final(self).adjacency@ == old(self).adjacency@,
            added ==> final(self).edges@ == old(self).edges@.push((src, dst, weight)),
            added && old(self).adj_proj(src, dst)
                ==> final(self).adjacency@ == old(self).adjacency@,
            added && !old(self).adj_proj(src, dst)
                ==> final(self).adjacency@ == old(self).adjacency@.push((src, dst)),
    {
        if self.contains_exact_edge(src, dst, weight) {
            return false;
        }
        let pair_present = self.contains_pair(src, dst);
        self.edges.push((src, dst, weight));
        if !pair_present {
            self.adjacency.push((src, dst));
        }
        assert(self.adjacency_consistency()) by {
            assert forall|s: usize, d: usize|
                s < self.num_nodes && d < self.num_nodes
                implies (#[trigger] self.adj_proj(s, d)) == self.edge_proj(s, d) by {
                lemma_push_proj_edge(old(self).edges@, src, dst, weight, s, d);
                assert(old(self).adj_proj(s, d) == old(self).edge_proj(s, d));
                if pair_present {
                    assert(old(self).adj_proj(src, dst));
                } else {
                    lemma_push_proj_pair(old(self).adjacency@, src, dst, s, d);
                }
            }
        }
        true
    }

    // ── RemoveEdge (TLA+ RemoveEdge) ────────────────────────────────────

    /// Remove every edge src -> dst (all weights) and drop the pair from the
    /// adjacency view. Both projections lose exactly the pair (src,dst), so
    /// they remain equivalent.
    pub fn remove_edge(&mut self, src: usize, dst: usize)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_weight == old(self).max_weight,
            forall|s: usize, d: usize|
                #[trigger] final(self).edge_proj(s, d)
                    == (!(s == src && d == dst) && old(self).edge_proj(s, d)),
            forall|s: usize, d: usize|
                #[trigger] final(self).adj_proj(s, d)
                    == (!(s == src && d == dst) && old(self).adj_proj(s, d)),
            forall|s: usize, d: usize, w: u64|
                #[trigger] final(self).exact_edge(s, d, w)
                    == (!(s == src && d == dst) && old(self).exact_edge(s, d, w)),
    {
        let new_edges = Self::filter_edges(&self.edges, src, dst, self.num_nodes, self.max_weight);
        let new_adj = Self::filter_pairs(&self.adjacency, src, dst, self.num_nodes);
        self.edges = new_edges;
        self.adjacency = new_adj;
        // type_invariant and no_self_loops follow directly: the filters return a
        // well-typed (and, for pairs, self-loop-free) Vec for self.num_nodes /
        // self.max_weight. Consistency: both projections drop exactly (src,dst),
        // and they agreed before (old consistency).
        assert(self.adjacency_consistency()) by {
            assert forall|s: usize, d: usize|
                s < self.num_nodes && d < self.num_nodes
                implies (#[trigger] self.adj_proj(s, d)) == self.edge_proj(s, d) by {
                assert(old(self).adj_proj(s, d) == old(self).edge_proj(s, d));
            }
        }
    }

    // ── filter helpers ──────────────────────────────────────────────────

    /// Edges with every src -> dst entry removed. Ensures the projection drops
    /// exactly the pair (src,dst), and (given a well-typed input) the output is
    /// well-typed too.
    fn filter_edges(edges: &Vec<(usize, usize, u64)>, src: usize, dst: usize,
        num_nodes: usize, max_weight: u64) -> (out: Vec<(usize, usize, u64)>)
        requires
            forall|i: int| #![trigger edges@[i]]
                0 <= i < edges@.len() ==>
                    edges@[i].0 < num_nodes && edges@[i].1 < num_nodes && edges@[i].2 <= max_weight,
        ensures
            forall|s: usize, d: usize|
                #[trigger] has_edge(out@, out@.len() as int, s, d)
                    == (!(s == src && d == dst) && has_edge(edges@, edges@.len() as int, s, d)),
            forall|k: int| #![trigger out@[k]]
                0 <= k < out@.len() ==>
                    out@[k].0 < num_nodes && out@[k].1 < num_nodes && out@[k].2 <= max_weight,
            forall|s: usize, d: usize, w: u64|
                #[trigger] has_exact_edge(out@, out@.len() as int, s, d, w)
                    == (!(s == src && d == dst)
                        && has_exact_edge(edges@, edges@.len() as int, s, d, w)),
    {
        let _ = (num_nodes, max_weight);
        let mut out: Vec<(usize, usize, u64)> = Vec::new();
        let mut i: usize = 0;
        while i < edges.len()
            invariant
                i <= edges.len(),
                forall|t: int| #![trigger edges@[t]]
                    0 <= t < edges@.len() ==>
                        edges@[t].0 < num_nodes && edges@[t].1 < num_nodes && edges@[t].2 <= max_weight,
                forall|s: usize, d: usize|
                    #[trigger] has_edge(out@, out@.len() as int, s, d)
                        == (!(s == src && d == dst) && has_edge(edges@, i as int, s, d)),
                forall|k: int| #![trigger out@[k]]
                    0 <= k < out@.len() ==>
                        out@[k].0 < num_nodes && out@[k].1 < num_nodes && out@[k].2 <= max_weight,
                forall|s: usize, d: usize, w: u64|
                    #[trigger] has_exact_edge(out@, out@.len() as int, s, d, w)
                        == (!(s == src && d == dst) && has_exact_edge(edges@, i as int, s, d, w)),
            decreases edges.len() - i,
        {
            let e = edges[i];
            assert(edges@[i as int].0 < num_nodes && edges@[i as int].1 < num_nodes
                && edges@[i as int].2 <= max_weight);
            let ghost ob = out@;
            if !(e.0 == src && e.1 == dst) {
                out.push(e);
            }
            assert forall|s: usize, d: usize|
                #[trigger] has_edge(out@, out@.len() as int, s, d)
                    == (!(s == src && d == dst) && has_edge(edges@, (i + 1) as int, s, d)) by {
                lemma_has_edge_extend(edges@, i as int, s, d);
                if !(e.0 == src && e.1 == dst) {
                    lemma_push_proj_edge(ob, e.0, e.1, e.2, s, d);
                }
            }
            assert forall|s: usize, d: usize, w: u64|
                #[trigger] has_exact_edge(out@, out@.len() as int, s, d, w)
                    == (!(s == src && d == dst)
                        && has_exact_edge(edges@, (i + 1) as int, s, d, w)) by {
                lemma_has_exact_edge_extend(edges@, i as int, s, d, w);
                if !(e.0 == src && e.1 == dst) {
                    lemma_push_exact_edge(ob, e.0, e.1, e.2, s, d, w);
                }
            }
            assert forall|k: int| #![trigger out@[k]] 0 <= k < out@.len()
                implies (out@[k].0 < num_nodes && out@[k].1 < num_nodes && out@[k].2 <= max_weight) by {
                if k < ob.len() {
                    assert(out@[k] == ob[k]);
                    assert(ob[k].0 < num_nodes && ob[k].1 < num_nodes && ob[k].2 <= max_weight);
                } else {
                    assert(out@[k] == edges@[i as int]);
                    assert(edges@[i as int].0 < num_nodes && edges@[i as int].1 < num_nodes
                        && edges@[i as int].2 <= max_weight);
                }
            }
            i = i + 1;
        }
        out
    }

    /// Adjacency pairs with every (src,dst) entry removed. Ensures the
    /// projection drops exactly that pair, and (given a well-typed, self-loop-
    /// free input) the output is well-typed and self-loop-free too.
    fn filter_pairs(pairs: &Vec<(usize, usize)>, src: usize, dst: usize, num_nodes: usize)
        -> (out: Vec<(usize, usize)>)
        requires
            forall|i: int| #![trigger pairs@[i]]
                0 <= i < pairs@.len() ==>
                    pairs@[i].0 < num_nodes && pairs@[i].1 < num_nodes && pairs@[i].0 != pairs@[i].1,
        ensures
            forall|s: usize, d: usize|
                #[trigger] has_pair(out@, out@.len() as int, s, d)
                    == (!(s == src && d == dst) && has_pair(pairs@, pairs@.len() as int, s, d)),
            forall|k: int| #![trigger out@[k]]
                0 <= k < out@.len() ==>
                    out@[k].0 < num_nodes && out@[k].1 < num_nodes && out@[k].0 != out@[k].1,
    {
        let _ = num_nodes;
        let mut out: Vec<(usize, usize)> = Vec::new();
        let mut i: usize = 0;
        while i < pairs.len()
            invariant
                i <= pairs.len(),
                forall|t: int| #![trigger pairs@[t]]
                    0 <= t < pairs@.len() ==>
                        pairs@[t].0 < num_nodes && pairs@[t].1 < num_nodes && pairs@[t].0 != pairs@[t].1,
                forall|s: usize, d: usize|
                    #[trigger] has_pair(out@, out@.len() as int, s, d)
                        == (!(s == src && d == dst) && has_pair(pairs@, i as int, s, d)),
                forall|k: int| #![trigger out@[k]]
                    0 <= k < out@.len() ==>
                        out@[k].0 < num_nodes && out@[k].1 < num_nodes && out@[k].0 != out@[k].1,
            decreases pairs.len() - i,
        {
            let p = pairs[i];
            assert(pairs@[i as int].0 < num_nodes && pairs@[i as int].1 < num_nodes
                && pairs@[i as int].0 != pairs@[i as int].1);
            let ghost ob = out@;
            if !(p.0 == src && p.1 == dst) {
                out.push(p);
            }
            assert forall|s: usize, d: usize|
                #[trigger] has_pair(out@, out@.len() as int, s, d)
                    == (!(s == src && d == dst) && has_pair(pairs@, (i + 1) as int, s, d)) by {
                lemma_has_pair_extend(pairs@, i as int, s, d);
                if !(p.0 == src && p.1 == dst) {
                    lemma_push_proj_pair(ob, p.0, p.1, s, d);
                }
            }
            assert forall|k: int| #![trigger out@[k]] 0 <= k < out@.len()
                implies (out@[k].0 < num_nodes && out@[k].1 < num_nodes && out@[k].0 != out@[k].1) by {
                if k < ob.len() {
                    assert(out@[k] == ob[k]);
                    assert(ob[k].0 < num_nodes && ob[k].1 < num_nodes && ob[k].0 != ob[k].1);
                } else {
                    assert(out@[k] == pairs@[i as int]);
                    assert(pairs@[i as int].0 < num_nodes && pairs@[i as int].1 < num_nodes
                        && pairs@[i as int].0 != pairs@[i as int].1);
                }
            }
            i = i + 1;
        }
        out
    }
}

}
