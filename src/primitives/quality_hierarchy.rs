// Executable QualityHierarchy contract.
//
// QualityHierarchy is a refinement forest over a node set: each node carries a
// level and a cost, and parent->child edges form a hierarchy in which a parent
// always sits at a strictly higher level than its children. The TLA+ spec at
// formal/structures/QualityHierarchy/QualityHierarchy.tla has four state variables over a node set
// Nodes — level ∈ [Nodes -> 0..MaxLevel], cost ∈ [Nodes -> Nat],
// children ∈ [Nodes -> SUBSET Nodes], parent ∈ [Nodes -> Nodes ∪ {NULL}] — and
// two actions (AddChild, SetNodeProperties). Its .cfg checks four invariants:
//
//   TypeInvariant     == the four variables are well-typed (level in 0..MaxLevel,
//                        cost a Nat, children a node set, parent a node or NULL)
//   StrictLevelDescent == ∀n: ∀c ∈ children[n]: level[n] > level[c]
//   ParentEdgeAgreement== ∀n: ∀c ∈ children[n]: parent[c] = n
//   CostMonotonicity  == ∀n: ∀c ∈ children[n]: cost[n] <= cost[c]
//
// All four predicates are preserved under the full forest dynamics.
//
// `QualityHierarchy.cfg` checks `CostMonotonicity`, so the executable contract
// includes it explicitly. The implementation maintains it because `add_child`
// requires cost[p] <= cost[c] and `set_node_properties` can only touch a node in
// no edge.
//
// Representation:
//   - Nodes is the index universe 0..num_nodes-1 (usize ids).
//   - The `children` relation (a per-node SUBSET Nodes) is modelled as a flat
//     edge list `edges: Vec<(parent, child)>`. (n, c) ∈ edges  iff  c ∈
//     children[n]. This keeps StrictLevelDescent and ParentEdgeAgreement as
//     single-quantifier statements over the edge list rather than nested
//     quantifiers over a Vec<Vec>, while remaining a faithful, independent
//     model of `children` (ParentEdgeAgreement is then a cross-check
//     between `edges` and `parent`, not a by-construction identity).
//   - parent[n] is a node id < num_nodes, or the sentinel `num_nodes` for NULL.
//   - level/cost are u64 per-node vectors; level[n] <= max_level realises the
//     `0..MaxLevel` typing, cost[n] ∈ Nat is carried by u64.

use vstd::prelude::*;

verus! {

/// A refinement forest: per-node level and cost, a parent map (with a NULL
/// sentinel), and the parent->child edge relation.
pub struct QualityHierarchy {
    pub num_nodes: usize,
    pub max_level: u64,
    pub level: Vec<u64>,
    pub cost: Vec<u64>,
    /// `parent[n]` is a node id below `num_nodes`, or `num_nodes` for NULL (no parent).
    pub parent: Vec<usize>,
    /// (parent, child) edges = the `children` relation.
    pub edges: Vec<(usize, usize)>,
}

impl QualityHierarchy {
    // ── Specifications ──────────────────────────────────────────────────

    /// The per-node vectors are indexed by the whole node universe.
    pub open spec fn lengths_ok(&self) -> bool {
        self.level.len() == self.num_nodes
            && self.cost.len() == self.num_nodes
            && self.parent.len() == self.num_nodes
    }

    /// level ∈ [Nodes -> 0..MaxLevel].
    pub open spec fn levels_bounded(&self) -> bool {
        forall|n: int| 0 <= n < self.num_nodes ==> #[trigger] self.level@[n] <= self.max_level
    }

    /// parent ∈ [Nodes -> Nodes ∪ {NULL}]: each entry is a node id or the
    /// NULL sentinel (== num_nodes).
    pub open spec fn parents_valid(&self) -> bool {
        forall|n: int| 0 <= n < self.num_nodes ==> #[trigger] self.parent@[n] <= self.num_nodes
    }

    /// Edge endpoints are nodes (children ⊆ Nodes, and a child's parent is a node).
    pub open spec fn edges_wf(&self) -> bool {
        forall|e: int|
            #![trigger self.edges@[e]]
            0 <= e < self.edges.len() ==>
                self.edges@[e].0 < self.num_nodes && self.edges@[e].1 < self.num_nodes
    }

    /// TLA+ `TypeInvariant`.
    pub open spec fn type_invariant(&self) -> bool {
        self.lengths_ok() && self.levels_bounded() && self.parents_valid() && self.edges_wf()
    }

    /// TLA+ `StrictLevelDescent`: for every parent->child edge, the parent's
    /// level strictly exceeds the child's.
    pub open spec fn strict_level_descent(&self) -> bool {
        forall|e: int|
            #![trigger self.edges@[e]]
            0 <= e < self.edges.len() ==>
                self.level@[self.edges@[e].0 as int] > self.level@[self.edges@[e].1 as int]
    }

    /// TLA+ `ParentEdgeAgreement`: for every parent->child edge, the child's
    /// parent pointer points back at the parent.
    pub open spec fn parent_edge_agreement(&self) -> bool {
        forall|e: int|
            #![trigger self.edges@[e]]
            0 <= e < self.edges.len() ==>
                self.parent@[self.edges@[e].1 as int] == self.edges@[e].0
    }

    /// TLA+ `CostMonotonicity`: for every parent->child edge, the parent's cost
    /// does not exceed the child's. Checked by `QualityHierarchy.cfg`.
    pub open spec fn cost_monotonicity(&self) -> bool {
        forall|e: int|
            #![trigger self.edges@[e]]
            0 <= e < self.edges.len() ==>
                self.cost@[self.edges@[e].0 as int] <= self.cost@[self.edges@[e].1 as int]
    }

    /// NULL: a node has no parent.
    pub open spec fn is_null(&self, x: usize) -> bool {
        x == self.num_nodes
    }

    /// Executable edge-list representation of `c \in children[p]`.
    pub open spec fn edge_exists(&self, p: usize, c: usize) -> bool {
        exists|e: int| 0 <= e < self.edges.len() && #[trigger] self.edges@[e] == (p, c)
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the discrete forest: every node at level 0, cost 0, no parent,
    /// no edges. Realises the TLA+ `Init` predicate.
    pub fn new(num_nodes: usize, max_level: u64) -> (h: QualityHierarchy)
        ensures
            h.num_nodes == num_nodes,
            h.max_level == max_level,
            h.edges@.len() == 0,
            h.type_invariant(),
            h.strict_level_descent(),
            h.parent_edge_agreement(),
            h.cost_monotonicity(),
            forall|n: int| 0 <= n < num_nodes ==> h.level@[n] == 0,
            forall|n: int| 0 <= n < num_nodes ==> h.cost@[n] == 0,
            forall|n: int| 0 <= n < num_nodes ==> h.parent@[n] == num_nodes,
    {
        let mut level: Vec<u64> = Vec::new();
        let mut cost: Vec<u64> = Vec::new();
        let mut parent: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < num_nodes
            invariant
                i <= num_nodes,
                level.len() == i,
                cost.len() == i,
                parent.len() == i,
                forall|k: int| 0 <= k < i ==> level@[k] == 0,
                forall|k: int| 0 <= k < i ==> cost@[k] == 0,
                forall|k: int| 0 <= k < i ==> parent@[k] == num_nodes,
            decreases num_nodes - i,
        {
            level.push(0);
            cost.push(0);
            parent.push(num_nodes);
            i = i + 1;
        }
        QualityHierarchy { num_nodes, max_level, level, cost, parent, edges: Vec::new() }
    }

    // ── Accessors / executable guards ───────────────────────────────────

    /// `level[n]` (executable).
    pub fn level_of(&self, n: usize) -> (l: u64)
        requires self.lengths_ok(), n < self.num_nodes,
        ensures l == self.level@[n as int],
    {
        self.level[n]
    }

    /// `cost[n]` (executable).
    pub fn cost_of(&self, n: usize) -> (c: u64)
        requires self.lengths_ok(), n < self.num_nodes,
        ensures c == self.cost@[n as int],
    {
        self.cost[n]
    }

    /// `parent[n]` (executable); returns the sentinel `num_nodes` for NULL.
    pub fn parent_of(&self, n: usize) -> (p: usize)
        requires self.lengths_ok(), n < self.num_nodes,
        ensures p == self.parent@[n as int],
    {
        self.parent[n]
    }

    /// Whether `n` is anyone's parent in the edge list (`children[n] != {}`).
    /// Used to discharge the SetNodeProperties guard `children[n] = {}`.
    pub fn has_children(&self, n: usize) -> (b: bool)
        ensures b == (exists|e: int|
            #![trigger self.edges@[e]] 0 <= e < self.edges.len() && self.edges@[e].0 == n),
    {
        let len = self.edges.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.edges.len(),
                forall|e: int| #![trigger self.edges@[e]] 0 <= e < i ==> self.edges@[e].0 != n,
            decreases len - i,
        {
            if self.edges[i].0 == n {
                assert(self.edges@[i as int].0 == n);
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// Whether the exact TLA+ `AddChild(p, c)` guard is enabled.
    pub fn can_add_child(&self, p: usize, c: usize) -> (b: bool)
        requires
            self.type_invariant(),
            p < self.num_nodes,
            c < self.num_nodes,
        ensures
            b == (p != c
                && !self.edge_exists(p, c)
                && self.parent@[c as int] == self.num_nodes
                && self.level@[p as int] > self.level@[c as int]
                && self.cost@[p as int] <= self.cost@[c as int]),
    {
        p != c
            && !self.has_edge(p, c)
            && self.parent_of(c) == self.num_nodes
            && self.level_of(p) > self.level_of(c)
            && self.cost_of(p) <= self.cost_of(c)
    }

    /// Whether the exact quantified TLA+ `SetNodeProperties(n, l, c)` guard is
    /// enabled. The canonical model bounds both written values by MaxLevel.
    pub fn can_set_node_properties(&self, n: usize, l: u64, c: u64) -> (b: bool)
        requires
            self.type_invariant(),
            n < self.num_nodes,
        ensures
            b == (!self.has_children_spec(n)
                && self.parent@[n as int] == self.num_nodes
                && l <= self.max_level
                && c <= self.max_level),
    {
        !self.has_children(n)
            && self.parent_of(n) == self.num_nodes
            && l <= self.max_level
            && c <= self.max_level
    }

    pub open spec fn has_children_spec(&self, n: usize) -> bool {
        exists|e: int| 0 <= e < self.edges.len() && #[trigger] self.edges@[e].0 == n
    }

    pub fn has_edge(&self, p: usize, c: usize) -> (b: bool)
        ensures b == self.edge_exists(p, c),
    {
        let len = self.edges.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.edges.len(),
                forall|e: int| 0 <= e < i ==> #[trigger] self.edges@[e] != (p, c),
            decreases len - i,
        {
            if self.edges[i].0 == p && self.edges[i].1 == c {
                assert(self.edges@[i as int].0 == p);
                assert(self.edges@[i as int].1 == c);
                return true;
            }
            i = i + 1;
        }
        false
    }

    // ── AddChild (TLA+ AddChild) ────────────────────────────────────────

    /// Add the edge p->c. Guards (the TLA+ AddChild enabling conditions):
    /// `p != c`, `c` has no parent yet (`parent[c] = NULL`, which under
    /// ParentEdgeAgreement means `c` is no one's child), `level[p] > level[c]`, and
    /// `cost[p] <= cost[c]`. Re-establishes all three invariants.
    pub fn add_child(&mut self, p: usize, c: usize)
        requires
            old(self).type_invariant(),
            old(self).strict_level_descent(),
            old(self).parent_edge_agreement(),
            old(self).cost_monotonicity(),
            p < old(self).num_nodes,
            c < old(self).num_nodes,
            p != c,
            !old(self).edge_exists(p, c),                              // c notin children[p]
            old(self).parent@[c as int] == old(self).num_nodes,        // parent[c] = NULL
            old(self).level@[p as int] > old(self).level@[c as int],    // level[p] > level[c]
            old(self).cost@[p as int] <= old(self).cost@[c as int],     // cost[p] <= cost[c]
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_level == old(self).max_level,
            final(self).level@ == old(self).level@,
            final(self).cost@ == old(self).cost@,
            final(self).edges@ == old(self).edges@.push((p, c)),
            final(self).parent@ == old(self).parent@.update(c as int, p),
            final(self).type_invariant(),
            final(self).strict_level_descent(),
            final(self).parent_edge_agreement(),
            final(self).cost_monotonicity(),
    {
        // Key fact: no existing edge has `c` as its child. If some edge (x, c)
        // existed, ParentEdgeAgreement would force parent[c] = x with x a node
        // (x < num_nodes by edges_wf), contradicting parent[c] = NULL (=num_nodes).
        assert forall|e: int| #![trigger self.edges@[e]]
            0 <= e < self.edges.len() implies self.edges@[e].1 != c by {
            assert(self.parent@[self.edges@[e].1 as int] == self.edges@[e].0);
            assert(self.edges@[e].0 < self.num_nodes);
        }
        self.edges.push((p, c));
        self.parent.set(c, p);
    }

    // ── SetNodeProperties (TLA+ SetNodeProperties) ──────────────────────

    /// Set level and cost of an isolated node (no children, no parent) — the
    /// TLA+ guard `children[n] = {} /\ parent[n] = NULL`. Because such a node
    /// participates in no edge, changing its level cannot break the hierarchy.
    pub fn set_node_properties(&mut self, n: usize, l: u64, c: u64)
        requires
            old(self).type_invariant(),
            old(self).strict_level_descent(),
            old(self).parent_edge_agreement(),
            old(self).cost_monotonicity(),
            n < old(self).num_nodes,
            l <= old(self).max_level,
            c <= old(self).max_level,
            old(self).parent@[n as int] == old(self).num_nodes,        // parent[n] = NULL
            forall|e: int|                                              // children[n] = {}
                #![trigger old(self).edges@[e]]
                0 <= e < old(self).edges.len() ==> old(self).edges@[e].0 != n,
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_level == old(self).max_level,
            final(self).parent@ == old(self).parent@,
            final(self).edges@ == old(self).edges@,
            final(self).level@ == old(self).level@.update(n as int, l),
            final(self).cost@ == old(self).cost@.update(n as int, c),
            final(self).type_invariant(),
            final(self).strict_level_descent(),
            final(self).parent_edge_agreement(),
            final(self).cost_monotonicity(),
    {
        // n is in no edge: it is no one's parent (precondition) and, since
        // parent[n] = NULL, no one's child (ParentEdgeAgreement + edges_wf, as in
        // add_child). So neither endpoint of any edge equals n, and changing
        // level[n] leaves every edge's level comparison untouched.
        assert forall|e: int| #![trigger self.edges@[e]] 0 <= e < self.edges.len()
            implies self.edges@[e].0 != n && self.edges@[e].1 != n by {
            assert(self.parent@[self.edges@[e].1 as int] == self.edges@[e].0);
            assert(self.edges@[e].0 < self.num_nodes);
        }
        self.level.set(n, l);
        self.cost.set(n, c);
    }
}

}
