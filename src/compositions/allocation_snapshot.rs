// Executable carrier for AllocationSnapshot.tla. The allocation decision has
// three state variables: `accepted`, `total_cost`, and `budget_remaining`.
// `accept_node` implements the guarded `AcceptNode(n, cost)` transition and
// maintains:
//
//   TypeInvariant     == accepted ⊆ Nodes /\ total_cost ∈ Nat
//                                          /\ budget_remaining ∈ Nat
//   BudgetConsistency == total_cost + budget_remaining <= BudgetCapacity
//
// `new` implements `Init`. `capture` folds a request sequence through the same
// guarded transition and returns a record with no exposed mutator.
// Representation mapping:
//   - Nodes is the index universe 0..num_nodes; `accepted ⊆ Nodes` becomes
//     "every accepted id < num_nodes".
//   - `accepted` is a TLA+ set variable; it is modelled as a Vec<u64> carrying
//     a no-duplicates invariant, preserving the `n ∉ accepted` guard.
//   - total_cost, budget_remaining ∈ Nat are carried by u64; the spec arithmetic
//     is lifted to `int` to state BudgetConsistency without overflow noise.

use vstd::prelude::*;

verus! {

/// An allocation snapshot: the accepted node set plus the running cost / budget
/// figures, over a node universe `0..num_nodes` bounded by `capacity`.
pub struct AllocationSnapshot {
    /// BudgetCapacity — the structural ceiling.
    pub capacity: u64,
    /// |Nodes|: the node universe is the index range `0..num_nodes`.
    pub num_nodes: u64,
    /// `accepted ⊆ Nodes`, modelled as a duplicate-free Vec of node ids.
    pub accepted: Vec<u64>,
    /// Sum of accepted node costs.
    pub total_cost: u64,
    /// Capacity not yet consumed.
    pub budget_remaining: u64,
}

impl AllocationSnapshot {
    // ── Specifications ──────────────────────────────────────────────────

    /// `accepted ⊆ Nodes`: every accepted id is a valid node index.
    pub open spec fn accepted_subset_nodes(&self) -> bool {
        forall|i: int|
            0 <= i < self.accepted.len() ==> #[trigger] self.accepted@[i] < self.num_nodes
    }

    /// `accepted` is a set: no duplicate node ids. This encodes the TLA+ set
    /// variable and makes the AcceptNode `n ∉ accepted` guard enforceable.
    pub open spec fn accepted_distinct(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < self.accepted.len() && 0 <= j < self.accepted.len() && i != j
                ==> self.accepted@[i] != self.accepted@[j]
    }

    /// TLA+ `TypeInvariant` (the structural clauses; the Nat clauses are carried
    /// by the u64 typing of total_cost / budget_remaining).
    pub open spec fn type_invariant(&self) -> bool {
        self.accepted_subset_nodes() && self.accepted_distinct()
    }

    /// TLA+ `BudgetConsistency`.
    pub open spec fn budget_consistency(&self) -> bool {
        self.total_cost + self.budget_remaining <= self.capacity
    }

    /// `n ∈ accepted`.
    pub open spec fn contains(&self, n: u64) -> bool {
        exists|i: int| 0 <= i < self.accepted.len() && self.accepted@[i] == n
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the empty snapshot: nothing accepted, full budget remaining.
    /// Realises the TLA+ `Init` predicate and establishes both invariants.
    pub fn new(capacity: u64, num_nodes: u64) -> (s: AllocationSnapshot)
        ensures
            s.capacity == capacity,
            s.num_nodes == num_nodes,
            s.accepted@.len() == 0,
            s.total_cost == 0,
            s.budget_remaining == capacity,
            s.type_invariant(),
            s.budget_consistency(),
    {
        AllocationSnapshot {
            capacity,
            num_nodes,
            accepted: Vec::new(),
            total_cost: 0,
            budget_remaining: capacity,
        }
    }

    // ── Membership (executable) ─────────────────────────────────────────

    /// Executable membership test; links to the `contains` spec so callers can
    /// discharge the `n ∉ accepted` precondition of `accept_node`.
    pub fn contains_exec(&self, n: u64) -> (b: bool)
        ensures
            b == self.contains(n),
    {
        let len = self.accepted.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.accepted.len(),
                forall|k: int| 0 <= k < i ==> self.accepted@[k] != n,
            decreases len - i,
        {
            if self.accepted[i] == n {
                assert(self.accepted@[i as int] == n);
                return true;
            }
            i = i + 1;
        }
        false
    }

    // ── AcceptNode (TLA+ AcceptNode) ────────────────────────────────────

    /// Accept node `n` at cost `node_cost`. Realises the TLA+ `AcceptNode`
    /// action: its three guards are `requires`, and both invariants are
    /// re-established as `ensures` (the inductive preservation step).
    pub fn accept_node(&mut self, n: u64, node_cost: u64)
        requires
            old(self).type_invariant(),
            old(self).budget_consistency(),
            n < old(self).num_nodes,                  // n ∈ Nodes
            !old(self).contains(n),                   // n ∉ accepted
            1 <= node_cost,                           // c is positive
            node_cost <= old(self).budget_remaining,  // cost fits remaining budget
        ensures
            final(self).capacity == old(self).capacity,
            final(self).num_nodes == old(self).num_nodes,
            final(self).total_cost == old(self).total_cost + node_cost,
            final(self).budget_remaining == old(self).budget_remaining - node_cost,
            final(self).accepted@ == old(self).accepted@.push(n),
            final(self).contains(n),
            final(self).type_invariant(),
            final(self).budget_consistency(),
    {
        // No overflow on total_cost: total_cost + node_cost
        //   <= total_cost + budget_remaining <= capacity <= u64::MAX.
        assert(self.total_cost + node_cost <= self.capacity);
        self.accepted.push(n);
        self.total_cost = self.total_cost + node_cost;
        self.budget_remaining = self.budget_remaining - node_cost;
        // Re-establish the set invariant: the pushed element n was absent
        // (precondition) and is a valid node, so distinctness and the subset
        // bound both carry to the extended sequence.
        assert(self.contains(n)) by {
            assert(self.accepted@[old(self).accepted@.len() as int] == n);
        }
    }
}

// ── capture (fold a whole acceptance sequence into a snapshot) ───────────

/// Build a finished snapshot by folding a sequence of (node, cost) requests
/// through the guarded `AcceptNode` action: a request is accepted iff it is a
/// fresh, valid node whose cost fits the remaining budget (exactly the TLA+
/// guards), otherwise it is skipped. The returned snapshot is immutable and
/// satisfies both invariants. `nodes[i]` is paired with `costs[i]`.
pub fn capture(capacity: u64, num_nodes: u64, nodes: &[u64], costs: &[u64])
    -> (s: AllocationSnapshot)
    requires
        nodes@.len() == costs@.len(),
    ensures
        s.capacity == capacity,
        s.num_nodes == num_nodes,
        s.type_invariant(),
        s.budget_consistency(),
{
    let mut s = AllocationSnapshot::new(capacity, num_nodes);
    let n_reqs = nodes.len();
    let mut i: usize = 0;
    while i < n_reqs
        invariant
            i <= n_reqs,
            n_reqs == nodes@.len(),
            nodes@.len() == costs@.len(),
            s.capacity == capacity,
            s.num_nodes == num_nodes,
            s.type_invariant(),
            s.budget_consistency(),
        decreases n_reqs - i,
    {
        let n = nodes[i];
        let c = costs[i];
        if n < num_nodes && 1 <= c && c <= s.budget_remaining && !s.contains_exec(n) {
            s.accept_node(n, c);
        }
        i = i + 1;
    }
    s
}

}
