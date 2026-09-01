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

/// Sum of the registered costs in the first `n` entries.
pub open spec fn cost_sum_to(entries: Seq<(u64, u64)>, n: int) -> int
    decreases n,
{
    if n <= 0 || n > entries.len() {
        0
    } else {
        entries[n - 1].1 as int + cost_sum_to(entries, n - 1)
    }
}

/// Appending one registry entry leaves every prior cost-sum prefix unchanged.
proof fn cost_sum_push_prefix(entries: Seq<(u64, u64)>, entry: (u64, u64), n: int)
    requires 0 <= n <= entries.len(),
    ensures cost_sum_to(entries.push(entry), n) == cost_sum_to(entries, n),
    decreases n,
{
    if n > 0 {
        cost_sum_push_prefix(entries, entry, n - 1);
        assert(entries.push(entry)[n - 1] == entries[n - 1]);
    }
}

/// Appending one cost extends the registered cost sum by exactly that cost.
pub proof fn cost_sum_push(entries: Seq<(u64, u64)>, key: u64, cost: u64)
    ensures
        cost_sum_to(entries.push((key, cost)), entries.len() as int + 1)
            == cost_sum_to(entries, entries.len() as int) + cost as int,
{
    cost_sum_push_prefix(entries, (key, cost), entries.len() as int);
    assert(entries.push((key, cost))[entries.len() as int].1 == cost);
}

/// Exact accepted-entry sequence after folding the first `n` requests.
pub open spec fn capture_entries_to(
    capacity: u64,
    num_nodes: u64,
    nodes: Seq<u64>,
    costs: Seq<u64>,
    n: int,
) -> Seq<(u64, u64)>
    decreases n,
{
    if n <= 0 || n > nodes.len() || n > costs.len() {
        Seq::empty()
    } else {
        let before = capture_entries_to(capacity, num_nodes, nodes, costs, n - 1);
        let node = nodes[n - 1];
        let cost = costs[n - 1];
        if node < num_nodes
            && cost >= 1
            && !crate::primitives::resource_registry::has_key(
                before,
                before.len() as int,
                node,
            )
            && cost_sum_to(before, before.len() as int) + cost as int
                <= capacity as int
        {
            before.push((node, cost))
        } else {
            before
        }
    }
}

/// An allocation snapshot: the accepted node set plus the running cost / budget
/// figures, over a node universe `0..num_nodes` bounded by `capacity`.
pub struct AllocationSnapshot {
    /// |Nodes|: the node universe is the index range `0..num_nodes`.
    pub num_nodes: u64,
    /// ResourceRegistry component mapping accepted nodes to their costs.
    pub registry: crate::primitives::resource_registry::ResourceRegistry<u64, u64>,
    /// Budget component charged by the registered costs.
    pub budget: crate::primitives::budget::Budget,
}

impl AllocationSnapshot {
    // ── Specifications ──────────────────────────────────────────────────

    /// `accepted ⊆ Nodes`: every accepted id is a valid node index.
    pub open spec fn accepted_subset_nodes(&self) -> bool {
        forall|i: int|
            0 <= i < self.registry.entries.len()
                ==> #[trigger] self.registry.entries@[i].0 < self.num_nodes
    }

    /// `accepted` is a set: no duplicate node ids. This encodes the TLA+ set
    /// variable and makes the AcceptNode `n ∉ accepted` guard enforceable.
    pub open spec fn accepted_distinct(&self) -> bool {
        self.registry.unique_mapping()
    }

    /// Every ResourceRegistry value is an admitted positive node cost.
    pub open spec fn costs_valid(&self) -> bool {
        forall|i: int| 0 <= i < self.registry.entries.len()
            ==> #[trigger] self.registry.entries@[i].1 > 0
    }

    /// TLA+ `TypeInvariant` (the structural clauses; the Nat clauses are carried
    /// by the u64 typing of total_cost / budget_remaining).
    pub open spec fn type_invariant(&self) -> bool {
        self.accepted_subset_nodes() && self.accepted_distinct() && self.costs_valid()
    }

    /// TLA+ `BudgetConsistency`.
    pub open spec fn budget_consistency(&self) -> bool {
        &&& self.budget.safety_invariant()
        &&& self.budget.reserved == 0
        &&& self.budget.pending_eviction == 0
        &&& self.budget.allocated as int
            == cost_sum_to(self.registry.entries@, self.registry.entries.len() as int)
    }

    /// `n ∈ accepted`.
    pub open spec fn contains(&self, n: u64) -> bool {
        self.registry.contains_key(n)
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the empty snapshot: nothing accepted, full budget remaining.
    /// Realises the TLA+ `Init` predicate and establishes both invariants.
    pub fn new(capacity: u64, num_nodes: u64) -> (s: AllocationSnapshot)
        ensures
            s.num_nodes == num_nodes,
            s.registry.entries@.len() == 0,
            s.budget.capacity == capacity,
            s.budget.allocated == 0,
            s.budget.reserved == 0,
            s.budget.pending_eviction == 0,
            s.type_invariant(),
            s.budget_consistency(),
    {
        AllocationSnapshot {
            num_nodes,
            registry: crate::primitives::resource_registry::ResourceRegistry::new(),
            budget: crate::primitives::budget::Budget::new(capacity),
        }
    }

    // ── Membership (executable) ─────────────────────────────────────────

    /// Executable membership test; links to the `contains` spec so callers can
    /// discharge the `n ∉ accepted` precondition of `accept_node`.
    pub fn contains_exec(&self, n: u64) -> (b: bool)
        requires self.registry.unique_mapping(),
        ensures
            b == self.contains(n),
    {
        match self.registry.lookup(n) {
            Some(_) => true,
            None => false,
        }
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
            old(self).budget.used() + node_cost as int <= old(self).budget.capacity as int,
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).registry.entries@
                == old(self).registry.entries@.push((n, node_cost)),
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).budget.allocated == old(self).budget.allocated + node_cost,
            final(self).contains(n),
            final(self).type_invariant(),
            final(self).budget_consistency(),
    {
        let _accepted = self.budget.try_allocate(node_cost);
        assert(_accepted);
        let ghost prior_entries = self.registry.entries@;
        self.registry.register(n, node_cost);
        proof { cost_sum_push(prior_entries, n, node_cost); }
        // Re-establish the set invariant: the pushed element n was absent
        // (precondition) and is a valid node, so distinctness and the subset
        // bound both carry to the extended sequence.
        assert(self.contains(n)) by {
            assert(self.registry.maps_to(n, node_cost));
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
        s.budget.capacity == capacity,
        s.num_nodes == num_nodes,
        s.registry.entries@ == capture_entries_to(
            capacity,
            num_nodes,
            nodes@,
            costs@,
            nodes@.len() as int,
        ),
        s.budget.allocated as int
            == cost_sum_to(s.registry.entries@, s.registry.entries@.len() as int),
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
            s.budget.capacity == capacity,
            s.num_nodes == num_nodes,
            s.registry.entries@ == capture_entries_to(
                capacity,
                num_nodes,
                nodes@,
                costs@,
                i as int,
            ),
            s.type_invariant(),
            s.budget_consistency(),
        decreases n_reqs - i,
    {
        let n = nodes[i];
        let c = costs[i];
        let available = s.budget.available();
        if n < num_nodes && 1 <= c && c <= available && !s.contains_exec(n) {
            s.accept_node(n, c);
        }
        assert(s.registry.entries@ == capture_entries_to(
            capacity,
            num_nodes,
            nodes@,
            costs@,
            i as int + 1,
        ));
        i = i + 1;
    }
    s
}

}
