// TraversalBudgetComposition theorem facade over the TraversalEngine assembly.
//
// TraversalEngine owns the graph, budget, markers, accepted accumulator, and frontier buffer.
// This type adds no state: `total_cost` is Budget.allocated and `budget_remaining` is the
// remaining-capacity projection proved by the composition theorem.

use vstd::prelude::*;

use crate::compositions::traversal_engine::TraversalEngine;

verus! {

/// The TraversalBudgetComposition theorem viewed through its state owner.
pub struct TraversalBudgetComposition {
    /// Traversal assembly that owns all executable state.
    pub traversal: TraversalEngine,
}

impl TraversalBudgetComposition {
    /// Whether the wrapped traversal owner is locally well formed.
    pub open spec fn type_invariant(&self) -> bool {
        self.traversal.inv()
    }

    /// Whether accepted nodes and charged cost agree through the wrapped owner.
    pub open spec fn composition_invariant(&self) -> bool {
        &&& self.traversal.budget.allocated <= self.traversal.budget.capacity
        &&& self.traversal.budget.allocated as int
            + (self.traversal.budget.capacity as int
                - self.traversal.budget.allocated as int)
                == self.traversal.budget.capacity as int
    }

    /// Whether every accepted node has also been visited.
    pub open spec fn accepted_subset_visited(&self) -> bool {
        self.traversal.accepted_subset_visited()
    }

    /// Whether the wrapper preserves all traversal and budget obligations.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.composition_invariant()
            && self.accepted_subset_visited()
    }

    /// Construct the zero-additional-state theorem facade.
    pub fn new(
        num_nodes: usize,
        root: usize,
        max_budget: u64,
    ) -> (composition: TraversalBudgetComposition)
        requires root < num_nodes,
        ensures
            composition.inv(),
            composition.traversal.num_nodes == num_nodes,
            composition.traversal.root == root,
            composition.traversal.budget.capacity == max_budget,
            composition.traversal.budget.allocated == 0,
            composition.traversal.queue.values@ == seq![root],
            composition.traversal.accepted.original@.len() == 0,
            composition.traversal.accepted.accumulated@.len() == 0,
            composition.traversal.accepted.pending@.len() == 0,
            forall|node: int| 0 <= node < composition.traversal.visited@.len() ==>
                !#[trigger] composition.traversal.visited@[node].marked,
    {
        let traversal = TraversalEngine::new(num_nodes, root, max_budget);
        TraversalBudgetComposition { traversal }
    }

    /// Total traversal cost committed by the budget.
    pub fn total_cost(&self) -> (cost: u64)
        ensures cost == self.traversal.budget.allocated,
    {
        self.traversal.budget.allocated
    }

    /// Remaining capacity projected from the budget.
    pub fn budget_remaining(&self) -> (remaining: u64)
        requires self.traversal.budget_invariant(),
        ensures remaining as int
            == self.traversal.budget.capacity as int
                - self.traversal.budget.allocated as int,
    {
        self.traversal.budget_remaining()
    }

    /// Whether the traversal has visited `node`.
    pub fn visited_contains(&self, node: usize) -> (present: bool)
        ensures present == self.traversal.visited_contains_spec(node),
    {
        self.traversal.visited_contains(node)
    }

    /// Whether the traversal accepted `node`.
    pub fn accepted_contains(&self, node: usize) -> (present: bool)
        ensures present == self.traversal.accepted_contains_spec(node),
    {
        self.traversal.accepted_contains(node)
    }

    /// Whether the frontier retains `node`.
    pub fn queue_contains(&self, node: usize) -> (present: bool)
        ensures present == self.traversal.queue_contains_spec(node),
    {
        self.traversal.queue_contains(node)
    }

    /// The affordable branch of TraversalEngine.VisitNode.
    pub fn visit_and_accept(&mut self, node: usize)
        requires
            old(self).inv(),
            node < old(self).traversal.num_nodes,
            old(self).traversal.queue_contains_spec(node),
            !old(self).traversal.visited_contains_spec(node),
            old(self).traversal.budget.allocated as int
                + crate::compositions::traversal_engine::NODE_COST as int
                <= old(self).traversal.budget.capacity as int,
        ensures
            final(self).inv(),
            final(self).traversal.num_nodes == old(self).traversal.num_nodes,
            final(self).traversal.root == old(self).traversal.root,
            final(self).traversal.graph == old(self).traversal.graph,
            final(self).traversal.budget.capacity == old(self).traversal.budget.capacity,
            final(self).traversal.budget.reserved == old(self).traversal.budget.reserved,
            final(self).traversal.budget.pending_eviction
                == old(self).traversal.budget.pending_eviction,
            final(self).traversal.budget.allocated
                == old(self).traversal.budget.allocated
                    + crate::compositions::traversal_engine::NODE_COST,
            final(self).traversal.accepted.original@
                == old(self).traversal.accepted.original@.push(node),
            final(self).traversal.accepted.accumulated@
                == old(self).traversal.accepted.accumulated@.push(node),
            final(self).traversal.accepted.pending@
                == old(self).traversal.accepted.pending@,
            final(self).traversal.accepted_contains_spec(node),
            final(self).traversal.visited_contains_spec(node),
            node == old(self).traversal.root ==> {
                &&& final(self).traversal.queue.values@.len()
                    == old(self).traversal.num_nodes - 1
                &&& forall|index: int|
                    0 <= index < final(self).traversal.queue.values@.len() ==>
                        #[trigger] final(self).traversal.queue.values@[index]
                            == if index < old(self).traversal.root as int {
                                index as usize
                            } else {
                                (index + 1) as usize
                            }
            },
            node != old(self).traversal.root ==> exists|index: int|
                0 <= index < old(self).traversal.queue.values@.len()
                    && old(self).traversal.queue.values@[index] == node
                    && final(self).traversal.queue.values@
                        == old(self).traversal.queue.values@.remove(index),
    {
        self.traversal.visit_node(node);
    }

    /// The unaffordable branch of TraversalEngine.VisitNode.
    pub fn skip_unaffordable(&mut self, node: usize)
        requires
            old(self).inv(),
            node < old(self).traversal.num_nodes,
            old(self).traversal.queue_contains_spec(node),
            !old(self).traversal.visited_contains_spec(node),
            old(self).traversal.budget.allocated as int
                + crate::compositions::traversal_engine::NODE_COST as int
                > old(self).traversal.budget.capacity as int,
        ensures
            final(self).inv(),
            final(self).traversal.num_nodes == old(self).traversal.num_nodes,
            final(self).traversal.root == old(self).traversal.root,
            final(self).traversal.graph == old(self).traversal.graph,
            final(self).traversal.budget == old(self).traversal.budget,
            final(self).traversal.accepted.original@
                == old(self).traversal.accepted.original@,
            final(self).traversal.accepted.accumulated@
                == old(self).traversal.accepted.accumulated@,
            final(self).traversal.accepted.pending@
                == old(self).traversal.accepted.pending@,
            final(self).traversal.budget.allocated
                == old(self).traversal.budget.allocated,
            !final(self).traversal.accepted_contains_spec(node),
            final(self).traversal.visited_contains_spec(node),
            exists|index: int|
                0 <= index < old(self).traversal.queue.values@.len()
                    && old(self).traversal.queue.values@[index] == node
                    && final(self).traversal.queue.values@
                        == old(self).traversal.queue.values@.remove(index),
    {
        self.traversal.visit_node(node);
    }

    /// Pure frontier removal through TraversalEngine.Skip.
    pub fn skip(&mut self, node: usize)
        requires
            old(self).inv(),
            node < old(self).traversal.num_nodes,
            old(self).traversal.queue_contains_spec(node),
        ensures
            final(self).inv(),
            final(self).traversal.num_nodes == old(self).traversal.num_nodes,
            final(self).traversal.root == old(self).traversal.root,
            final(self).traversal.graph == old(self).traversal.graph,
            !final(self).traversal.queue_contains_spec(node),
            final(self).traversal.budget == old(self).traversal.budget,
            final(self).traversal.visited@ == old(self).traversal.visited@,
            final(self).traversal.accepted == old(self).traversal.accepted,
            exists|index: int|
                0 <= index < old(self).traversal.queue.values@.len()
                    && old(self).traversal.queue.values@[index] == node
                    && final(self).traversal.queue.values@
                        == old(self).traversal.queue.values@.remove(index),
    {
        self.traversal.skip(node);
    }
}

}
