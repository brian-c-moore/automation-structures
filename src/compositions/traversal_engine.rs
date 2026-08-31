// RelationshipGraph + Budget + connective-owned TraversalEngine composition.
//
// This is the Rust realization of TraversalEngineFromGraphBudget.tla:
// RelationshipGraph owns topology, Budget owns capacity accounting, Marker owns
// per-node visited state, Accumulator owns accepted output, and Buffer owns the
// pending frontier. Remaining budget and all public sets are projections.

use vstd::prelude::*;

use crate::compositions::relationship_graph::RelationshipGraph;
use crate::connectives::accumulator::Accumulator;
use crate::connectives::buffer::Buffer;
use crate::connectives::marker::Marker;
use crate::primitives::budget::Budget;

verus! {

/// The fixed cost used by the retained TraversalEngine model.
pub const NODE_COST: u64 = 2;

/// Budgeted traversal assembled from reusable structures and connective owners.
pub struct TraversalEngine {
    /// Number of nodes in the fixed universe.
    pub num_nodes: usize,
    /// Root node admitted into the initial frontier.
    pub root: usize,
    /// Relationship owner.
    pub graph: RelationshipGraph,
    /// Traversal-cost owner.
    pub budget: Budget,
    /// Per-node visited markers.
    pub visited: Vec<Marker>,
    /// Owner of accepted traversal results.
    pub accepted: Accumulator<usize>,
    /// Frontier owner.
    pub queue: Buffer<usize>,
}

impl TraversalEngine {
    /// Whether every retained node identifier is below `num_nodes`.
    pub open spec fn all_valid(values: Seq<usize>, num_nodes: usize) -> bool {
        forall|index: int| 0 <= index < values.len() ==>
            #[trigger] values[index] < num_nodes
    }

    /// Whether `node` occurs in the accepted-result owner.
    pub open spec fn accepted_contains_spec(&self, node: usize) -> bool {
        crate::connectives::buffer::contains_value(self.accepted.accumulated@, node)
    }

    /// Whether `node` occurs in the frontier owner.
    pub open spec fn queue_contains_spec(&self, node: usize) -> bool {
        crate::connectives::buffer::contains_value(self.queue.values@, node)
    }

    /// Whether the marker owner records `node` as visited.
    pub open spec fn visited_contains_spec(&self, node: usize) -> bool {
        node < self.visited.len() && self.visited@[node as int].marked
    }

    /// Graph edges loaded through RelationshipGraph are exactly the target star.
    pub open spec fn full_topology(&self) -> bool {
        forall|source: usize, target: usize|
            source < self.num_nodes && target < self.num_nodes ==>
                #[trigger] self.graph.edge_proj(source, target)
                    == (source == self.root && target != self.root)
    }

    /// Whether the graph contains the required prefix of the configured topology.
    pub open spec fn partial_topology(
        graph: &RelationshipGraph,
        root: usize,
        loaded_targets: usize,
    ) -> bool {
        forall|source: usize, target: usize|
            source < graph.num_nodes && target < graph.num_nodes ==>
                #[trigger] graph.edge_proj(source, target)
                    == (source == root && target < loaded_targets && target != root)
    }

    /// Before the root is visited, it is the only possible frontier member.
    pub open spec fn root_frontier_gate(&self) -> bool {
        !self.visited@[self.root as int].marked ==>
            forall|node: usize| #[trigger] self.queue_contains_spec(node) ==> node == self.root
    }

    /// Whether every accepted node is valid and marked as visited.
    pub open spec fn accepted_subset_visited(&self) -> bool {
        forall|node: usize| #[trigger] self.accepted_contains_spec(node) ==>
            node < self.num_nodes && self.visited_contains_spec(node)
    }

    /// Whether the traversal budget is safe and has no transitional holdings.
    pub open spec fn budget_invariant(&self) -> bool {
        &&& self.budget.safety_invariant()
        &&& self.budget.reserved == 0
        &&& self.budget.pending_eviction == 0
    }

    /// Whether every component owner and retained domain value is well formed.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.root < self.num_nodes
        &&& self.graph.num_nodes == self.num_nodes
        &&& self.graph.max_weight == 0
        &&& self.graph.inv()
        &&& self.full_topology()
        &&& self.visited@.len() == self.num_nodes
        &&& self.queue.well_formed()
        &&& self.queue.capacity == self.num_nodes
        &&& Self::all_valid(self.queue.values@, self.num_nodes)
        &&& crate::connectives::buffer::all_distinct(self.queue.values@)
        &&& self.accepted.well_formed()
        &&& self.accepted.pending@.len() == 0
        &&& Self::all_valid(self.accepted.accumulated@, self.num_nodes)
        &&& crate::connectives::buffer::all_distinct(self.accepted.accumulated@)
    }

    /// Whether all component and cross-component traversal obligations hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.budget_invariant()
        &&& self.accepted_subset_visited()
        &&& self.root_frontier_gate()
    }

    /// Expose the composition facts needed by checked facades and actions.
    pub proof fn expose(&self)
        requires self.inv(),
        ensures
            self.type_invariant(),
            self.budget_invariant(),
            self.accepted_subset_visited(),
            self.root_frontier_gate(),
            self.root < self.num_nodes,
            self.visited@.len() == self.num_nodes,
            self.full_topology(),
            self.queue.well_formed(),
            self.accepted.well_formed(),
            self.accepted.pending@.len() == 0,
            crate::connectives::buffer::all_distinct(self.queue.values@),
            Self::all_valid(self.queue.values@, self.num_nodes),
            crate::connectives::buffer::all_distinct(self.accepted.accumulated@),
            Self::all_valid(self.accepted.accumulated@, self.num_nodes),
            forall|candidate: usize|
                #[trigger] self.accepted_contains_spec(candidate) ==>
                    candidate < self.num_nodes && self.visited_contains_spec(candidate),
            !self.visited@[self.root as int].marked ==>
                forall|candidate: usize| #[trigger] self.queue_contains_spec(candidate) ==>
                    candidate == self.root,
    {
        reveal(TraversalEngine::inv);
        reveal(TraversalEngine::type_invariant);
        reveal(TraversalEngine::accepted_subset_visited);
        reveal(TraversalEngine::root_frontier_gate);
    }

    /// Load the target graph through RelationshipGraph, then initialize the connective owners.
    pub fn new(num_nodes: usize, root: usize, max_budget: u64) -> (engine: TraversalEngine)
        requires root < num_nodes,
        ensures
            engine.inv(),
            engine.num_nodes == num_nodes,
            engine.root == root,
            engine.budget.capacity == max_budget,
            engine.budget.allocated == 0,
            engine.queue.values@ == seq![root],
            engine.accepted.accumulated@.len() == 0,
            forall|node: int| 0 <= node < engine.visited@.len() ==>
                !#[trigger] engine.visited@[node].marked,
    {
        let mut graph = RelationshipGraph::new(num_nodes, 0);
        assert(Self::partial_topology(&graph, root, 0)) by {
            assert forall|source: usize, target: usize|
                source < graph.num_nodes && target < graph.num_nodes implies
                    #[trigger] graph.edge_proj(source, target)
                        == (source == root && target < 0 && target != root) by {
                if graph.edge_proj(source, target) {
                    let entry = choose|entry: int|
                        0 <= entry < graph.registry.entries@.len()
                            && graph.registry.entries@[entry].0.0 == source
                            && graph.registry.entries@[entry].0.1 == target;
                    assert(false);
                }
            }
        }
        let mut target: usize = 0;
        while target < num_nodes
            invariant
                root < num_nodes,
                graph.num_nodes == num_nodes,
                graph.max_weight == 0,
                graph.inv(),
                target <= num_nodes,
                Self::partial_topology(&graph, root, target),
            decreases num_nodes - target,
        {
            if target != root {
                proof {
                    graph.exact_edge_implies_pair(root, target, 0);
                    assert(!graph.edge_proj(root, target));
                    assert(!graph.exact_edge(root, target, 0));
                }
                let added = graph.add_edge(root, target, 0);
                assert(added);
                let _ = added;
            }
            let next_target = target + 1;
            assert(Self::partial_topology(&graph, root, next_target)) by {
                assert forall|source: usize, destination: usize|
                    source < graph.num_nodes && destination < graph.num_nodes implies
                        #[trigger] graph.edge_proj(source, destination)
                            == (source == root
                                && destination < next_target
                                && destination != root) by {
                    if target == root {
                        if destination != root {
                            if destination < next_target {
                                assert(destination <= target);
                                assert(destination < target);
                            }
                            if destination < target {
                                assert(destination < next_target);
                            }
                        }
                    }
                }
            }
            target = next_target;
        }

        let mut visited: Vec<Marker> = Vec::new();
        let mut node: usize = 0;
        while node < num_nodes
            invariant
                node <= num_nodes,
                visited@.len() == node,
                forall|index: int| 0 <= index < visited@.len() ==>
                    !#[trigger] visited@[index].marked,
            decreases num_nodes - node,
        {
            visited.push(Marker::new(false));
            node = node + 1;
        }

        let budget = Budget::new(max_budget);
        let accepted = Accumulator::from_accumulated(Vec::new());
        let mut queue = Buffer::new(num_nodes);
        let queued = queue.push(root);
        let _ = queued;
        assert(queue.values@ == seq![root]);
        assert(crate::connectives::buffer::all_distinct(queue.values@));

        let engine = TraversalEngine {
            num_nodes,
            root,
            graph,
            budget,
            visited,
            accepted,
            queue,
        };
        assert(engine.full_topology()) by {
            assert forall|source: usize, destination: usize|
                source < engine.num_nodes && destination < engine.num_nodes implies
                    #[trigger] engine.graph.edge_proj(source, destination)
                        == (source == engine.root && destination != engine.root) by {
            }
        }
        assert(engine.accepted_subset_visited());
        assert(engine.root_frontier_gate());
        engine
    }

    /// Remaining capacity projected from the Budget owner.
    pub fn budget_remaining(&self) -> (remaining: u64)
        requires self.budget_invariant(),
        ensures remaining as int == self.budget.capacity as int - self.budget.allocated as int,
    {
        self.budget.available()
    }

    /// Whether the frontier currently retains `node`.
    pub fn queue_contains(&self, node: usize) -> (present: bool)
        ensures present == self.queue_contains_spec(node),
    {
        self.queue.contains(node)
    }

    /// Whether `node` has been visited.
    pub fn visited_contains(&self, node: usize) -> (present: bool)
        ensures present == self.visited_contains_spec(node),
    {
        if node >= self.visited.len() { false } else { self.visited[node].is_marked() }
    }

    /// Whether `node` was accepted into the result.
    pub fn accepted_contains(&self, node: usize) -> (present: bool)
        ensures present == self.accepted_contains_spec(node),
    {
        crate::connectives::buffer::retained_contains(&self.accepted.accumulated, node)
    }

    /// Whether visiting `node` is currently enabled.
    pub fn can_visit(&self, node: usize) -> (enabled: bool)
        ensures enabled == (node < self.num_nodes
            && self.queue_contains_spec(node)
            && !self.visited_contains_spec(node)),
    {
        node < self.num_nodes && self.queue_contains(node) && !self.visited_contains(node)
    }

    /// Whether skipping `node` is currently enabled.
    pub fn can_skip(&self, node: usize) -> (enabled: bool)
        ensures enabled == (node < self.num_nodes && self.queue_contains_spec(node)),
    {
        node < self.num_nodes && self.queue_contains(node)
    }

    /// Whether terminal stuttering is enabled.
    pub fn can_terminate(&self) -> (enabled: bool)
        ensures enabled == (self.queue.values@.len() == 0),
    {
        self.queue.is_empty()
    }

    /// Number of set visited markers, derived without a duplicate counter.
    pub fn visited_count(&self) -> (count: usize) {
        let mut count: usize = 0;
        let mut index: usize = 0;
        while index < self.visited.len()
            invariant index <= self.visited.len(), count <= index,
            decreases self.visited.len() - index,
        {
            if self.visited[index].is_marked() {
                count = count + 1;
            }
            index = index + 1;
        }
        count
    }

    fn enqueue_star_children(
        graph: &RelationshipGraph,
        queue: &mut Buffer<usize>,
        root: usize,
        num_nodes: usize,
    )
        requires
            root < num_nodes,
            graph.num_nodes == num_nodes,
            graph.inv(),
            forall|source: usize, target: usize|
                source < num_nodes && target < num_nodes ==>
                    #[trigger] graph.edge_proj(source, target)
                        == (source == root && target != root),
            old(queue).well_formed(),
            old(queue).capacity == num_nodes,
            old(queue).values@.len() == 0,
        ensures
            final(queue).well_formed(),
            final(queue).capacity == old(queue).capacity,
            crate::connectives::buffer::all_distinct(final(queue).values@),
            Self::all_valid(final(queue).values@, num_nodes),
            forall|candidate: usize|
                #[trigger] crate::connectives::buffer::contains_value(
                    final(queue).values@,
                    candidate,
                ) == (candidate < num_nodes && candidate != root),
    {
        let mut target: usize = 0;
        while target < num_nodes
            invariant
                root < num_nodes,
                graph.num_nodes == num_nodes,
                graph.inv(),
                forall|source: usize, destination: usize|
                    source < num_nodes && destination < num_nodes ==>
                        #[trigger] graph.edge_proj(source, destination)
                            == (source == root && destination != root),
                target <= num_nodes,
                queue.well_formed(),
                queue.capacity == num_nodes,
                crate::connectives::buffer::all_distinct(queue.values@),
                Self::all_valid(queue.values@, num_nodes),
                queue.values@.len() <= target,
                forall|candidate: usize|
                    #[trigger] crate::connectives::buffer::contains_value(
                        queue.values@,
                        candidate,
                    ) == (candidate < target && candidate != root),
            decreases num_nodes - target,
        {
            let ghost before_queue = queue.values@;
            let edge = graph.contains_pair(root, target);
            assert(edge == (target != root));
            if edge {
                assert(!crate::connectives::buffer::contains_value(before_queue, target));
                assert(queue.values@.len() < queue.capacity);
                let queued = queue.push_unique(target);
                assert(queued);
                let _ = queued;
                assert(Self::all_valid(queue.values@, num_nodes)) by {
                    assert forall|index: int| 0 <= index < queue.values@.len()
                        implies #[trigger] queue.values@[index] < num_nodes by {
                        if index == before_queue.len() {
                            assert(queue.values@[index] == target);
                        } else {
                            assert(index < before_queue.len());
                            assert(queue.values@[index] == before_queue[index]);
                        }
                    }
                }
            }
            let next_target = target + 1;
            assert forall|candidate: usize|
                #[trigger] crate::connectives::buffer::contains_value(
                    queue.values@,
                    candidate,
                ) == (candidate < next_target && candidate != root) by {
                if edge {
                    crate::connectives::buffer::lemma_push_contains(
                        before_queue,
                        target,
                        candidate,
                    );
                } else {
                    assert(queue.values@ == before_queue);
                }
                if target == root && candidate != root {
                    if candidate < next_target {
                        assert(candidate <= target);
                        assert(candidate < target);
                    }
                }
            }
            target = next_target;
        }
    }

    /// Visit one queued node and atomically couple acceptance to Budget allocation.
    pub fn visit_node(&mut self, node: usize)
        requires
            old(self).inv(),
            node < old(self).num_nodes,
            old(self).queue_contains_spec(node),
            !old(self).visited_contains_spec(node),
        ensures
            final(self).inv(),
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).graph.registry.entries@ == old(self).graph.registry.entries@,
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).budget.reserved == old(self).budget.reserved,
            final(self).budget.pending_eviction == old(self).budget.pending_eviction,
            final(self).budget.allocated as int
                == if old(self).budget.allocated as int + NODE_COST as int
                        <= old(self).budget.capacity as int {
                    old(self).budget.allocated as int + NODE_COST as int
                } else {
                    old(self).budget.allocated as int
                },
            forall|candidate: usize|
                candidate < old(self).num_nodes ==>
                    #[trigger] final(self).visited_contains_spec(candidate)
                        == (old(self).visited_contains_spec(candidate) || candidate == node),
            forall|candidate: usize|
                #[trigger] final(self).accepted_contains_spec(candidate)
                    == (old(self).accepted_contains_spec(candidate)
                        || (old(self).budget.allocated as int + NODE_COST as int
                                <= old(self).budget.capacity as int
                            && candidate == node)),
            forall|candidate: usize|
                #[trigger] final(self).queue_contains_spec(candidate)
                    == if old(self).budget.allocated as int + NODE_COST as int
                            <= old(self).budget.capacity as int
                        && node == old(self).root {
                        (old(self).queue_contains_spec(candidate) && candidate != node)
                            || (candidate < old(self).num_nodes
                                && candidate != old(self).root)
                    } else {
                        old(self).queue_contains_spec(candidate) && candidate != node
                    },
    {
        proof { self.expose(); }
        let num_nodes = self.num_nodes;
        let root = self.root;
        let initial_allocated = self.budget.allocated;
        let budget_capacity = self.budget.capacity;
        let _ = (initial_allocated, budget_capacity);
        let ghost old_accepted = self.accepted.accumulated@;
        let ghost old_visited = self.visited@;
        let ghost old_queue = self.queue.values@;
        proof {
            reveal(TraversalEngine::accepted_contains_spec);
            reveal(TraversalEngine::queue_contains_spec);
            reveal(TraversalEngine::visited_contains_spec);
            assert forall|candidate: usize|
                crate::connectives::buffer::contains_value(old_accepted, candidate) implies
                    candidate < self.num_nodes && old_visited[candidate as int].marked by {
                assert(self.accepted_contains_spec(candidate));
                assert(self.visited_contains_spec(candidate));
            }
            assert(!old_visited[node as int].marked);
            assert(crate::connectives::buffer::contains_value(old_queue, node));
            assert(!old_visited[root as int].marked ==> forall|candidate: usize|
                #[trigger] crate::connectives::buffer::contains_value(old_queue, candidate)
                    ==> candidate == root) by {
                if !old_visited[root as int].marked {
                    assert(!self.visited@[root as int].marked);
                    assert forall|candidate: usize|
                        #[trigger] crate::connectives::buffer::contains_value(
                            old_queue,
                            candidate,
                        ) implies candidate == root by {
                        assert(self.queue_contains_spec(candidate));
                    }
                }
            }
            assert(self.full_topology());
            assert(Self::all_valid(old_queue, num_nodes));
            assert(crate::connectives::buffer::all_distinct(old_queue));
            assert(Self::all_valid(old_accepted, num_nodes));
            assert(crate::connectives::buffer::all_distinct(old_accepted));
        }

        let removed = self.queue.remove_value(node);
        assert(removed);
        let _ = removed;
        let ghost queue_after_removal = self.queue.values@;

        let mut marker = self.visited[node];
        let changed = marker.set();
        assert(changed);
        let _ = changed;
        self.visited.set(node, marker);
        assert(self.visited@ == old_visited.update(node as int, marker));
        assert forall|candidate: usize| candidate < self.num_nodes implies
            #[trigger] self.visited_contains_spec(candidate)
                == (candidate == node || old_visited[candidate as int].marked) by {
        }

        let accepted = self.budget.try_allocate(NODE_COST);
        assert(accepted == (initial_allocated as int + NODE_COST as int
            <= budget_capacity as int));
        if accepted {
            assert(!crate::connectives::buffer::contains_value(old_accepted, node)) by {
            if crate::connectives::buffer::contains_value(old_accepted, node) {
                    assert(old_visited[node as int].marked);
                }
            }
            self.accepted.append(node);
            assert(self.accepted.accumulated@ == old_accepted.push(node));
            proof {
                crate::connectives::buffer::lemma_push_contains(old_accepted, node, node);
                assert forall|candidate: usize|
                    #[trigger] crate::connectives::buffer::contains_value(
                        self.accepted.accumulated@,
                        candidate,
                    ) == (crate::connectives::buffer::contains_value(
                        old_accepted,
                        candidate,
                    ) || candidate == node) by {
                    crate::connectives::buffer::lemma_push_contains(
                        old_accepted,
                        node,
                        candidate,
                    );
                }
            }
            assert(crate::connectives::buffer::all_distinct(self.accepted.accumulated@)) by {
                assert forall|left: int, right: int|
                    0 <= left < self.accepted.accumulated@.len()
                        && 0 <= right < self.accepted.accumulated@.len()
                        && left != right
                    implies #[trigger] self.accepted.accumulated@[left]
                        != #[trigger] self.accepted.accumulated@[right] by {
                    if left < old_accepted.len() && right < old_accepted.len() {
                    } else if left == old_accepted.len() && right < old_accepted.len() {
                        crate::connectives::buffer::indexed_value_contained(
                            old_accepted,
                            right,
                        );
                        assert(crate::connectives::buffer::contains_value(
                            old_accepted,
                            old_accepted[right],
                        ));
                    } else if right == old_accepted.len() && left < old_accepted.len() {
                        crate::connectives::buffer::indexed_value_contained(
                            old_accepted,
                            left,
                        );
                        assert(crate::connectives::buffer::contains_value(
                            old_accepted,
                            old_accepted[left],
                        ));
                    }
                }
            }

            if node == root {
                assert(self.queue.values@.len() == 0) by {
                    if self.queue.values@.len() > 0 {
                        let queued = self.queue.values@[0];
                        crate::connectives::buffer::indexed_value_contained(
                            self.queue.values@,
                            0,
                        );
                        assert(self.queue_contains_spec(queued));
                        assert(crate::connectives::buffer::contains_value(old_queue, queued));
                        assert(queued == root);
                        assert(!self.queue_contains_spec(root));
                    }
                }
                Self::enqueue_star_children(
                    &self.graph,
                    &mut self.queue,
                    root,
                    num_nodes,
                );
            }
        } else {
            assert(self.accepted.accumulated@ == old_accepted);
        }

        assert(Self::all_valid(self.accepted.accumulated@, self.num_nodes)) by {
            assert forall|index: int| 0 <= index < self.accepted.accumulated@.len()
                implies #[trigger] self.accepted.accumulated@[index] < self.num_nodes by {
                if accepted {
                    if index == old_accepted.len() {
                        assert(self.accepted.accumulated@[index] == node);
                    } else {
                        assert(index < old_accepted.len());
                        assert(self.accepted.accumulated@[index] == old_accepted[index]);
                    }
                }
            }
        }
        assert forall|candidate: usize|
            #[trigger] self.accepted_contains_spec(candidate)
                == (crate::connectives::buffer::contains_value(old_accepted, candidate)
                    || (accepted && candidate == node)) by {
            reveal(TraversalEngine::accepted_contains_spec);
            if accepted {
                crate::connectives::buffer::lemma_push_contains(
                    old_accepted,
                    node,
                    candidate,
                );
            }
        }
        assert(self.accepted_subset_visited()) by {
            assert forall|candidate: usize| #[trigger] self.accepted_contains_spec(candidate)
                implies candidate < self.num_nodes && self.visited_contains_spec(candidate) by {
                if accepted && candidate == node {
                } else {
                    assert(crate::connectives::buffer::contains_value(old_accepted, candidate));
                    assert(old_visited[candidate as int].marked);
                }
            }
        }
        assert forall|candidate: usize|
            #[trigger] self.queue_contains_spec(candidate)
                == if accepted && node == root {
                    (crate::connectives::buffer::contains_value(old_queue, candidate)
                        && candidate != node)
                        || (candidate < num_nodes && candidate != root)
                } else {
                    crate::connectives::buffer::contains_value(old_queue, candidate)
                        && candidate != node
                } by {
            reveal(TraversalEngine::queue_contains_spec);
            if accepted && node == root {
                assert(self.queue_contains_spec(candidate)
                    == (candidate < num_nodes && candidate != root));
            } else {
                assert(self.queue.values@ == queue_after_removal);
            }
        }
        assert(self.visited@[root as int].marked) by {
            if old_visited[root as int].marked {
                if node != root {
                    assert(self.visited@[root as int] == old_visited[root as int]);
                }
            } else {
                assert(node == root) by {
                    assert(crate::connectives::buffer::contains_value(old_queue, node));
                }
            }
        }
        assert(self.root_frontier_gate());
        assert(self.num_nodes == num_nodes);
        assert(self.root == root);
        assert(Self::all_valid(self.queue.values@, self.num_nodes)) by {
            assert forall|index: int| 0 <= index < self.queue.values@.len()
                implies #[trigger] self.queue.values@[index] < self.num_nodes by {
                crate::connectives::buffer::indexed_value_contained(
                    self.queue.values@,
                    index,
                );
                let candidate = self.queue.values@[index];
                if !accepted || node != root {
                    assert(crate::connectives::buffer::contains_value(old_queue, candidate));
                    let old_index = choose|old_index: int|
                        0 <= old_index < old_queue.len() && old_queue[old_index] == candidate;
                    assert(old_queue[old_index] < num_nodes);
                }
            }
        }
        assert(self.type_invariant()) by {
            reveal(TraversalEngine::type_invariant);
        }
        assert(self.budget_invariant()) by {
            reveal(TraversalEngine::budget_invariant);
        }
        assert(self.inv()) by {
            reveal(TraversalEngine::inv);
        }
    }

    /// Remove one queued node without visiting or charging it.
    pub fn skip(&mut self, node: usize)
        requires
            old(self).inv(),
            node < old(self).num_nodes,
            old(self).queue_contains_spec(node),
        ensures
            final(self).inv(),
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).graph.registry.entries@ == old(self).graph.registry.entries@,
            final(self).budget == old(self).budget,
            final(self).visited@ == old(self).visited@,
            final(self).accepted.accumulated@ == old(self).accepted.accumulated@,
            forall|candidate: usize| #[trigger] final(self).queue_contains_spec(candidate)
                == (old(self).queue_contains_spec(candidate) && candidate != node),
    {
        proof { self.expose(); }
        let root = self.root;
        let num_nodes = self.num_nodes;
        let _ = (root, num_nodes);
        let ghost old_queue = self.queue.values@;
        let ghost old_visited = self.visited@;
        let ghost old_accepted = self.accepted.accumulated@;
        proof {
            reveal(TraversalEngine::queue_contains_spec);
            reveal(TraversalEngine::accepted_contains_spec);
            reveal(TraversalEngine::visited_contains_spec);
            assert(!old_visited[root as int].marked ==> forall|candidate: usize|
                #[trigger] crate::connectives::buffer::contains_value(old_queue, candidate)
                    ==> candidate == root) by {
                if !old_visited[root as int].marked {
                    assert(!self.visited@[root as int].marked);
                    assert forall|candidate: usize|
                        #[trigger] crate::connectives::buffer::contains_value(
                            old_queue,
                            candidate,
                        ) implies candidate == root by {
                        assert(self.queue_contains_spec(candidate));
                    }
                }
            }
            assert(Self::all_valid(old_queue, num_nodes));
            assert forall|candidate: usize|
                crate::connectives::buffer::contains_value(old_accepted, candidate) implies
                    candidate < num_nodes && old_visited[candidate as int].marked by {
                assert(self.accepted_contains_spec(candidate));
                assert(self.visited_contains_spec(candidate));
            }
        }
        let removed = self.queue.remove_value(node);
        assert(removed);
        let _ = removed;
        assert(self.root_frontier_gate()) by {
            if !self.visited@[root as int].marked {
                assert forall|candidate: usize| #[trigger] self.queue_contains_spec(candidate)
                    implies candidate == root by {
                    assert(crate::connectives::buffer::contains_value(old_queue, candidate));
                }
            }
        }
        assert(Self::all_valid(self.queue.values@, self.num_nodes)) by {
            assert forall|index: int| 0 <= index < self.queue.values@.len()
                implies #[trigger] self.queue.values@[index] < self.num_nodes by {
                crate::connectives::buffer::indexed_value_contained(
                    self.queue.values@,
                    index,
                );
                let candidate = self.queue.values@[index];
                assert(crate::connectives::buffer::contains_value(old_queue, candidate));
                let old_index = choose|old_index: int|
                    0 <= old_index < old_queue.len() && old_queue[old_index] == candidate;
                assert(old_queue[old_index] < num_nodes);
            }
        }
        assert(self.type_invariant()) by {
            reveal(TraversalEngine::type_invariant);
        }
        assert(self.budget_invariant());
        assert(self.accepted.accumulated@ == old_accepted);
        assert(self.visited@ == old_visited);
        assert(self.accepted_subset_visited()) by {
            assert forall|candidate: usize| #[trigger] self.accepted_contains_spec(candidate)
                implies candidate < self.num_nodes && self.visited_contains_spec(candidate) by {
                assert(crate::connectives::buffer::contains_value(old_accepted, candidate));
                assert(old_visited[candidate as int].marked);
            }
        }
        assert(self.inv()) by {
            reveal(TraversalEngine::inv);
        }
    }

    /// Enabled-at-empty traversal termination is an exact stutter.
    pub fn terminate(&mut self)
        requires
            old(self).inv(),
            old(self).queue.values@.len() == 0,
        ensures final(self).inv(), *final(self) == *old(self),
    {
    }
}

}
