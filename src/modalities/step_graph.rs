//! Finite-index StepGraph execution carrier.

use crate::execution_api::StepState as StepGraphNodeState;
use vstd::prelude::*;

verus! {

/// Monotone rank of the shared StepGraph node-state vocabulary.
pub open spec fn state_rank(state: StepGraphNodeState) -> int {
    match state {
        StepGraphNodeState::NotReady => 0,
        StepGraphNodeState::Ready => 1,
        StepGraphNodeState::Running => 2,
        StepGraphNodeState::Complete => 3,
    }
}

/// Every node state is retained or advances monotonically.
pub open spec fn states_monotone(
    before: Seq<StepGraphNodeState>,
    after: Seq<StepGraphNodeState>,
) -> bool {
    &&& after.len() == before.len()
    &&& forall|i: int| 0 <= i < before.len() ==>
        state_rank(after[i]) >= state_rank(before[i])
}

/// Blocked-node release action over any faithful state carrier.
pub open spec fn become_ready_action(
    before: Seq<StepGraphNodeState>,
    after: Seq<StepGraphNodeState>,
    node: int,
    eligible: bool,
    accepted: bool,
) -> bool {
    let enabled = 0 <= node < before.len()
        && before[node] == StepGraphNodeState::NotReady
        && eligible;
    &&& accepted == enabled
    &&& after == if accepted {
        before.update(node, StepGraphNodeState::Ready)
    } else {
        before
    }
}

/// Ready-node start action over any faithful state carrier.
pub open spec fn start_running_action(
    before: Seq<StepGraphNodeState>,
    after: Seq<StepGraphNodeState>,
    node: int,
    selected: bool,
    accepted: bool,
) -> bool {
    let enabled = 0 <= node < before.len()
        && selected
        && before[node] == StepGraphNodeState::Ready;
    &&& accepted == enabled
    &&& after == if accepted {
        before.update(node, StepGraphNodeState::Running)
    } else {
        before
    }
}

/// Running-node completion action over any faithful state carrier.
pub open spec fn complete_node_action(
    before: Seq<StepGraphNodeState>,
    after: Seq<StepGraphNodeState>,
    node: int,
    selected: bool,
    accepted: bool,
) -> bool {
    let enabled = 0 <= node < before.len()
        && selected
        && before[node] == StepGraphNodeState::Running;
    &&& accepted == enabled
    &&& after == if accepted {
        before.update(node, StepGraphNodeState::Complete)
    } else {
        before
    }
}

/// Predecessor-governed step-graph owner.
pub struct StepGraph {
    /// Number of execution nodes.
    pub num_nodes: usize,
    /// Directed predecessor edges.
    pub edges: Vec<(usize, usize)>,
    /// Lifecycle state by node index.
    pub nstate: Vec<StepGraphNodeState>,
}

impl StepGraph {
    /// Whether every dependency edge names two valid, distinct nodes.
    pub open spec fn edges_valid(edges: Seq<(usize, usize)>, num_nodes: usize) -> bool {
        forall|i: int| 0 <= i < edges.len() ==>
            #[trigger] edges[i].0 < num_nodes && edges[i].1 < num_nodes
    }

    /// Whether the dependency edge sequence contains no duplicate edge.
    pub open spec fn edges_distinct(edges: Seq<(usize, usize)>) -> bool {
        forall|i: int, j: int|
            0 <= i < edges.len() && 0 <= j < edges.len() && i != j
                ==> #[trigger] edges[i] != #[trigger] edges[j]
    }

    /// Whether `node` has at least one incoming dependency edge.
    pub open spec fn has_predecessor_in(edges: Seq<(usize, usize)>, node: usize) -> bool {
        exists|i: int| 0 <= i < edges.len() && edges[i].1 == node
    }

    /// Whether every predecessor of `node` is complete in `states`.
    pub open spec fn predecessors_complete_in(
        edges: Seq<(usize, usize)>, states: Seq<StepGraphNodeState>, node: usize,
    ) -> bool {
        forall|i: int| 0 <= i < edges.len() && edges[i].1 == node
            ==> #[trigger] states[edges[i].0 as int] == StepGraphNodeState::Complete
    }

    /// Whether node states and dependency edges have valid shape and values.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.nstate@.len() == self.num_nodes
        &&& Self::edges_valid(self.edges@, self.num_nodes)
        &&& Self::edges_distinct(self.edges@)
    }

    /// Whether readiness agrees with predecessor completion.
    pub open spec fn eligibility_closed(&self) -> bool {
        forall|n: usize| n < self.num_nodes
            && #[trigger] self.nstate@[n as int] != StepGraphNodeState::NotReady
            ==> Self::predecessors_complete_in(self.edges@, self.nstate@, n)
    }

    /// Whether no node runs or completes before all predecessors complete.
    pub open spec fn no_run_before_predecessors(&self) -> bool {
        forall|n: usize| n < self.num_nodes
            && (#[trigger] self.nstate@[n as int] == StepGraphNodeState::Running
                || self.nstate@[n as int] == StepGraphNodeState::Complete)
            ==> Self::predecessors_complete_in(self.edges@, self.nstate@, n)
    }

    /// Whether all dependency-ordered execution obligations hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.eligibility_closed()
    }

    #[expect(clippy::ptr_arg, reason = "Verus sequence-view contracts are stated over Vec for StepGraph edges")]
    #[expect(clippy::indexing_slicing, reason = "Verus proves the predecessor cursor remains in bounds")]
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the predecessor cursor increment remains in bounds")]
    fn has_predecessor_exec(edges: &Vec<(usize, usize)>, node: usize) -> (b: bool)
        ensures b == Self::has_predecessor_in(edges@, node),
    {
        let mut i = 0;
        while i < edges.len()
            invariant
                i <= edges.len(),
                forall|k: int| 0 <= k < i ==> edges@[k].1 != node,
            decreases edges.len() - i,
        {
            if edges[i].1 == node {
                assert(Self::has_predecessor_in(edges@, node));
                return true;
            }
            i += 1;
        }
        false
    }

    #[expect(clippy::indexing_slicing, reason = "the type invariant and loop invariant bound edge and predecessor-state indices")]
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the predecessor-completion cursor increment remains in bounds")]
    fn predecessors_complete_exec(&self, node: usize) -> (b: bool)
        requires
            self.type_invariant(),
            node < self.num_nodes,
        ensures b == Self::predecessors_complete_in(self.edges@, self.nstate@, node),
    {
        let mut i = 0;
        while i < self.edges.len()
            invariant
                i <= self.edges.len(),
                self.type_invariant(),
                forall|k: int| 0 <= k < i && self.edges@[k].1 == node
                    ==> self.nstate@[self.edges@[k].0 as int]
                        == StepGraphNodeState::Complete,
            decreases self.edges.len() - i,
        {
            if self.edges[i].1 == node
                && !matches!(
                    self.nstate[self.edges[i].0],
                    StepGraphNodeState::Complete
                )
            {
                assert(!Self::predecessors_complete_in(self.edges@, self.nstate@, node));
                return false;
            }
            i += 1;
        }
        true
    }

    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the state-construction cursor remains within the node bound")]
    /// Construct initial readiness states for a valid edge set.
    pub fn new(num_nodes: usize, edges: Vec<(usize, usize)>) -> (s: StepGraph)
        requires
            Self::edges_valid(edges@, num_nodes),
            Self::edges_distinct(edges@),
        ensures
            s.num_nodes == num_nodes,
            s.edges@ == edges@,
            s.nstate@.len() == num_nodes,
            forall|n: usize| n < num_nodes ==>
                #[trigger] s.nstate@[n as int]
                    == if Self::has_predecessor_in(edges@, n) {
                        StepGraphNodeState::NotReady
                    } else {
                        StepGraphNodeState::Ready
                    },
            s.inv(),
            s.no_run_before_predecessors(),
    {
        let mut nstate = Vec::new();
        let mut n = 0;
        while n < num_nodes
            invariant
                n <= num_nodes,
                nstate@.len() == n,
                forall|k: usize| k < n ==>
                    #[trigger] nstate@[k as int]
                        == if Self::has_predecessor_in(edges@, k) {
                            StepGraphNodeState::NotReady
                        } else {
                            StepGraphNodeState::Ready
                        },
            decreases num_nodes - n,
        {
            if Self::has_predecessor_exec(&edges, n) {
                nstate.push(StepGraphNodeState::NotReady);
            } else {
                nstate.push(StepGraphNodeState::Ready);
            }
            n += 1;
        }
        let s = StepGraph { num_nodes, edges, nstate };
        assert(s.eligibility_closed()) by {
            assert forall|node: usize| node < s.num_nodes
                && #[trigger] s.nstate@[node as int] != StepGraphNodeState::NotReady
                implies Self::predecessors_complete_in(s.edges@, s.nstate@, node) by {
                assert(!Self::has_predecessor_in(s.edges@, node));
            }
        }
        s
    }

    #[expect(clippy::indexing_slicing, reason = "the action guard and Verus invariant bound the node-state index")]
    /// Promote a node after every predecessor completes.
    pub fn become_ready(&mut self, node: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            become_ready_action(
                old(self).nstate@,
                final(self).nstate@,
                node as int,
                Self::has_predecessor_in(old(self).edges@, node)
                    && Self::predecessors_complete_in(
                        old(self).edges@,
                        old(self).nstate@,
                        node,
                    ),
                accepted,
            ),
            states_monotone(old(self).nstate@, final(self).nstate@),
            final(self).inv(),
            final(self).no_run_before_predecessors(),
    {
        if node < self.num_nodes
            && matches!(self.nstate[node], StepGraphNodeState::NotReady)
            && Self::has_predecessor_exec(&self.edges, node)
            && self.predecessors_complete_exec(node)
        {
            let ghost old_states = self.nstate@;
            self.nstate.set(node, StepGraphNodeState::Ready);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] != StepGraphNodeState::NotReady
                    implies Self::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    if m == node {
                        assert forall|e: int| 0 <= e < self.edges@.len()
                            && self.edges@[e].1 == m
                            implies #[trigger] self.nstate@[self.edges@[e].0 as int]
                                == StepGraphNodeState::Complete by {
                            let p = self.edges@[e].0;
                            assert(old_states[p as int] == StepGraphNodeState::Complete);
                            assert(p != node);
                        }
                    } else {
                        assert(Self::predecessors_complete_in(self.edges@, old_states, m));
                        assert forall|e: int| 0 <= e < self.edges@.len()
                            && self.edges@[e].1 == m
                            implies #[trigger] self.nstate@[self.edges@[e].0 as int]
                                == StepGraphNodeState::Complete by {
                            let p = self.edges@[e].0;
                            assert(old_states[p as int] == StepGraphNodeState::Complete);
                            assert(p != node);
                        }
                    }
                }
            }
            true
        } else {
            false
        }
    }

    #[expect(clippy::indexing_slicing, reason = "the action guard and Verus invariant bound the node-state index")]
    /// Start one ready node.
    pub fn start_running(&mut self, node: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            start_running_action(
                old(self).nstate@,
                final(self).nstate@,
                node as int,
                true,
                accepted,
            ),
            states_monotone(old(self).nstate@, final(self).nstate@),
            final(self).inv(),
            final(self).no_run_before_predecessors(),
    {
        if node < self.num_nodes && matches!(self.nstate[node], StepGraphNodeState::Ready) {
            let ghost old_states = self.nstate@;
            self.nstate.set(node, StepGraphNodeState::Running);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] != StepGraphNodeState::NotReady
                    implies Self::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    assert(Self::predecessors_complete_in(self.edges@, old_states, m));
                    assert forall|e: int| 0 <= e < self.edges@.len()
                        && self.edges@[e].1 == m
                        implies #[trigger] self.nstate@[self.edges@[e].0 as int]
                            == StepGraphNodeState::Complete by {
                        let p = self.edges@[e].0;
                        assert(old_states[p as int] == StepGraphNodeState::Complete);
                        assert(p != node);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    #[expect(clippy::indexing_slicing, reason = "the action guard and Verus invariant bound the node-state index")]
    /// Complete one running node.
    pub fn complete_node(&mut self, node: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            complete_node_action(
                old(self).nstate@,
                final(self).nstate@,
                node as int,
                true,
                accepted,
            ),
            states_monotone(old(self).nstate@, final(self).nstate@),
            final(self).inv(),
            final(self).no_run_before_predecessors(),
    {
        if node < self.num_nodes && matches!(self.nstate[node], StepGraphNodeState::Running) {
            let ghost old_states = self.nstate@;
            self.nstate.set(node, StepGraphNodeState::Complete);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] != StepGraphNodeState::NotReady
                    implies Self::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    assert(Self::predecessors_complete_in(self.edges@, old_states, m));
                    assert forall|e: int| 0 <= e < self.edges@.len()
                        && self.edges@[e].1 == m
                        implies #[trigger] self.nstate@[self.edges@[e].0 as int]
                            == StepGraphNodeState::Complete by {
                        let p = self.edges@[e].0;
                        if p != node {
                            assert(self.nstate@[p as int] == old_states[p as int]);
                        }
                    }
                }
            }
            true
        } else {
            false
        }
    }

    #[expect(clippy::indexing_slicing, reason = "Verus proves the completion cursor remains in bounds")]
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the completion cursor increment remains in bounds")]
    /// Execute the terminal stutter when every node is complete.
    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (forall|i: int| 0 <= i < old(self).nstate@.len()
                ==> #[trigger] old(self).nstate@[i] == StepGraphNodeState::Complete),
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            final(self).nstate@ == old(self).nstate@,
            final(self).inv(),
    {
        let mut i = 0;
        while i < self.nstate.len()
            invariant
                i <= self.nstate.len(),
                self.inv(),
                forall|k: int| 0 <= k < i ==>
                    self.nstate@[k] == StepGraphNodeState::Complete,
            decreases self.nstate.len() - i,
        {
            if !matches!(self.nstate[i], StepGraphNodeState::Complete) {
                return false;
            }
            i += 1;
        }
        true
    }
}

}
