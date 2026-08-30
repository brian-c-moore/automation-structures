// Faithful finite-index carrier for StepGraph.tla.
// State tags: 0=NotReady, 1=Ready, 2=Running, 3=Completed.

use vstd::prelude::*;

verus! {

pub struct StepGraph {
    pub num_nodes: usize,
    pub edges: Vec<(usize, usize)>,
    pub nstate: Vec<u8>,
}

impl StepGraph {
    pub open spec fn edges_valid(edges: Seq<(usize, usize)>, num_nodes: usize) -> bool {
        forall|i: int| 0 <= i < edges.len() ==>
            #[trigger] edges[i].0 < num_nodes && edges[i].1 < num_nodes
    }

    pub open spec fn edges_distinct(edges: Seq<(usize, usize)>) -> bool {
        forall|i: int, j: int|
            0 <= i < edges.len() && 0 <= j < edges.len() && i != j
                ==> #[trigger] edges[i] != #[trigger] edges[j]
    }

    pub open spec fn has_predecessor_in(edges: Seq<(usize, usize)>, node: usize) -> bool {
        exists|i: int| 0 <= i < edges.len() && edges[i].1 == node
    }

    pub open spec fn predecessors_complete_in(
        edges: Seq<(usize, usize)>, states: Seq<u8>, node: usize,
    ) -> bool {
        forall|i: int| 0 <= i < edges.len() && edges[i].1 == node
            ==> #[trigger] states[edges[i].0 as int] == 3
    }

    pub open spec fn type_invariant(&self) -> bool {
        &&& self.nstate@.len() == self.num_nodes
        &&& Self::edges_valid(self.edges@, self.num_nodes)
        &&& Self::edges_distinct(self.edges@)
        &&& (forall|i: int| 0 <= i < self.nstate@.len()
                ==> #[trigger] self.nstate@[i] <= 3)
    }

    pub open spec fn eligibility_closed(&self) -> bool {
        forall|n: usize| n < self.num_nodes && #[trigger] self.nstate@[n as int] >= 1
            ==> Self::predecessors_complete_in(self.edges@, self.nstate@, n)
    }

    pub open spec fn no_run_before_predecessors(&self) -> bool {
        forall|n: usize| n < self.num_nodes && #[trigger] self.nstate@[n as int] >= 2
            ==> Self::predecessors_complete_in(self.edges@, self.nstate@, n)
    }

    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.eligibility_closed()
    }

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
            i = i + 1;
        }
        false
    }

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
                    ==> self.nstate@[self.edges@[k].0 as int] == 3,
            decreases self.edges.len() - i,
        {
            if self.edges[i].1 == node && self.nstate[self.edges[i].0] != 3 {
                assert(!Self::predecessors_complete_in(self.edges@, self.nstate@, node));
                return false;
            }
            i = i + 1;
        }
        true
    }

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
                    == if Self::has_predecessor_in(edges@, n) { 0u8 } else { 1u8 },
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
                        == if Self::has_predecessor_in(edges@, k) { 0u8 } else { 1u8 },
            decreases num_nodes - n,
        {
            if Self::has_predecessor_exec(&edges, n) {
                nstate.push(0);
            } else {
                nstate.push(1);
            }
            n = n + 1;
        }
        let s = StepGraph { num_nodes, edges, nstate };
        assert(s.eligibility_closed()) by {
            assert forall|node: usize| node < s.num_nodes
                && #[trigger] s.nstate@[node as int] >= 1
                implies Self::predecessors_complete_in(s.edges@, s.nstate@, node) by {
                assert(!Self::has_predecessor_in(s.edges@, node));
            }
        }
        s
    }

    pub fn become_ready(&mut self, node: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (node < old(self).num_nodes
                && old(self).nstate@[node as int] == 0
                && Self::has_predecessor_in(old(self).edges@, node)
                && Self::predecessors_complete_in(old(self).edges@, old(self).nstate@, node)),
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            final(self).nstate@ == if accepted {
                old(self).nstate@.update(node as int, 1)
            } else { old(self).nstate@ },
            forall|i: int| 0 <= i < final(self).nstate@.len()
                ==> #[trigger] final(self).nstate@[i] >= old(self).nstate@[i],
            final(self).inv(),
            final(self).no_run_before_predecessors(),
    {
        if node < self.num_nodes && self.nstate[node] == 0
            && Self::has_predecessor_exec(&self.edges, node)
            && self.predecessors_complete_exec(node)
        {
            let ghost old_states = self.nstate@;
            self.nstate.set(node, 1);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] >= 1
                    implies Self::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    if m == node {
                        assert forall|e: int| 0 <= e < self.edges@.len()
                            && self.edges@[e].1 == m
                            implies #[trigger] self.nstate@[self.edges@[e].0 as int] == 3 by {
                            let p = self.edges@[e].0;
                            assert(old_states[p as int] == 3);
                            assert(p != node);
                        }
                    } else {
                        assert(Self::predecessors_complete_in(self.edges@, old_states, m));
                        assert forall|e: int| 0 <= e < self.edges@.len()
                            && self.edges@[e].1 == m
                            implies #[trigger] self.nstate@[self.edges@[e].0 as int] == 3 by {
                            let p = self.edges@[e].0;
                            assert(old_states[p as int] == 3);
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

    pub fn start_running(&mut self, node: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (node < old(self).num_nodes && old(self).nstate@[node as int] == 1),
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            final(self).nstate@ == if accepted {
                old(self).nstate@.update(node as int, 2)
            } else { old(self).nstate@ },
            forall|i: int| 0 <= i < final(self).nstate@.len()
                ==> #[trigger] final(self).nstate@[i] >= old(self).nstate@[i],
            final(self).inv(),
            final(self).no_run_before_predecessors(),
    {
        if node < self.num_nodes && self.nstate[node] == 1 {
            let ghost old_states = self.nstate@;
            self.nstate.set(node, 2);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] >= 1
                    implies Self::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    assert(Self::predecessors_complete_in(self.edges@, old_states, m));
                    assert forall|e: int| 0 <= e < self.edges@.len()
                        && self.edges@[e].1 == m
                        implies #[trigger] self.nstate@[self.edges@[e].0 as int] == 3 by {
                        let p = self.edges@[e].0;
                        assert(old_states[p as int] == 3);
                        assert(p != node);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    pub fn complete_node(&mut self, node: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (node < old(self).num_nodes && old(self).nstate@[node as int] == 2),
            final(self).num_nodes == old(self).num_nodes,
            final(self).edges@ == old(self).edges@,
            final(self).nstate@ == if accepted {
                old(self).nstate@.update(node as int, 3)
            } else { old(self).nstate@ },
            forall|i: int| 0 <= i < final(self).nstate@.len()
                ==> #[trigger] final(self).nstate@[i] >= old(self).nstate@[i],
            final(self).inv(),
            final(self).no_run_before_predecessors(),
    {
        if node < self.num_nodes && self.nstate[node] == 2 {
            let ghost old_states = self.nstate@;
            self.nstate.set(node, 3);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] >= 1
                    implies Self::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    assert(Self::predecessors_complete_in(self.edges@, old_states, m));
                    assert forall|e: int| 0 <= e < self.edges@.len()
                        && self.edges@[e].1 == m
                        implies #[trigger] self.nstate@[self.edges@[e].0 as int] == 3 by {
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

    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (forall|i: int| 0 <= i < old(self).nstate@.len()
                ==> #[trigger] old(self).nstate@[i] == 3),
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
                forall|k: int| 0 <= k < i ==> self.nstate@[k] == 3,
            decreases self.nstate.len() - i,
        {
            if self.nstate[i] != 3 {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

}
