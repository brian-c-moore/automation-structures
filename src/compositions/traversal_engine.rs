// TraversalEngine executable correspondence boundary.
//
// Concrete carrier for formal/structures/TraversalEngine/TraversalEngine.tla.
// Nodes is the index range [0, num_nodes), NodeCost is 2, and only the root has children
// (every non-root node). Vec fields represent the TLA+ sets: validity and
// duplicate-freedom are maintained, while contracts state action effects
// extensionally through membership. VisitNode, Skip, and the enabled-at-empty
// Terminate stutter are all implemented.
//
// The proof boundary is the model's safety boundary: BudgetInvariant,
// AcceptedSubsetVisited, and exact action correspondence. It does not claim a
// traversal order, fairness, or graph-search completeness.

use vstd::prelude::*;

verus! {

pub struct TraversalEngine {
    pub num_nodes: usize,
    pub root: usize,
    pub budget_remaining: u64,
    pub visited: Vec<usize>,
    pub accepted: Vec<usize>,
    pub queue: Vec<usize>,
}

impl TraversalEngine {
    pub open spec fn all_valid(s: Seq<usize>, num_nodes: usize) -> bool {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < num_nodes
    }

    pub open spec fn all_distinct(s: Seq<usize>) -> bool {
        forall|i: int, j: int|
            0 <= i < s.len() && 0 <= j < s.len() && i != j
                ==> #[trigger] s[i] != #[trigger] s[j]
    }

    pub open spec fn contains_up_to(s: Seq<usize>, end: int, n: usize) -> bool {
        exists|i: int| 0 <= i < end && i < s.len() && s[i] == n
    }

    pub open spec fn seq_contains(s: Seq<usize>, n: usize) -> bool {
        Self::contains_up_to(s, s.len() as int, n)
    }

    pub open spec fn type_invariant(&self) -> bool {
        &&& Self::all_valid(self.visited@, self.num_nodes)
        &&& Self::all_valid(self.accepted@, self.num_nodes)
        &&& Self::all_valid(self.queue@, self.num_nodes)
        &&& Self::all_distinct(self.visited@)
        &&& Self::all_distinct(self.accepted@)
        &&& Self::all_distinct(self.queue@)
    }

    pub open spec fn budget_invariant(&self) -> bool {
        self.budget_remaining >= 0
    }

    pub open spec fn accepted_subset_visited(&self) -> bool {
        forall|n: usize| #[trigger] Self::seq_contains(self.accepted@, n)
            ==> Self::seq_contains(self.visited@, n)
    }

    pub proof fn lemma_contains_extend(s: Seq<usize>, end: int, n: usize)
        requires 0 <= end < s.len(),
        ensures Self::contains_up_to(s, end + 1, n)
            == (Self::contains_up_to(s, end, n) || s[end] == n),
    {
        if Self::contains_up_to(s, end + 1, n) {
            let i = choose|i: int| 0 <= i < end + 1 && i < s.len() && s[i] == n;
            assert(i < end || i == end);
        }
        if Self::contains_up_to(s, end, n) {
            let i = choose|i: int| 0 <= i < end && i < s.len() && s[i] == n;
            assert(0 <= i < end + 1 && i < s.len() && s[i] == n);
        }
        if s[end] == n {
            assert(0 <= end < end + 1 && end < s.len());
        }
    }

    pub proof fn lemma_push_contains(s: Seq<usize>, value: usize, n: usize)
        ensures Self::seq_contains(s.push(value), n)
            == (Self::seq_contains(s, n) || value == n),
    {
        let p = s.push(value);
        if Self::seq_contains(p, n) {
            let i = choose|i: int| 0 <= i < p.len() && p[i] == n;
            if i < s.len() {
                assert(p[i] == s[i]);
            } else {
                assert(i == s.len());
            }
        }
        if Self::seq_contains(s, n) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == n;
            assert(p[i] == s[i]);
        }
        if value == n {
            assert(p[s.len() as int] == n);
        }
    }

    pub fn new(num_nodes: usize, root: usize, max_budget: u64) -> (s: TraversalEngine)
        requires root < num_nodes,
        ensures
            s.num_nodes == num_nodes,
            s.root == root,
            s.budget_remaining == max_budget,
            s.visited@.len() == 0,
            s.accepted@.len() == 0,
            s.queue@ == seq![root],
            s.type_invariant(),
            s.budget_invariant(),
            s.accepted_subset_visited(),
    {
        let mut queue = Vec::new();
        queue.push(root);
        TraversalEngine {
            num_nodes,
            root,
            budget_remaining: max_budget,
            visited: Vec::new(),
            accepted: Vec::new(),
            queue,
        }
    }

    fn contains_exec(s: &Vec<usize>, n: usize) -> (b: bool)
        ensures b == Self::seq_contains(s@, n),
    {
        let mut i = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                !Self::contains_up_to(s@, i as int, n),
            decreases s.len() - i,
        {
            if s[i] == n {
                assert(Self::contains_up_to(s@, (i + 1) as int, n));
                assert(Self::seq_contains(s@, n));
                return true;
            }
            proof { Self::lemma_contains_extend(s@, i as int, n); }
            i = i + 1;
        }
        false
    }

    pub fn queue_contains(&self, n: usize) -> (b: bool)
        ensures b == Self::seq_contains(self.queue@, n),
    {
        Self::contains_exec(&self.queue, n)
    }

    pub fn visited_contains(&self, n: usize) -> (b: bool)
        ensures b == Self::seq_contains(self.visited@, n),
    {
        Self::contains_exec(&self.visited, n)
    }

    pub fn accepted_contains(&self, n: usize) -> (b: bool)
        ensures b == Self::seq_contains(self.accepted@, n),
    {
        Self::contains_exec(&self.accepted, n)
    }

    pub fn can_visit(&self, n: usize) -> (b: bool)
        ensures b == (n < self.num_nodes
            && Self::seq_contains(self.queue@, n)
            && !Self::seq_contains(self.visited@, n)),
    {
        if n >= self.num_nodes {
            false
        } else if !Self::contains_exec(&self.queue, n) {
            false
        } else {
            !Self::contains_exec(&self.visited, n)
        }
    }

    pub fn can_skip(&self, n: usize) -> (b: bool)
        ensures b == (n < self.num_nodes && Self::seq_contains(self.queue@, n)),
    {
        n < self.num_nodes && Self::contains_exec(&self.queue, n)
    }

    pub fn can_terminate(&self) -> (b: bool)
        ensures b == (self.queue@.len() == 0),
    {
        self.queue.len() == 0
    }

    fn without_node(nodes: &Vec<usize>, n: usize, num_nodes: usize) -> (out: Vec<usize>)
        requires
            Self::all_valid(nodes@, num_nodes),
            Self::all_distinct(nodes@),
        ensures
            Self::all_valid(out@, num_nodes),
            Self::all_distinct(out@),
            forall|x: usize| #[trigger] Self::seq_contains(out@, x)
                == (Self::seq_contains(nodes@, x) && x != n),
    {
        let _ = num_nodes;
        let mut out = Vec::new();
        let mut i = 0;
        while i < nodes.len()
            invariant
                i <= nodes.len(),
                Self::all_valid(nodes@, num_nodes),
                Self::all_distinct(nodes@),
                Self::all_valid(out@, num_nodes),
                Self::all_distinct(out@),
                forall|x: usize| #[trigger] Self::seq_contains(out@, x)
                    == (Self::contains_up_to(nodes@, i as int, x) && x != n),
            decreases nodes.len() - i,
        {
            let v = nodes[i];
            let ghost old_out = out@;
            if v != n {
                assert(!Self::seq_contains(old_out, v)) by {
                    if Self::seq_contains(old_out, v) {
                        assert(Self::contains_up_to(nodes@, i as int, v));
                        let j = choose|j: int| 0 <= j < i as int && j < nodes@.len()
                            && nodes@[j] == v;
                        assert(nodes@[j] != nodes@[i as int]);
                    }
                }
                out.push(v);
                assert(Self::all_distinct(out@)) by {
                    assert forall|a: int, b: int|
                        0 <= a < out@.len() && 0 <= b < out@.len() && a != b
                            implies #[trigger] out@[a] != #[trigger] out@[b] by {
                        if a < old_out.len() && b < old_out.len() {
                        } else if a == old_out.len() && b < old_out.len() {
                            assert(out@[b] == old_out[b]);
                            assert(Self::seq_contains(old_out, old_out[b]));
                        } else if b == old_out.len() && a < old_out.len() {
                            assert(out@[a] == old_out[a]);
                            assert(Self::seq_contains(old_out, old_out[a]));
                        }
                    }
                }
                assert(Self::all_valid(out@, num_nodes)) by {
                    assert forall|k: int| 0 <= k < out@.len()
                        implies #[trigger] out@[k] < num_nodes by {
                        if k < old_out.len() {
                            assert(out@[k] == old_out[k]);
                        } else {
                            assert(out@[k] == nodes@[i as int]);
                        }
                    }
                }
            }
            assert forall|x: usize| #[trigger] Self::seq_contains(out@, x)
                == (Self::contains_up_to(nodes@, (i + 1) as int, x) && x != n) by {
                Self::lemma_contains_extend(nodes@, i as int, x);
                if v != n {
                    Self::lemma_push_contains(old_out, v, x);
                }
            }
            i = i + 1;
        }
        out
    }

    fn enqueue_star_children(&mut self)
        requires
            old(self).root < old(self).num_nodes,
            Self::all_valid(old(self).queue@, old(self).num_nodes),
            Self::all_distinct(old(self).queue@),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).budget_remaining == old(self).budget_remaining,
            final(self).visited@ == old(self).visited@,
            final(self).accepted@ == old(self).accepted@,
            Self::all_valid(final(self).queue@, final(self).num_nodes),
            Self::all_distinct(final(self).queue@),
            forall|x: usize| #[trigger] Self::seq_contains(final(self).queue@, x)
                == (Self::seq_contains(old(self).queue@, x)
                    || (x < old(self).num_nodes && x != old(self).root)),
    {
        let ghost original = self.queue@;
        let mut j = 0;
        while j < self.num_nodes
            invariant
                j <= self.num_nodes,
                self.num_nodes == old(self).num_nodes,
                self.root == old(self).root,
                self.budget_remaining == old(self).budget_remaining,
                self.visited@ == old(self).visited@,
                self.accepted@ == old(self).accepted@,
                Self::all_valid(self.queue@, self.num_nodes),
                Self::all_distinct(self.queue@),
                forall|x: usize| #[trigger] Self::seq_contains(self.queue@, x)
                    == (Self::seq_contains(original, x) || (x < j && x != self.root)),
            decreases self.num_nodes - j,
        {
            let ghost before = self.queue@;
            if j != self.root {
                let present = Self::contains_exec(&self.queue, j);
                if !present {
                    self.queue.push(j);
                    assert(Self::all_distinct(self.queue@)) by {
                        assert forall|a: int, b: int|
                            0 <= a < self.queue@.len() && 0 <= b < self.queue@.len() && a != b
                                implies #[trigger] self.queue@[a] != #[trigger] self.queue@[b] by {
                            if a < before.len() && b < before.len() {
                            } else if a == before.len() && b < before.len() {
                                assert(self.queue@[b] == before[b]);
                                assert(Self::seq_contains(before, before[b]));
                            } else if b == before.len() && a < before.len() {
                                assert(self.queue@[a] == before[a]);
                                assert(Self::seq_contains(before, before[a]));
                            }
                        }
                    }
                    assert(Self::all_valid(self.queue@, self.num_nodes)) by {
                        assert forall|k: int| 0 <= k < self.queue@.len()
                            implies #[trigger] self.queue@[k] < self.num_nodes by {
                            if k < before.len() {
                                assert(self.queue@[k] == before[k]);
                            } else {
                                assert(self.queue@[k] == j);
                            }
                        }
                    }
                }
            }
            assert forall|x: usize| #[trigger] Self::seq_contains(self.queue@, x)
                == (Self::seq_contains(original, x) || (x < j + 1 && x != self.root)) by {
                if j != self.root {
                    if self.queue@ != before {
                        Self::lemma_push_contains(before, j, x);
                    }
                }
            }
            j = j + 1;
        }
    }

    pub fn visit_node(&mut self, n: usize)
        requires
            old(self).type_invariant(),
            old(self).accepted_subset_visited(),
            old(self).root < old(self).num_nodes,
            n < old(self).num_nodes,
            Self::seq_contains(old(self).queue@, n),
            !Self::seq_contains(old(self).visited@, n),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).budget_remaining as int
                == if old(self).budget_remaining >= 2 {
                    old(self).budget_remaining as int - 2
                } else { old(self).budget_remaining as int },
            forall|x: usize| #[trigger] Self::seq_contains(final(self).visited@, x)
                == (Self::seq_contains(old(self).visited@, x) || x == n),
            forall|x: usize| #[trigger] Self::seq_contains(final(self).accepted@, x)
                == (Self::seq_contains(old(self).accepted@, x)
                    || (old(self).budget_remaining >= 2 && x == n)),
            forall|x: usize| #[trigger] Self::seq_contains(final(self).queue@, x)
                == if old(self).budget_remaining >= 2 && n == old(self).root {
                    (Self::seq_contains(old(self).queue@, x) && x != n)
                        || (x < old(self).num_nodes && x != old(self).root)
                } else {
                    Self::seq_contains(old(self).queue@, x) && x != n
                },
            final(self).type_invariant(),
            final(self).budget_invariant(),
            final(self).accepted_subset_visited(),
    {
        let ghost old_visited = self.visited@;
        let ghost old_accepted = self.accepted@;
        let old_budget = self.budget_remaining;

        self.queue = Self::without_node(&self.queue, n, self.num_nodes);
        self.visited.push(n);

        assert(Self::all_valid(self.visited@, self.num_nodes)) by {
            assert forall|k: int| 0 <= k < self.visited@.len()
                implies #[trigger] self.visited@[k] < self.num_nodes by {
                if k < old_visited.len() {
                    assert(self.visited@[k] == old_visited[k]);
                } else {
                    assert(self.visited@[k] == n);
                }
            }
        }
        assert(Self::all_distinct(self.visited@)) by {
            assert forall|i: int, j: int|
                0 <= i < self.visited@.len() && 0 <= j < self.visited@.len() && i != j
                    implies #[trigger] self.visited@[i] != #[trigger] self.visited@[j] by {
                if i < old_visited.len() && j < old_visited.len() {
                } else if i == old_visited.len() && j < old_visited.len() {
                    assert(self.visited@[j] == old_visited[j]);
                    assert(Self::seq_contains(old_visited, old_visited[j]));
                } else if j == old_visited.len() && i < old_visited.len() {
                    assert(self.visited@[i] == old_visited[i]);
                    assert(Self::seq_contains(old_visited, old_visited[i]));
                }
            }
        }

        if old_budget >= 2 {
            assert(!Self::seq_contains(old_accepted, n)) by {
                if Self::seq_contains(old_accepted, n) {
                    assert(Self::seq_contains(old_visited, n));
                }
            }
            self.accepted.push(n);
            self.budget_remaining = self.budget_remaining - 2;

            assert(Self::all_valid(self.accepted@, self.num_nodes)) by {
                assert forall|k: int| 0 <= k < self.accepted@.len()
                    implies #[trigger] self.accepted@[k] < self.num_nodes by {
                    if k < old_accepted.len() {
                        assert(self.accepted@[k] == old_accepted[k]);
                    } else {
                        assert(self.accepted@[k] == n);
                    }
                }
            }
            assert(Self::all_distinct(self.accepted@)) by {
                assert forall|i: int, j: int|
                    0 <= i < self.accepted@.len() && 0 <= j < self.accepted@.len() && i != j
                        implies #[trigger] self.accepted@[i] != #[trigger] self.accepted@[j] by {
                    if i < old_accepted.len() && j < old_accepted.len() {
                    } else if i == old_accepted.len() && j < old_accepted.len() {
                        assert(self.accepted@[j] == old_accepted[j]);
                        assert(Self::seq_contains(old_accepted, old_accepted[j]));
                    } else if j == old_accepted.len() && i < old_accepted.len() {
                        assert(self.accepted@[i] == old_accepted[i]);
                        assert(Self::seq_contains(old_accepted, old_accepted[i]));
                    }
                }
            }
            if n == self.root {
                self.enqueue_star_children();
            }
        }

        assert forall|x: usize| #[trigger] Self::seq_contains(self.visited@, x)
            == (Self::seq_contains(old_visited, x) || x == n) by {
            Self::lemma_push_contains(old_visited, n, x);
        }
        if old_budget >= 2 {
            assert forall|x: usize| #[trigger] Self::seq_contains(self.accepted@, x)
                == (Self::seq_contains(old_accepted, x) || x == n) by {
                Self::lemma_push_contains(old_accepted, n, x);
            }
        }
        assert(self.accepted_subset_visited()) by {
            assert forall|x: usize| #[trigger] Self::seq_contains(self.accepted@, x)
                implies Self::seq_contains(self.visited@, x) by {
                if Self::seq_contains(old_accepted, x) {
                    assert(Self::seq_contains(old_visited, x));
                }
            }
        }
    }

    pub fn skip(&mut self, n: usize)
        requires
            old(self).type_invariant(),
            old(self).accepted_subset_visited(),
            n < old(self).num_nodes,
            Self::seq_contains(old(self).queue@, n),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).budget_remaining == old(self).budget_remaining,
            final(self).visited@ == old(self).visited@,
            final(self).accepted@ == old(self).accepted@,
            forall|x: usize| #[trigger] Self::seq_contains(final(self).queue@, x)
                == (Self::seq_contains(old(self).queue@, x) && x != n),
            final(self).type_invariant(),
            final(self).budget_invariant(),
            final(self).accepted_subset_visited(),
    {
        self.queue = Self::without_node(&self.queue, n, self.num_nodes);
    }

    pub fn terminate(&mut self)
        requires
            old(self).type_invariant(),
            old(self).accepted_subset_visited(),
            old(self).queue@.len() == 0,
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).budget_remaining == old(self).budget_remaining,
            final(self).visited@ == old(self).visited@,
            final(self).accepted@ == old(self).accepted@,
            final(self).queue@ == old(self).queue@,
            final(self).type_invariant(),
            final(self).budget_invariant(),
            final(self).accepted_subset_visited(),
    {
    }
}

}
