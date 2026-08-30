// Executable witness for formal/composition/structure-compositions/TraversalBudgetComposition.tla.
//
// Nodes is the half-open index range [0, num_nodes), NodeCost is 2, and only
// the root has children. Vec fields represent the TLA+ sets extensionally and
// remain duplicate-free. VisitAndAccept removes the selected queue member,
// accepts and visits it, moves the two budget views by the same cost, and adds
// the root's children. SkipUnaffordable visits and removes without charging;
// Skip only removes. The shared equation is
// total_cost + budget_remaining = max_budget.
//
// This is a sequential witness: each TLA+ action is one &mut self method. A
// concurrent implementation must provide an equivalent atomic boundary.

use vstd::prelude::*;

verus! {

/// TraversalBudgetComposition state over a node universe `0..num_nodes` rooted
/// at `root`, with a shared budget of `max_budget` split into the spent view
/// `total_cost` and the remaining view `budget_remaining`.
pub struct TraversalBudgetComposition {
    /// |Nodes|: the node universe is the index range `0..num_nodes`.
    pub num_nodes: usize,
    /// RootNode.
    pub root: usize,
    /// MaxBudget (constant): the shared capacity.
    pub max_budget: u64,
    /// total_cost ∈ 0..MaxBudget: the AllocationSnapshot (spent) view.
    pub total_cost: u64,
    /// budget_remaining ∈ 0..MaxBudget: the Budget (remaining) view.
    pub budget_remaining: u64,
    /// visited ⊆ Nodes, a duplicate-free Vec of node ids.
    pub visited: Vec<usize>,
    /// accepted ⊆ Nodes, a duplicate-free Vec of node ids.
    pub accepted: Vec<usize>,
    /// queue ⊆ Nodes, a worklist of valid node ids.
    pub queue: Vec<usize>,
}

impl TraversalBudgetComposition {
    // ── Specifications ──────────────────────────────────────────────────

    /// Every id in `s` is a valid node index (`s ⊆ Nodes`).
    pub open spec fn all_valid(s: Seq<usize>, num_nodes: usize) -> bool {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < num_nodes
    }

    /// `s` is a set: no duplicate ids.
    pub open spec fn all_distinct(s: Seq<usize>) -> bool {
        forall|i: int, j: int|
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j]
    }

    pub open spec fn contains_up_to(s: Seq<usize>, end: int, n: usize) -> bool {
        exists|i: int| 0 <= i < end && i < s.len() && s[i] == n
    }

    /// `n ∈ s`.
    pub open spec fn seq_contains(s: Seq<usize>, n: usize) -> bool {
        Self::contains_up_to(s, s.len() as int, n)
    }

    /// TLA+ `TypeInvariant`: the node sets are valid and represented without
    /// duplicates; total_cost and budget_remaining are within 0..MaxBudget (the
    /// Nat lower bound is carried by u64).
    pub open spec fn type_invariant(&self) -> bool {
        &&& Self::all_valid(self.visited@, self.num_nodes)
        &&& Self::all_valid(self.accepted@, self.num_nodes)
        &&& Self::all_valid(self.queue@, self.num_nodes)
        &&& Self::all_distinct(self.visited@)
        &&& Self::all_distinct(self.accepted@)
        &&& Self::all_distinct(self.queue@)
        &&& self.total_cost <= self.max_budget
        &&& self.budget_remaining <= self.max_budget
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

    /// TLA+ `CompositionInvariant`: the spent total is bounded by capacity AND
    /// the two views agree (no resource appears or disappears).
    pub open spec fn composition_invariant(&self) -> bool {
        &&& self.total_cost <= self.max_budget
        &&& self.total_cost + self.budget_remaining == self.max_budget
    }

    /// TLA+ `AcceptedSubsetVisited == accepted ⊆ visited`.
    pub open spec fn accepted_subset_visited(&self) -> bool {
        forall|i: int|
            0 <= i < self.accepted.len() ==> #[trigger] Self::seq_contains(
                self.visited@,
                self.accepted@[i],
            )
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the initial state: full budget unspent, nothing
    /// visited/accepted, the root queued. Realises the TLA+ `Init` and
    /// establishes all three invariants (the equation holds as
    /// `0 + max_budget = max_budget`).
    pub fn new(num_nodes: usize, root: usize, max_budget: u64) -> (s: TraversalBudgetComposition)
        requires
            root < num_nodes,
        ensures
            s.num_nodes == num_nodes,
            s.root == root,
            s.max_budget == max_budget,
            s.total_cost == 0,
            s.budget_remaining == max_budget,
            s.visited@.len() == 0,
            s.accepted@.len() == 0,
            s.queue@.len() == 1,
            s.queue@[0] == root,
            s.type_invariant(),
            s.composition_invariant(),
            s.accepted_subset_visited(),
    {
        let mut queue: Vec<usize> = Vec::new();
        queue.push(root);
        TraversalBudgetComposition {
            num_nodes,
            root,
            max_budget,
            total_cost: 0,
            budget_remaining: max_budget,
            visited: Vec::new(),
            accepted: Vec::new(),
            queue,
        }
    }

    // ── Membership (executable) ─────────────────────────────────────────

    /// Executable `n ∈ visited` test (discharges the `n ∉ visited` guard).
    pub fn visited_contains(&self, n: usize) -> (b: bool)
        ensures
            b == Self::seq_contains(self.visited@, n),
    {
        let len = self.visited.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.visited.len(),
                forall|k: int| 0 <= k < i ==> self.visited@[k] != n,
            decreases len - i,
        {
            if self.visited[i] == n {
                assert(self.visited@[i as int] == n);
                return true;
            }
            i = i + 1;
        }
        assert(!Self::seq_contains(self.visited@, n));
        false
    }

    /// Executable `n ∈ queue` test (discharges the `n ∈ queue` guard).
    pub fn queue_contains(&self, n: usize) -> (b: bool)
        ensures
            b == Self::seq_contains(self.queue@, n),
    {
        let len = self.queue.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.queue.len(),
                forall|k: int| 0 <= k < i ==> self.queue@[k] != n,
            decreases len - i,
        {
            if self.queue[i] == n {
                assert(self.queue@[i as int] == n);
                return true;
            }
            i = i + 1;
        }
        assert(!Self::seq_contains(self.queue@, n));
        false
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

    // ── Enqueue star children (TLA+ NodeChildren(root) = Nodes \ {root}) ──

    /// Add every non-root node to the queue if it is not already present.
    /// Preserves the set representation and touches no other state.
    fn enqueue_star_children(&mut self)
        requires
            old(self).root < old(self).num_nodes,
            Self::all_valid(old(self).queue@, old(self).num_nodes),
            Self::all_distinct(old(self).queue@),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).max_budget == old(self).max_budget,
            final(self).total_cost == old(self).total_cost,
            final(self).budget_remaining == old(self).budget_remaining,
            final(self).visited@ == old(self).visited@,
            final(self).accepted@ == old(self).accepted@,
            Self::all_valid(final(self).queue@, final(self).num_nodes),
            Self::all_distinct(final(self).queue@),
            forall|m: usize| #[trigger] Self::seq_contains(final(self).queue@, m)
                <==> Self::seq_contains(old(self).queue@, m)
                     || (m < old(self).num_nodes && m != old(self).root),
    {
        let ghost original = self.queue@;
        let mut j: usize = 0;
        while j < self.num_nodes
            invariant
                j <= self.num_nodes,
                self.num_nodes == old(self).num_nodes,
                self.root == old(self).root,
                self.max_budget == old(self).max_budget,
                self.total_cost == old(self).total_cost,
                self.budget_remaining == old(self).budget_remaining,
                self.visited@ == old(self).visited@,
                self.accepted@ == old(self).accepted@,
                Self::all_valid(self.queue@, self.num_nodes),
                Self::all_distinct(self.queue@),
                forall|m: usize| #[trigger] Self::seq_contains(self.queue@, m)
                    <==> Self::seq_contains(original, m)
                         || (m < j && m != self.root),
            decreases self.num_nodes - j,
        {
            let ghost oq = self.queue@;
            if j != self.root {
                let present = Self::contains_exec(&self.queue, j);
                if !present {
                    self.queue.push(j);
                    assert(Self::all_distinct(self.queue@)) by {
                        assert forall|a: int, b: int|
                            0 <= a < self.queue@.len() && 0 <= b < self.queue@.len() && a != b
                                implies #[trigger] self.queue@[a] != #[trigger] self.queue@[b] by {
                            if a < oq.len() && b < oq.len() {
                            } else if a == oq.len() && b < oq.len() {
                                assert(self.queue@[b] == oq[b]);
                                assert(Self::seq_contains(oq, oq[b]));
                            } else if b == oq.len() && a < oq.len() {
                                assert(self.queue@[a] == oq[a]);
                                assert(Self::seq_contains(oq, oq[a]));
                            }
                        }
                    }
                    assert(Self::all_valid(self.queue@, self.num_nodes)) by {
                        assert forall|k: int| 0 <= k < self.queue@.len()
                            implies #[trigger] self.queue@[k] < self.num_nodes by {
                            if k < oq.len() {
                                assert(self.queue@[k] == oq[k]);
                            } else {
                                assert(self.queue@[k] == j);
                            }
                        }
                    }
                }
            }
            assert forall|m: usize| #[trigger] Self::seq_contains(self.queue@, m)
                <==> Self::seq_contains(original, m) || (m < j + 1 && m != self.root) by {
                if j != self.root {
                    if self.queue@ != oq {
                        Self::lemma_push_contains(oq, j, m);
                    }
                }
            }
            j = j + 1;
        }
    }

    // ── VisitAndAccept (TLA+ VisitAndAccept) ────────────────────────────

    /// Visit and accept node `n`: the atomic visit-accept-deduct. Realises the
    /// TLA+ `VisitAndAccept(n)` action — its three guards (n ∈ queue,
    /// n ∉ visited, NodeCost 2 <= budget_remaining) are `requires`; in one step
    /// n is accepted, both budget views move by NodeCost (total_cost += 2,
    /// budget_remaining -= 2 — the coupling), n is marked visited, and the star
    /// children are enqueued. All three invariants are re-established.
    pub fn visit_and_accept(&mut self, n: usize)
        requires
            old(self).type_invariant(),
            old(self).composition_invariant(),
            old(self).accepted_subset_visited(),
            old(self).root < old(self).num_nodes,
            n < old(self).num_nodes,
            Self::seq_contains(old(self).queue@, n),     // n ∈ queue
            !Self::seq_contains(old(self).visited@, n),  // n ∉ visited
            2 <= old(self).budget_remaining,             // NodeCost 2 <= budget_remaining
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).max_budget == old(self).max_budget,
            final(self).total_cost == old(self).total_cost + 2,
            final(self).budget_remaining == old(self).budget_remaining - 2,
            final(self).accepted@ == old(self).accepted@.push(n),
            final(self).visited@ == old(self).visited@.push(n),
            // Remove n, then add the star children exactly when n is the root.
            forall|m: usize| #[trigger] Self::seq_contains(final(self).queue@, m)
                <==> (Self::seq_contains(old(self).queue@, m) && m != n)
                     || (n == old(self).root && m < old(self).num_nodes
                         && m != old(self).root),
            final(self).type_invariant(),
            final(self).composition_invariant(),
            final(self).accepted_subset_visited(),
    {
        let ghost ov = self.visited@;
        let ghost oa = self.accepted@;

        self.queue = Self::without_node(&self.queue, n, self.num_nodes);

        // n ∉ accepted: from accepted ⊆ visited and n ∉ visited.
        assert(!Self::seq_contains(oa, n)) by {
            if Self::seq_contains(oa, n) {
                let k = choose|k: int| 0 <= k < oa.len() && oa[k] == n;
                assert(0 <= k < oa.len() && oa[k] == n);
                assert(Self::seq_contains(ov, oa[k]));   // old accepted_subset_visited at k
                assert(Self::seq_contains(ov, n));       // oa[k] == n
                assert(false);
            }
        };

        // Accept n, spend NodeCost from both views, mark visited.
        self.visited.push(n);
        assert(self.visited@ == ov.push(n));
        self.accepted.push(n);
        assert(self.accepted@ == oa.push(n));
        self.total_cost = self.total_cost + 2;
        self.budget_remaining = self.budget_remaining - 2;

        if n == self.root {
            self.enqueue_star_children();
        }

        // visited' is still a valid set.
        assert(Self::all_valid(self.visited@, self.num_nodes));
        assert(Self::all_distinct(self.visited@)) by {
            assert forall|i: int, j: int|
                0 <= i < self.visited@.len() && 0 <= j < self.visited@.len() && i != j
                implies self.visited@[i] != self.visited@[j] by {
                if i < ov.len() && j < ov.len() {
                    // both old elements: old distinctness
                } else if i == ov.len() && j < ov.len() {
                    assert(self.visited@[j] == ov[j]);
                    assert(ov[j] != n);   // n ∉ ov
                } else if j == ov.len() && i < ov.len() {
                    assert(self.visited@[i] == ov[i]);
                    assert(ov[i] != n);
                }
            }
        };

        // accepted' is still a valid set.
        assert(Self::all_valid(self.accepted@, self.num_nodes));
        assert(Self::all_distinct(self.accepted@)) by {
            assert forall|i: int, j: int|
                0 <= i < self.accepted@.len() && 0 <= j < self.accepted@.len() && i != j
                implies self.accepted@[i] != self.accepted@[j] by {
                if i < oa.len() && j < oa.len() {
                    // old distinctness
                } else if i == oa.len() && j < oa.len() {
                    assert(self.accepted@[j] == oa[j]);
                    assert(oa[j] != n);   // n ∉ oa
                } else if j == oa.len() && i < oa.len() {
                    assert(self.accepted@[i] == oa[i]);
                    assert(oa[i] != n);
                }
            }
        };

        // accepted' ⊆ visited': old members are in ov ⊆ visited'; n ∈ visited'.
        assert(self.accepted_subset_visited()) by {
            assert forall|i: int| 0 <= i < self.accepted@.len()
                implies Self::seq_contains(self.visited@, self.accepted@[i]) by {
                if i < oa.len() {
                    assert(self.accepted@[i] == oa[i]);
                    assert(Self::seq_contains(ov, oa[i]));   // old invariant at i
                    let w = choose|w: int| 0 <= w < ov.len() && ov[w] == oa[i];
                    assert(self.visited@[w] == ov[w]);       // push preserves prefix
                    assert(Self::seq_contains(self.visited@, self.accepted@[i]));
                } else {
                    assert(self.accepted@[i] == n);
                    assert(self.visited@[ov.len() as int] == n);   // pushed element
                    assert(Self::seq_contains(self.visited@, n));
                }
            }
        };
        // CompositionInvariant and the TypeInvariant budget clauses hold by
        // linear arithmetic: total_cost' + budget_remaining' = (old + 2) +
        // (old - 2) = old sum = max_budget; and from 2 <= budget_remaining and
        // the equation, total_cost' = old_total + 2 <= max_budget.
    }

    // ── SkipUnaffordable (TLA+ SkipUnaffordable) ────────────────────────

    /// Visit `n` but skip acceptance: the cost overruns the remaining budget.
    /// Realises the TLA+ `SkipUnaffordable(n)` action — its guards (n ∈ queue,
    /// n ∉ visited, NodeCost 2 > budget_remaining) are `requires`; n is marked
    /// visited but NOT accepted and the budget views are UNCHANGED, so
    /// `accepted` becomes a proper subset of `visited` when n was not already
    /// accepted.
    pub fn skip_unaffordable(&mut self, n: usize)
        requires
            old(self).type_invariant(),
            old(self).composition_invariant(),
            old(self).accepted_subset_visited(),
            n < old(self).num_nodes,
            Self::seq_contains(old(self).queue@, n),     // n ∈ queue
            !Self::seq_contains(old(self).visited@, n),  // n ∉ visited
            old(self).budget_remaining < 2,              // NodeCost 2 > budget_remaining
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).max_budget == old(self).max_budget,
            final(self).total_cost == old(self).total_cost,           // UNCHANGED
            final(self).budget_remaining == old(self).budget_remaining, // UNCHANGED
            final(self).accepted@ == old(self).accepted@,             // NOT accepted
            final(self).visited@ == old(self).visited@.push(n),
            forall|m: usize| #[trigger] Self::seq_contains(final(self).queue@, m)
                <==> Self::seq_contains(old(self).queue@, m) && m != n,
            final(self).type_invariant(),
            final(self).composition_invariant(),
            final(self).accepted_subset_visited(),
    {
        let ghost ov = self.visited@;
        let ghost oa = self.accepted@;

        self.queue = Self::without_node(&self.queue, n, self.num_nodes);

        // Mark n visited; accepted unchanged.
        self.visited.push(n);
        assert(self.visited@ == ov.push(n));

        // visited' is still a valid set.
        assert(Self::all_valid(self.visited@, self.num_nodes));
        assert(Self::all_distinct(self.visited@)) by {
            assert forall|i: int, j: int|
                0 <= i < self.visited@.len() && 0 <= j < self.visited@.len() && i != j
                implies self.visited@[i] != self.visited@[j] by {
                if i < ov.len() && j < ov.len() {
                    // old distinctness
                } else if i == ov.len() && j < ov.len() {
                    assert(self.visited@[j] == ov[j]);
                    assert(ov[j] != n);
                } else if j == ov.len() && i < ov.len() {
                    assert(self.visited@[i] == ov[i]);
                    assert(ov[i] != n);
                }
            }
        };

        // accepted' ⊆ visited': accepted unchanged; every old member is still
        // in visited (which only grew) — the proper-subset case.
        assert(self.accepted_subset_visited()) by {
            assert forall|i: int| 0 <= i < self.accepted@.len()
                implies Self::seq_contains(self.visited@, self.accepted@[i]) by {
                assert(Self::seq_contains(ov, oa[i]));   // old invariant at i
                let w = choose|w: int| 0 <= w < ov.len() && ov[w] == oa[i];
                assert(self.visited@[w] == ov[w]);
                assert(Self::seq_contains(self.visited@, self.accepted@[i]));
            }
        };
    }

    // ── Skip (TLA+ Skip) ────────────────────────────────────────────────

    /// Drop a queued node without visiting it. All other state is unchanged.
    pub fn skip(&mut self, n: usize)
        requires
            old(self).type_invariant(),
            old(self).composition_invariant(),
            old(self).accepted_subset_visited(),
            Self::seq_contains(old(self).queue@, n),   // n ∈ queue
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).root == old(self).root,
            final(self).max_budget == old(self).max_budget,
            final(self).total_cost == old(self).total_cost,
            final(self).budget_remaining == old(self).budget_remaining,
            final(self).accepted@ == old(self).accepted@,
            final(self).visited@ == old(self).visited@,
            forall|m: usize| #[trigger] Self::seq_contains(final(self).queue@, m)
                <==> Self::seq_contains(old(self).queue@, m) && m != n,
            final(self).type_invariant(),
            final(self).composition_invariant(),
            final(self).accepted_subset_visited(),
    {
        self.queue = Self::without_node(&self.queue, n, self.num_nodes);
    }
}

}
