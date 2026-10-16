//! Finite-index StepGraph execution carrier.

use crate::connectives::counter::Counter;
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

mod step_graph_storage_seal { pub trait Sealed {} }

/// Physical node-state binding beneath the one StepGraph transition owner.
pub trait StepGraphStates: step_graph_storage_seal::Sealed + View<V = Seq<StepGraphNodeState>> {
    /// Exact retained node count.
    fn len(&self) -> (length: usize) ensures length == self@.len();
    /// Whether the retained node set is empty.
    fn is_empty(&self) -> (empty: bool) ensures empty == (self@.len() == 0),
    { self.len() == 0 }
    /// Read one node without changing its state.
    fn state_at(&self, node: usize) -> (state: StepGraphNodeState)
        requires node < self@.len(), ensures state == self@[node as int];
    /// Replace one state; the StepGraph action supplies the dependency guard.
    fn set_state(&mut self, node: usize, state: StepGraphNodeState)
        requires node < old(self)@.len(),
        ensures final(self)@ == old(self)@.update(node as int, state);
    /// Observe the exact quantified completion predicate.
    fn all_complete(&self) -> (complete: bool)
        ensures complete == (forall|i: int| 0 <= i < self@.len()
            ==> #[trigger] self@[i] == StepGraphNodeState::Complete);
}

impl step_graph_storage_seal::Sealed for Vec<StepGraphNodeState> {}
impl StepGraphStates for Vec<StepGraphNodeState> {
    fn len(&self) -> (length: usize) { self.len() }
    #[expect(clippy::indexing_slicing, reason = "the storage contract bounds the node index")]
    fn state_at(&self, node: usize) -> (state: StepGraphNodeState) { self[node] }
    fn set_state(&mut self, node: usize, state: StepGraphNodeState) {
        vstd::pervasive::VecAdditionalExecFns::set(self, node, state);
    }
    #[expect(clippy::indexing_slicing, reason = "the scan cursor is bounded by the retained node count")]
    #[expect(clippy::arithmetic_side_effects, reason = "the scan advances only below the node count")]
    fn all_complete(&self) -> (complete: bool) {
        let mut i = 0;
        while i < self.len()
            invariant i <= self.len(),
                forall|k: int| 0 <= k < i ==> self@[k] == StepGraphNodeState::Complete,
            decreases self.len() - i,
        {
            if !matches!(self[i], StepGraphNodeState::Complete) { return false; }
            i += 1;
        }
        true
    }
}

spec fn unfinished_tag(state: StepGraphNodeState) -> nat {
    if state == StepGraphNodeState::Complete { 0 } else { 1 }
}
spec fn unfinished_prefix(states: Seq<StepGraphNodeState>, end: int) -> nat
    decreases end,
{
    if end <= 0 || end > states.len() { 0 }
    else { unfinished_prefix(states, end - 1) + unfinished_tag(states[end - 1]) }
}
proof fn unfinished_prefix_bounds(states: Seq<StepGraphNodeState>, end: int)
    requires 0 <= end <= states.len(),
    ensures unfinished_prefix(states, end) <= end,
        (unfinished_prefix(states, end) == 0) <==> (forall|i: int| 0 <= i < end
            ==> #[trigger] states[i] == StepGraphNodeState::Complete),
    decreases end,
{
    reveal_with_fuel(unfinished_prefix, 2);
    if end > 0 {
        unfinished_prefix_bounds(states, end - 1);
        assert forall|i: int| 0 <= i < end && unfinished_prefix(states, end) == 0
            implies #[trigger] states[i] == StepGraphNodeState::Complete by {
            if i < end - 1 { assert(states[i] == StepGraphNodeState::Complete); }
        }
    }
}
proof fn unfinished_prefix_initial(states: Seq<StepGraphNodeState>, end: int)
    requires 0 <= end <= states.len(),
        forall|i: int| 0 <= i < end ==> #[trigger] states[i] != StepGraphNodeState::Complete,
    ensures unfinished_prefix(states, end) == end,
    decreases end,
{
    reveal_with_fuel(unfinished_prefix, 2);
    if end > 0 { unfinished_prefix_initial(states, end - 1); }
}
proof fn unfinished_prefix_update(states: Seq<StepGraphNodeState>, node: int,
    state: StepGraphNodeState, end: int)
    requires 0 <= node < states.len(), 0 <= end <= states.len(),
    ensures unfinished_prefix(states.update(node, state), end)
            + (if node < end { unfinished_tag(states[node]) } else { 0 })
        == unfinished_prefix(states, end)
            + (if node < end { unfinished_tag(state) } else { 0 }),
    decreases end,
{
    reveal_with_fuel(unfinished_prefix, 2);
    if end > 0 { unfinished_prefix_update(states, node, state, end - 1); }
}

type CountedStepGraph = StepGraph<CountedStepStates>;

/// Checked layout: retained node tags coupled to their canonical unfinished Counter.
pub struct CountedStepStates { data: CountedStepData }
struct CountedStepData { states: Vec<StepGraphNodeState>, unfinished: Counter }
impl CountedStepData {
    // Finish the bounded Copy update before exposing the whole retained-data frame.
    #[inline(always)]
    #[expect(clippy::indexing_slicing, reason = "the private helper contract bounds the node index")]
    fn set_incomplete_state(&mut self, node: usize, state: StepGraphNodeState)
        requires node < old(self).states@.len(),
            old(self).states@[node as int] != StepGraphNodeState::Complete,
            state != StepGraphNodeState::Complete,
        ensures final(self).states@ == old(self).states@.update(node as int, state),
            final(self).unfinished == old(self).unfinished,
        no_unwind
    {
        let slot = &mut self.states[node];
        *slot = state;
    }
}
impl step_graph_storage_seal::Sealed for CountedStepStates {}
impl View for CountedStepStates {
    type V = Seq<StepGraphNodeState>;
    closed spec fn view(&self) -> Seq<StepGraphNodeState> { self.data.states@ }
}
impl CountedStepStates {
    /// Borrow the actual state tags without exposing a mutable writer.
    pub(crate) fn as_slice(&self) -> (states: &[StepGraphNodeState])
        ensures states@ == self@,
    { self.data.states.as_slice() }
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.data.states@.len() <= u64::MAX as nat
            && self.data.unfinished.value_spec() == unfinished_prefix(self.data.states@, self.data.states@.len() as int)
    }
    fn from_initial(states: Vec<StepGraphNodeState>) -> (counted: Self)
        requires states@.len() <= u64::MAX as nat,
            forall|i: int| 0 <= i < states@.len()
                ==> #[trigger] states@[i] != StepGraphNodeState::Complete,
        ensures counted@ == states@,
    {
        proof { unfinished_prefix_initial(states@, states@.len() as int); }
        let count = states.len();
        Self { data: CountedStepData { states, unfinished: Counter::new(count as u64) } }
    }
}
impl StepGraphStates for CountedStepStates {
    fn len(&self) -> (length: usize) { self.data.states.len() }
    #[expect(clippy::indexing_slicing, reason = "the storage contract bounds the node index")]
    fn state_at(&self, node: usize) -> (state: StepGraphNodeState) { self.data.states[node] }
    #[expect(clippy::indexing_slicing, reason = "the storage contract bounds the node index")]
    fn set_state(&mut self, node: usize, state: StepGraphNodeState) {
        proof { use_type_invariant(&*self); }
        let previous = self.data.states[node];
        if !matches!(previous, StepGraphNodeState::Complete) && !matches!(state, StepGraphNodeState::Complete) {
            let ghost before = self.data.states@;
            proof {
                unfinished_prefix_update(before, node as int, state, before.len() as int);
                assert(unfinished_prefix(before.update(node as int, state), before.len() as int)
                    == unfinished_prefix(before, before.len() as int));
            }
            self.data.set_incomplete_state(node, state);
            return;
        }

        // Retain a valid empty carrier while updating data whose calls may unwind.
        let mut data = CountedStepData { states: Vec::new(), unfinished: Counter::new(0) };
        core::mem::swap(&mut self.data, &mut data);
        let ghost before = data.states@;
        let previous = data.states[node];
        proof { unfinished_prefix_update(before, node as int, state, before.len() as int); }
        if matches!(previous, StepGraphNodeState::Complete) && !matches!(state, StepGraphNodeState::Complete) {
            proof { unfinished_prefix_bounds(before.update(node as int, state), before.len() as int); }
            let _incremented = data.unfinished.try_increment();
            assert(_incremented);
        } else if !matches!(previous, StepGraphNodeState::Complete) && matches!(state, StepGraphNodeState::Complete) {
            let _decremented = data.unfinished.try_decrement();
            assert(_decremented);
        }
        data.states.set(node, state);
        core::mem::swap(&mut self.data, &mut data);
    }
    fn all_complete(&self) -> (complete: bool) {
        proof {
            use_type_invariant(self);
            unfinished_prefix_bounds(self.data.states@, self.data.states@.len() as int);
        }
        self.data.unfinished.value() == 0
    }
}

/// Predecessor-governed step-graph owner.
pub struct StepGraph<S: StepGraphStates = Vec<StepGraphNodeState>> {
    /// Number of execution nodes.
    pub num_nodes: usize,
    /// Directed predecessor edges.
    pub edges: Vec<(usize, usize)>,
    /// Lifecycle state by node index.
    pub nstate: S,
}

impl StepGraph {
    /// Whether every dependency edge names two valid nodes.
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

}

impl<S: StepGraphStates> StepGraph<S> {
    /// Whether node states and dependency edges have valid shape and values.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.nstate@.len() == self.num_nodes
        &&& StepGraph::edges_valid(self.edges@, self.num_nodes)
        &&& StepGraph::edges_distinct(self.edges@)
    }

    /// Whether readiness agrees with predecessor completion.
    pub open spec fn eligibility_closed(&self) -> bool {
        forall|n: usize| n < self.num_nodes
            && #[trigger] self.nstate@[n as int] != StepGraphNodeState::NotReady
            ==> StepGraph::predecessors_complete_in(self.edges@, self.nstate@, n)
    }

    /// Derived consequence of `eligibility_closed`: no node runs or completes before all
    /// predecessors complete.
    pub open spec fn no_run_before_predecessors(&self) -> bool {
        forall|n: usize| n < self.num_nodes
            && (#[trigger] self.nstate@[n as int] == StepGraphNodeState::Running
                || self.nstate@[n as int] == StepGraphNodeState::Complete)
            ==> StepGraph::predecessors_complete_in(self.edges@, self.nstate@, n)
    }

    /// Whether all dependency-ordered execution contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.eligibility_closed()
    }

}

impl StepGraph {
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

}

impl<S: StepGraphStates> StepGraph<S> {
    #[expect(clippy::indexing_slicing, reason = "the type invariant and loop invariant bound edge and predecessor-state indices")]
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves the predecessor-completion cursor increment remains in bounds")]
    /// Observe the exact predecessor-completion predicate used by readiness admission.
    pub fn predecessors_complete_exec(&self, node: usize) -> (b: bool)
        requires
            self.type_invariant(),
            node < self.num_nodes,
        ensures b == StepGraph::predecessors_complete_in(self.edges@, self.nstate@, node),
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
                    self.nstate.state_at(self.edges[i].0),
                    StepGraphNodeState::Complete
                )
            {
                assert(!StepGraph::predecessors_complete_in(self.edges@, self.nstate@, node));
                return false;
            }
            i += 1;
        }
        true
    }

}

impl StepGraph {
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
        Self::initialize(num_nodes, edges, Vec::new())
    }

    /// Reserve lifecycle storage before constructing the admitted dependency owner.
    /// The raw proof API retains the existing edge-domain preconditions.
    ///
    /// # Errors
    /// Returns the allocation error and the unconsumed edge data on reservation failure.
    pub fn try_new(num_nodes: usize, edges: Vec<(usize, usize)>)
        -> (result: Result<Self, (std::collections::TryReserveError, Vec<(usize, usize)>)>)
        requires Self::edges_valid(edges@, num_nodes), Self::edges_distinct(edges@),
        ensures
            result is Err ==> (result->Err_0).1@ == edges@,
            result is Ok ==> {
                let s = result.unwrap();
                &&& s.num_nodes == num_nodes
                &&& s.edges@ == edges@
                &&& s.nstate@.len() == num_nodes
                &&& forall|n: usize| n < num_nodes ==> #[trigger] s.nstate@[n as int]
                    == if Self::has_predecessor_in(edges@, n) {
                        StepGraphNodeState::NotReady
                    } else { StepGraphNodeState::Ready }
                &&& s.inv()
                &&& s.no_run_before_predecessors()
            },
    {
        let mut nstate = Vec::<StepGraphNodeState>::new();
        if let Err(error) = nstate.try_reserve(num_nodes) { return Err((error, edges)); }
        Ok(Self::initialize(num_nodes, edges, nstate))
    }

    #[expect(clippy::indexing_slicing, reason = "the processed-edge cursor and valid topology bound each destination state update")]
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves node and edge construction cursors remain within their fixed bounds")]
    fn initialize(num_nodes: usize, edges: Vec<(usize, usize)>, mut nstate: Vec<StepGraphNodeState>) -> (s: StepGraph)
        requires
            nstate@.len() == 0,
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
        let mut n = 0;
        while n < num_nodes
            invariant
                n <= num_nodes,
                nstate@.len() == n,
                forall|k: usize| k < n ==>
                    #[trigger] nstate@[k as int] == StepGraphNodeState::Ready,
            decreases num_nodes - n,
        {
            nstate.push(StepGraphNodeState::Ready);
            n += 1;
        }
        let mut e = 0;
        while e < edges.len()
            invariant
                e <= edges.len(),
                Self::edges_valid(edges@, num_nodes),
                nstate@.len() == num_nodes,
                forall|node: usize| node < num_nodes ==>
                    #[trigger] nstate@[node as int]
                        == if exists|k: int| 0 <= k < e && edges@[k].1 == node {
                            StepGraphNodeState::NotReady
                        } else { StepGraphNodeState::Ready },
            decreases edges.len() - e,
        {
            let target = edges[e].1;
            proof {
                assert(0 <= e < edges@.len());
                assert(edges@[e as int].0 < num_nodes);
                assert(edges@[e as int].1 < num_nodes);
                assert(target == edges@[e as int].1);
                assert(target < nstate@.len());
            }
            let ghost before = nstate@;
            nstate.set(target, StepGraphNodeState::NotReady);
            proof {
                assert(nstate@ == before.update(target as int, StepGraphNodeState::NotReady));
                assert(nstate@.len() == num_nodes);
            }
            assert forall|node: usize| node < num_nodes implies
                #[trigger] nstate@[node as int]
                    == if exists|k: int| 0 <= k < e + 1 && edges@[k].1 == node {
                        StepGraphNodeState::NotReady
                    } else { StepGraphNodeState::Ready } by {
                if node == target {
                    assert(edges@[e as int].1 == node);
                    assert(exists|k: int| 0 <= k < e + 1 && edges@[k].1 == node);
                } else {
                    assert((exists|k: int| 0 <= k < e + 1 && edges@[k].1 == node)
                        == (exists|k: int| 0 <= k < e && edges@[k].1 == node)) by {
                        if exists|k: int| 0 <= k < e + 1 && edges@[k].1 == node {
                            let k = choose|k: int| 0 <= k < e + 1 && edges@[k].1 == node;
                            assert(k != e);
                            assert(k < e);
                        }
                    }
                    assert(nstate@[node as int] == before[node as int]);
                }
            }
            e += 1;
        }
        assert forall|node: usize| node < num_nodes implies
            #[trigger] nstate@[node as int]
                == if Self::has_predecessor_in(edges@, node) {
                    StepGraphNodeState::NotReady
                } else { StepGraphNodeState::Ready } by {}
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

    /// Fallibly construct the counted layout under the same topology contract.
    ///
    /// # Errors
    ///
    /// Reservation failure returns the original edge data without an initialized owner.
    pub fn try_new_counted(num_nodes: usize, edges: Vec<(usize, usize)>)
        -> (result: Result<CountedStepGraph, (std::collections::TryReserveError, Vec<(usize, usize)>)>)
        requires Self::edges_valid(edges@, num_nodes), Self::edges_distinct(edges@),
            num_nodes as nat <= u64::MAX as nat,
        ensures
            result is Err ==> (result->Err_0).1@ == edges@,
            result is Ok ==> {
                let s = result->Ok_0;
                &&& s.num_nodes == num_nodes
                &&& s.edges@ == edges@
                &&& s.nstate@.len() == num_nodes
                &&& s.inv()
                &&& s.no_run_before_predecessors()
                &&& forall|n: usize| n < num_nodes ==> #[trigger] s.nstate@[n as int]
                    == if Self::has_predecessor_in(edges@, n) {
                        StepGraphNodeState::NotReady
                    } else { StepGraphNodeState::Ready }
            },
    {
        let raw = Self::try_new(num_nodes, edges)?;
        proof {
            assert forall|i: int| 0 <= i < raw.nstate@.len()
                implies #[trigger] raw.nstate@[i] != StepGraphNodeState::Complete by {
                let n = i as usize;
                assert(n < num_nodes);
            }
        }
        let nstate = CountedStepStates::from_initial(raw.nstate);
        Ok(StepGraph { num_nodes: raw.num_nodes, edges: raw.edges, nstate })
    }

    /// Construct the counted checked layout without repeating topology initialization.
    pub(crate) fn new_counted(num_nodes: usize, edges: Vec<(usize, usize)>)
        -> (s: StepGraph<CountedStepStates>)
        requires Self::edges_valid(edges@, num_nodes), Self::edges_distinct(edges@),
            num_nodes as nat <= u64::MAX as nat,
        ensures s.num_nodes == num_nodes, s.edges@ == edges@,
            s.nstate@.len() == num_nodes, s.inv(), s.no_run_before_predecessors(),
            forall|n: usize| n < num_nodes ==> #[trigger] s.nstate@[n as int]
                == if Self::has_predecessor_in(edges@, n) {
                    StepGraphNodeState::NotReady
                } else { StepGraphNodeState::Ready },
    {
        let raw = Self::new(num_nodes, edges);
        proof {
            assert forall|i: int| 0 <= i < raw.nstate@.len()
                implies #[trigger] raw.nstate@[i] != StepGraphNodeState::Complete by {
                let n = i as usize;
                assert(n < num_nodes);
            }
        }
        let nstate = CountedStepStates::from_initial(raw.nstate);
        StepGraph { num_nodes: raw.num_nodes, edges: raw.edges, nstate }
    }
}

impl<S: StepGraphStates> StepGraph<S> {
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
                StepGraph::has_predecessor_in(old(self).edges@, node)
                    && StepGraph::predecessors_complete_in(
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
            && matches!(self.nstate.state_at(node), StepGraphNodeState::NotReady)
            && StepGraph::has_predecessor_exec(&self.edges, node)
            && self.predecessors_complete_exec(node)
        {
            let ghost old_states = self.nstate@;
            self.nstate.set_state(node, StepGraphNodeState::Ready);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] != StepGraphNodeState::NotReady
                    implies StepGraph::predecessors_complete_in(self.edges@, self.nstate@, m) by {
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
                        assert(StepGraph::predecessors_complete_in(self.edges@, old_states, m));
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

    /// Observe the owner's exact Start guard without changing lifecycle state.
    pub(crate) fn can_start_ready(&self, node: usize) -> (ready: bool)
        requires self.inv(),
        ensures ready == (node < self.num_nodes
            && self.nstate@[node as int] == StepGraphNodeState::Ready),
    {
        node < self.num_nodes && matches!(self.nstate.state_at(node), StepGraphNodeState::Ready)
    }

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
        if self.can_start_ready(node) {
            let ghost old_states = self.nstate@;
            self.nstate.set_state(node, StepGraphNodeState::Running);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] != StepGraphNodeState::NotReady
                    implies StepGraph::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    assert(StepGraph::predecessors_complete_in(self.edges@, old_states, m));
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
        if node < self.num_nodes && matches!(self.nstate.state_at(node), StepGraphNodeState::Running) {
            let ghost old_states = self.nstate@;
            self.nstate.set_state(node, StepGraphNodeState::Complete);
            assert(self.eligibility_closed()) by {
                assert forall|m: usize| m < self.num_nodes
                    && #[trigger] self.nstate@[m as int] != StepGraphNodeState::NotReady
                    implies StepGraph::predecessors_complete_in(self.edges@, self.nstate@, m) by {
                    assert(StepGraph::predecessors_complete_in(self.edges@, old_states, m));
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

    /// Observe the canonical owner's all-nodes-complete predicate.
    pub(crate) fn all_nodes_complete(&self) -> (complete: bool)
        requires self.inv(),
        ensures
            complete == (forall|i: int| 0 <= i < self.nstate@.len()
                ==> #[trigger] self.nstate@[i] == StepGraphNodeState::Complete),
    {
        self.nstate.all_complete()
    }

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
    { self.all_nodes_complete() }
}

}
