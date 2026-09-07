// Executable PropagationPassGraph contract. The graph is
// immutable, each round snapshots the values, UpdateNode commits one local
// combine from that snapshot, and EndRound alone charges the iteration and
// records whether the round changed anything.
//
// Edges are directed (source, target) pairs. The default domain combine is
// the TLA+ miniature: if any in-neighbour has a smaller snapshot value, the
// target decreases by one; otherwise it retains its snapshot value.

use crate::value_eq::ValueEq;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// Lifecycle state of a propagation round.
pub enum Round {
    /// No round is active.
    Idle,
    /// Nodes are committing updates from the retained snapshot.
    Running,
}

/// Whether node `n` has an incoming neighbor with a smaller snapshot value.
pub open spec fn has_better_in_neighbor(
    edges: Seq<(usize, usize)>,
    snapshot: Seq<u64>,
    n: usize,
) -> bool {
    exists|i: int| 0 <= i < edges.len()
        && edges[i].1 == n
        && snapshot[edges[i].0 as int] < snapshot[n as int]
}

/// Compute node `n`'s next value from the retained round snapshot.
pub open spec fn local_combine(
    edges: Seq<(usize, usize)>,
    snapshot: Seq<u64>,
    n: usize,
) -> int {
    if has_better_in_neighbor(edges, snapshot, n) {
        snapshot[n as int] as int - 1
    } else {
        snapshot[n as int] as int
    }
}

/// Pure data operation for one snapshot-local update. It has no mutable owner access.
pub trait PropagationDomain<T: Copy + ValueEq> {
    /// Membership of a retained value in this domain.
    spec fn contains(&self, value: T) -> bool;
    /// Whether the selected snapshot update is defined.
    spec fn accepts(&self, edges: Seq<(usize, usize)>, snapshot: Seq<T>, node: usize) -> bool;
    /// Mathematical result, depending only on this domain and the common snapshot.
    spec fn combined(&self, edges: Seq<(usize, usize)>, snapshot: Seq<T>, node: usize) -> T;
    /// Decide domain eligibility without changing the pass.
    fn accepts_exec(&self, edges: &Vec<(usize, usize)>, snapshot: &Vec<T>, node: usize) -> (yes: bool)
        requires node < snapshot.len(),
            forall|i: int| 0 <= i < snapshot.len() ==> self.contains(#[trigger] snapshot@[i]),
            forall|i: int| 0 <= i < edges.len() ==> #[trigger] edges@[i].0 < snapshot.len() && edges@[i].1 < snapshot.len(),
        ensures yes == self.accepts(edges@, snapshot@, node);
    /// Compute the admitted result and prove closure in the retained value domain.
    fn combine(&self, edges: &Vec<(usize, usize)>, snapshot: &Vec<T>, node: usize) -> (value: T)
        requires node < snapshot.len(),
            forall|i: int| 0 <= i < snapshot.len() ==> self.contains(#[trigger] snapshot@[i]),
            forall|i: int| 0 <= i < edges.len() ==> #[trigger] edges@[i].0 < snapshot.len() && edges@[i].1 < snapshot.len(),
            self.accepts(edges@, snapshot@, node),
        ensures value == self.combined(edges@, snapshot@, node), self.contains(value);
}

/// Admissible graph indices and domain values for a snapshot operation.
pub open spec fn valid_input<T: Copy + ValueEq, D: PropagationDomain<T> + ?Sized>(
    domain: &D, edges: Seq<(usize, usize)>, values: Seq<T>,
) -> bool {
    &&& forall|i: int| 0 <= i < values.len() ==> domain.contains(#[trigger] values[i])
    &&& forall|i: int| 0 <= i < edges.len() ==> #[trigger] edges[i].0 < values.len() && edges[i].1 < values.len()
}

impl PropagationDomain<u64> for u64 {
    open spec fn contains(&self, value: u64) -> bool { value <= *self }
    open spec fn accepts(&self, _edges: Seq<(usize,usize)>, _snapshot: Seq<u64>, _node: usize) -> bool { true }
    open spec fn combined(&self, edges: Seq<(usize,usize)>, snapshot: Seq<u64>, node: usize) -> u64 {
        local_combine(edges, snapshot, node) as u64
    }
    fn accepts_exec(&self, _edges: &Vec<(usize,usize)>, _snapshot: &Vec<u64>, _node: usize) -> (yes: bool) { true }
    fn combine(&self, edges: &Vec<(usize,usize)>, snapshot: &Vec<u64>, node: usize) -> (value: u64) {
        default_combine(*self, edges, snapshot, node)
    }
}

/// Snapshot-local bounded propagation owner.
pub struct PropagationPass<T: Copy + ValueEq = u64, D: PropagationDomain<T> = u64> {
    /// Number of graph nodes.
    pub num_nodes: usize,
    /// Maximum completed propagation rounds.
    pub max_iterations: u64,
    /// Pure value-domain configuration; the default is the inclusive value ceiling.
    pub max_value: D,
    /// Directed propagation edges.
    pub edges: Vec<(usize, usize)>,
    /// Current node values.
    pub values: Vec<T>,
    /// Immutable values captured at round start.
    pub snapshot: Vec<T>,
    /// Per-node update markers for the active or latest round.
    pub updated: Vec<bool>,
    /// Number of completed rounds.
    pub iteration: u64,
    /// Whether the latest completed round changed any value.
    pub changed: bool,
    /// Current round lifecycle.
    pub round: Round,
}

impl<T: Copy + ValueEq, D: PropagationDomain<T>> PropagationPass<T, D> {
    // -- Specifications --------------------------------------------------

    /// Whether graph, value, snapshot, and marker storage have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.values.len() == self.num_nodes
        &&& self.snapshot.len() == self.num_nodes
        &&& self.updated.len() == self.num_nodes
        &&& (forall|i: int| 0 <= i < self.values.len()
                ==> self.max_value.contains(#[trigger] self.values@[i]))
        &&& (forall|i: int| 0 <= i < self.snapshot.len()
                ==> self.max_value.contains(#[trigger] self.snapshot@[i]))
        &&& (forall|i: int| 0 <= i < self.edges.len()
                ==> #[trigger] self.edges@[i].0 < self.num_nodes
                    && self.edges@[i].1 < self.num_nodes)
    }

    /// Whether the completed-round count remains within its configured ceiling.
    pub open spec fn iteration_bound(&self) -> bool {
        self.iteration <= self.max_iterations
    }

    /// Whether an active round has remaining iteration capacity.
    pub open spec fn round_bound(&self) -> bool {
        self.round == Round::Running ==> self.iteration < self.max_iterations
    }

    /// Whether the active-round state retains its provisional changed marker.
    pub open spec fn running_changed(&self) -> bool {
        self.round == Round::Running ==> self.changed
    }

    /// Whether every graph node has committed its update for the round.
    pub open spec fn all_updated(&self) -> bool {
        forall|i: int| 0 <= i < self.updated.len() ==> #[trigger] self.updated@[i]
    }

    /// TLA+ `SnapshotLocality`: every node committed in this round is the local
    /// combine of the shared round-start snapshot.
    pub open spec fn snapshot_locality(&self) -> bool {
        forall|i: int| 0 <= i < self.updated.len() && #[trigger] self.updated@[i]
            ==> self.values@[i] == self.max_value.combined(self.edges@, self.snapshot@, i as usize)
    }

    /// Whether an unchanged completed round preserved the full snapshot.
    pub open spec fn settled_ok(&self) -> bool {
        !self.changed ==> self.values@ == self.snapshot@ && self.all_updated()
    }

    /// Whether all propagation-pass contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.iteration_bound()
        &&& self.round_bound()
        &&& self.running_changed()
        &&& self.settled_ok()
        &&& self.snapshot_locality()
    }

    /// Whether execution settled or exhausted its admitted round count.
    pub open spec fn settled_or_iteration_limit(&self) -> bool {
        !self.changed || self.iteration == self.max_iterations
    }

    /// Fallibly admit both node-sized work arrays before creating the owner.
    ///
    /// # Errors
    /// Returns the allocation error, domain and original graph/value inputs.
    #[allow(clippy::type_complexity)]
    pub fn try_new(num_nodes: usize, max_iterations: u64, max_value: D,
        edges: Vec<(usize,usize)>, init_values: Vec<T>)
        -> (result: Result<Self, (std::collections::TryReserveError, D, Vec<(usize,usize)>, Vec<T>)>)
        requires init_values.len() == num_nodes, valid_input(&max_value, edges@, init_values@),
        ensures match result {
            Ok(p) => p.inv() && p.num_nodes == num_nodes && p.max_iterations == max_iterations
                && p.max_value == max_value && p.edges@ == edges@ && p.values@ == init_values@
                && p.snapshot@ == init_values@ && p.iteration == 0 && p.changed && p.round == Round::Idle
                && forall|i: int| 0 <= i < p.updated.len() ==> !p.updated@[i],
            Err((_, domain, graph, values)) => domain == max_value && graph == edges && values == init_values,
        },
    {
        let mut snapshot = Vec::new();
        if let Err(e) = snapshot.try_reserve(num_nodes) { return Err((e, max_value, edges, init_values)); }
        let mut updated = Vec::new();
        if let Err(e) = updated.try_reserve(num_nodes) { return Err((e, max_value, edges, init_values)); }
        Ok(Self::initialize(num_nodes, max_iterations, max_value, edges, init_values, snapshot, updated))
    }

    fn initialize(num_nodes: usize, max_iterations: u64, max_value: D,
        edges: Vec<(usize,usize)>, init_values: Vec<T>, mut snapshot: Vec<T>, mut updated: Vec<bool>) -> (p: Self)
        requires init_values.len() == num_nodes, valid_input(&max_value, edges@, init_values@),
            snapshot.len() == 0, updated.len() == 0,
        ensures p.inv(), p.num_nodes == num_nodes, p.max_iterations == max_iterations, p.max_value == max_value,
            p.edges@ == edges@, p.values@ == init_values@, p.snapshot@ == init_values@,
            p.iteration == 0, p.changed, p.round == Round::Idle,
            forall|i: int| 0 <= i < p.updated.len() ==> !p.updated@[i],
    {
        let mut i: usize = 0;
        while i < num_nodes
            invariant i <= num_nodes, num_nodes == init_values.len(), snapshot.len() == i, updated.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] snapshot@[k] == init_values@[k],
                forall|k: int| 0 <= k < i ==> !#[trigger] updated@[k],
            decreases num_nodes - i,
        {
            snapshot.push(init_values[i]); updated.push(false); i = i + 1;
        }
        assert(snapshot@ =~= init_values@);
        Self { num_nodes, max_iterations, max_value, edges, values: init_values, snapshot, updated,
            iteration: 0, changed: true, round: Round::Idle }
    }

    /// Commit one eligible node from the immutable round snapshot, or refuse unchanged.
    pub fn try_update_node(&mut self, n: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures final(self).inv(),
            accepted == (old(self).round == Round::Running && n < old(self).num_nodes
                && !old(self).updated@[n as int] && old(self).max_value.accepts(old(self).edges@,old(self).snapshot@,n)),
            !accepted ==> *final(self) == *old(self),
            final(self).num_nodes == old(self).num_nodes, final(self).max_iterations == old(self).max_iterations,
            final(self).max_value == old(self).max_value, final(self).edges@ == old(self).edges@,
            final(self).snapshot@ == old(self).snapshot@, final(self).iteration == old(self).iteration,
            final(self).changed == old(self).changed, final(self).round == old(self).round,
            accepted ==> final(self).values@ == old(self).values@.update(n as int,
                old(self).max_value.combined(old(self).edges@,old(self).snapshot@,n)),
            accepted ==> final(self).updated@ == old(self).updated@.update(n as int,true),
    {
        match self.round { Round::Idle => { return false; }, Round::Running => {} }
        if n >= self.num_nodes { return false; }
        if self.updated[n] { return false; }
        if !self.max_value.accepts_exec(&self.edges, &self.snapshot, n) { return false; }
        assert(old(self).round == Round::Running && n < old(self).num_nodes && !old(self).updated@[n as int]);
        assert(old(self).max_value.accepts(old(self).edges@,old(self).snapshot@,n));
        let next = self.max_value.combine(&self.edges, &self.snapshot, n);
        self.values.set(n, next); self.updated.set(n, true);
        assert(self.snapshot_locality()) by {
            assert forall|i: int| 0 <= i < self.updated.len() && self.updated@[i]
                implies self.values@[i] == self.max_value.combined(self.edges@,self.snapshot@,i as usize) by {
                if i == n as int {} else {
                    assert(self.values@[i] == old(self).values@[i]);
                    assert(self.updated@[i] == old(self).updated@[i]);
                }
            }
        }
        true
    }

    // -- Init ------------------------------------------------------------

    // -- Executable queries ---------------------------------------------

    /// Whether every node committed its update in the current round.
    pub fn all_nodes_updated(&self) -> (b: bool)
        requires self.type_invariant(),
        ensures b == self.all_updated(),
    {
        let n = self.updated.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.updated.len(),
                forall|k: int| 0 <= k < i ==> self.updated@[k],
            decreases n - i,
        {
            if !self.updated[i] {
                assert(!self.all_updated());
                return false;
            }
            i = i + 1;
        }
        assert(self.all_updated());
        true
    }

    // -- Round actions ---------------------------------------------------

    /// TLA+ `StartRound`: capture the common snapshot and clear the update set.
    pub fn start_round(&mut self)
        requires
            old(self).inv(),
            old(self).round == Round::Idle,
            old(self).changed,
            old(self).iteration < old(self).max_iterations,
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_iterations == old(self).max_iterations,
            final(self).max_value == old(self).max_value,
            final(self).edges@ == old(self).edges@,
            final(self).values@ == old(self).values@,
            final(self).snapshot@ == old(self).values@,
            forall|i: int| 0 <= i < final(self).updated.len() ==> !final(self).updated@[i],
            final(self).iteration == old(self).iteration,
            final(self).changed == old(self).changed,
            final(self).round == Round::Running,
            final(self).inv(),
    {
        let mut i: usize = 0;
        while i < self.num_nodes
            invariant
                i <= self.num_nodes,
                self.type_invariant(),
                self.num_nodes == old(self).num_nodes,
                self.max_iterations == old(self).max_iterations,
                self.max_value == old(self).max_value,
                self.edges@ == old(self).edges@,
                self.values@ == old(self).values@,
                self.iteration == old(self).iteration,
                self.changed == old(self).changed,
                forall|k: int| 0 <= k < i ==> #[trigger] self.snapshot@[k] == self.values@[k],
                forall|k: int| 0 <= k < i ==> !#[trigger] self.updated@[k],
            decreases self.num_nodes - i,
        {
            self.snapshot.set(i, self.values[i]);
            self.updated.set(i, false);
            i = i + 1;
        }
        assert(self.snapshot@ =~= old(self).values@);
        self.round = Round::Running;
    }

    /// TLA+ `EndRound`: require full coverage, detect movement, and charge once.
    pub fn end_round(&mut self)
        requires
            old(self).inv(),
            old(self).round == Round::Running,
            old(self).all_updated(),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_iterations == old(self).max_iterations,
            final(self).max_value == old(self).max_value,
            final(self).edges@ == old(self).edges@,
            final(self).values@ == old(self).values@,
            final(self).snapshot@ == old(self).snapshot@,
            final(self).updated@ == old(self).updated@,
            crate::connectives::counter::increment(
                old(self).iteration as int,
                final(self).iteration as int,
            ),
            final(self).changed == (old(self).values@ != old(self).snapshot@),
            final(self).round == Round::Idle,
            final(self).inv(),
    {
        let differ = !vectors_equal(&self.values, &self.snapshot);
        self.changed = differ;
        self.iteration = self.iteration + 1;
        self.round = Round::Idle;
    }

    /// TLA+ `Terminate`: an idle self-loop at a fixed point or the ceiling.
    pub fn terminate(&mut self)
        requires
            old(self).inv(),
            old(self).round == Round::Idle,
            old(self).settled_or_iteration_limit(),
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_iterations == old(self).max_iterations,
            final(self).max_value == old(self).max_value,
            final(self).edges@ == old(self).edges@,
            final(self).values@ == old(self).values@,
            final(self).snapshot@ == old(self).snapshot@,
            final(self).updated@ == old(self).updated@,
            final(self).iteration == old(self).iteration,
            final(self).changed == old(self).changed,
            final(self).round == old(self).round,
            final(self).inv(),
    {
    }
}

impl PropagationPass {
    /// Construct an idle pass over a valid graph and value assignment.
    pub fn new(
        num_nodes: usize,
        max_iterations: u64,
        max_value: u64,
        edges: Vec<(usize, usize)>,
        init_values: Vec<u64>,
    ) -> (p: PropagationPass)
        requires
            init_values.len() == num_nodes,
            forall|i: int| 0 <= i < init_values.len() ==> init_values@[i] <= max_value,
            forall|i: int| 0 <= i < edges.len()
                ==> edges@[i].0 < num_nodes && edges@[i].1 < num_nodes,
        ensures
            p.num_nodes == num_nodes,
            p.max_iterations == max_iterations,
            p.max_value == max_value,
            p.edges@ == edges@,
            p.values@ == init_values@,
            p.snapshot@ == init_values@,
            p.iteration == 0,
            p.changed,
            p.round == Round::Idle,
            forall|i: int| 0 <= i < p.updated.len() ==> !p.updated@[i],
            p.inv(),
    {
        Self::initialize(num_nodes, max_iterations, max_value, edges, init_values, Vec::new(), Vec::new())
    }

    /// Execute the local combine using only immutable `edges` and `snapshot`.
    pub fn combine_node(&self, n: usize) -> (value: u64)
        requires
            self.type_invariant(),
            n < self.num_nodes,
        ensures
            value as int == local_combine(self.edges@, self.snapshot@, n),
            value <= self.max_value,
    { default_combine(self.max_value, &self.edges, &self.snapshot, n) }

    /// TLA+ `UpdateNode(n)`: compute from the round snapshot and commit one node.
    pub fn update_node(&mut self, n: usize)
        requires
            old(self).inv(),
            old(self).round == Round::Running,
            n < old(self).num_nodes,
            !old(self).updated@[n as int],
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_iterations == old(self).max_iterations,
            final(self).max_value == old(self).max_value,
            final(self).edges@ == old(self).edges@,
            final(self).snapshot@ == old(self).snapshot@,
            final(self).values@ == old(self).values@.update(
                n as int,
                local_combine(old(self).edges@, old(self).snapshot@, n) as u64,
            ),
            final(self).updated@ == old(self).updated@.update(n as int, true),
            final(self).iteration == old(self).iteration,
            final(self).changed == old(self).changed,
            final(self).round == old(self).round,
            final(self).inv(),
    {
        let accepted = self.try_update_node(n);
        assert(accepted);
        let _ = accepted;
    }

}

fn default_combine(_ceiling: u64, edges: &Vec<(usize,usize)>, snapshot: &Vec<u64>, n: usize) -> (value: u64)
    requires ((forall|i: int| 0 <= i < snapshot.len() ==> #[trigger] snapshot@[i] <= _ceiling)
                    && (forall|i: int| 0 <= i < edges.len() ==> #[trigger] edges@[i].0 < snapshot.len() && edges@[i].1 < snapshot.len())), n < snapshot.len(),
    ensures value as int == local_combine(edges@, snapshot@, n), value <= _ceiling,
    {
        let edge_count = edges.len();
        let mut i: usize = 0;
        while i < edge_count
            invariant
                i <= edge_count,
                edge_count == edges.len(),
                ((forall|i: int| 0 <= i < snapshot.len() ==> #[trigger] snapshot@[i] <= _ceiling)
                    && (forall|i: int| 0 <= i < edges.len() ==> #[trigger] edges@[i].0 < snapshot.len() && edges@[i].1 < snapshot.len())),
                n < snapshot.len(),
                forall|j: int| 0 <= j < i ==> !(
                    edges@[j].1 == n
                    && snapshot@[edges@[j].0 as int] < snapshot@[n as int]
                ),
            decreases edge_count - i,
        {
            let edge = edges[i];
            if edge.1 == n && snapshot[edge.0] < snapshot[n] {
                assert(has_better_in_neighbor(edges@, snapshot@, n));
                assert(snapshot@[n as int] > 0);
                return snapshot[n] - 1;
            }
            i = i + 1;
        }
        assert(!has_better_in_neighbor(edges@, snapshot@, n));
        snapshot[n]
    }


fn vectors_equal<T: Copy + ValueEq>(a: &Vec<T>, b: &Vec<T>) -> (same: bool)
    requires a.len() == b.len(),
    ensures same == (a@ == b@),
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases n - i,
    {
        if !a[i].value_eq(&b[i]) {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

}
