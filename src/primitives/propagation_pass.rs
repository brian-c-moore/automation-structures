// Executable PropagationPassGraph contract. The graph is
// immutable, each round snapshots the values, UpdateNode commits one local
// combine from that snapshot, and EndRound alone charges the iteration and
// records whether the round changed anything.
//
// Edges are directed (source, target) pairs. The concrete domain combine is
// the TLA+ miniature: if any in-neighbour has a smaller snapshot value, the
// target decreases by one; otherwise it retains its snapshot value.

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

/// Snapshot-local bounded propagation owner.
pub struct PropagationPass {
    /// Number of graph nodes.
    pub num_nodes: usize,
    /// Maximum completed propagation rounds.
    pub max_iterations: u64,
    /// Inclusive ceiling of node values.
    pub max_value: u64,
    /// Directed propagation edges.
    pub edges: Vec<(usize, usize)>,
    /// Current node values.
    pub values: Vec<u64>,
    /// Immutable values captured at round start.
    pub snapshot: Vec<u64>,
    /// Per-node update markers for the active or latest round.
    pub updated: Vec<bool>,
    /// Number of completed rounds.
    pub iteration: u64,
    /// Whether the latest completed round changed any value.
    pub changed: bool,
    /// Current round lifecycle.
    pub round: Round,
}

impl PropagationPass {
    // -- Specifications --------------------------------------------------

    /// Whether graph, value, snapshot, and marker storage have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.values.len() == self.num_nodes
        &&& self.snapshot.len() == self.num_nodes
        &&& self.updated.len() == self.num_nodes
        &&& (forall|i: int| 0 <= i < self.values.len()
                ==> #[trigger] self.values@[i] <= self.max_value)
        &&& (forall|i: int| 0 <= i < self.snapshot.len()
                ==> #[trigger] self.snapshot@[i] <= self.max_value)
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
            ==> self.values@[i] as int == local_combine(self.edges@, self.snapshot@, i as usize)
    }

    /// Whether an unchanged completed round preserved the full snapshot.
    pub open spec fn settled_ok(&self) -> bool {
        !self.changed ==> self.values@ == self.snapshot@ && self.all_updated()
    }

    /// Whether all propagation-pass obligations hold.
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

    // -- Init ------------------------------------------------------------

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
        let snapshot = clone_values(&init_values);
        let updated = false_vector(num_nodes);
        PropagationPass {
            num_nodes,
            max_iterations,
            max_value,
            edges,
            values: init_values,
            snapshot,
            updated,
            iteration: 0,
            changed: true,
            round: Round::Idle,
        }
    }

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

    /// Execute the local combine using only immutable `edges` and `snapshot`.
    pub fn combine_node(&self, n: usize) -> (value: u64)
        requires
            self.type_invariant(),
            n < self.num_nodes,
        ensures
            value as int == local_combine(self.edges@, self.snapshot@, n),
            value <= self.max_value,
    {
        let edge_count = self.edges.len();
        let mut i: usize = 0;
        while i < edge_count
            invariant
                i <= edge_count,
                edge_count == self.edges.len(),
                self.type_invariant(),
                n < self.num_nodes,
                forall|j: int| 0 <= j < i ==> !(
                    self.edges@[j].1 == n
                    && self.snapshot@[self.edges@[j].0 as int] < self.snapshot@[n as int]
                ),
            decreases edge_count - i,
        {
            let edge = self.edges[i];
            if edge.1 == n && self.snapshot[edge.0] < self.snapshot[n] {
                assert(has_better_in_neighbor(self.edges@, self.snapshot@, n));
                assert(self.snapshot@[n as int] > 0);
                return self.snapshot[n] - 1;
            }
            i = i + 1;
        }
        assert(!has_better_in_neighbor(self.edges@, self.snapshot@, n));
        self.snapshot[n]
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
        self.snapshot = clone_values(&self.values);
        self.updated = false_vector(self.num_nodes);
        self.round = Round::Running;
    }

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
        let next = self.combine_node(n);
        self.values.set(n, next);
        self.updated.set(n, true);
        assert(self.snapshot_locality()) by {
            assert forall|i: int| 0 <= i < self.updated.len() && self.updated@[i]
                implies self.values@[i] as int
                    == local_combine(self.edges@, self.snapshot@, i as usize) by {
                if i == n as int {
                    assert(self.values@[i] == next);
                } else {
                    assert(self.values@[i] == old(self).values@[i]);
                    assert(self.updated@[i] == old(self).updated@[i]);
                }
            }
        }
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

fn false_vector(n: usize) -> (out: Vec<bool>)
    ensures
        out.len() == n,
        forall|i: int| 0 <= i < out.len() ==> !out@[i],
{
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < i ==> !out@[k],
        decreases n - i,
    {
        out.push(false);
        i = i + 1;
    }
    out
}

fn clone_values(v: &Vec<u64>) -> (out: Vec<u64>)
    ensures out@ == v@,
{
    let mut out: Vec<u64> = Vec::new();
    let n = v.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == v.len(),
            out.len() == i,
            forall|k: int| 0 <= k < i ==> out@[k] == v@[k],
        decreases n - i,
    {
        out.push(v[i]);
        i = i + 1;
    }
    assert(out@ =~= v@);
    out
}

fn vectors_equal(a: &Vec<u64>, b: &Vec<u64>) -> (same: bool)
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
        if a[i] != b[i] {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

}
