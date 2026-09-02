// RelationshipGraph assembled from the ResourceRegistry owner.
//
// The formal reduction stores each weighted edge as one ResourceRegistry key. The graph's
// adjacency relation is the source/destination projection of those keys; it is not a second
// mutable graph representation. AddEdge and RemoveEdge therefore mutate registry state only by
// calling ResourceRegistry actions. The public carrier is the selected irreflexive profile and
// rejects self-loops; that policy is not asserted for every possible relationship structure.

use vstd::prelude::*;

use crate::primitives::resource_registry::ResourceRegistry;

verus! {

/// `(source, destination, weight)` registry key.
pub type EdgeKey = (usize, usize, u64);
/// Registry entry used to retain an edge without a second payload.
pub type EdgeBinding = (EdgeKey, ());

/// One weighted relationship is admitted by a RelationshipGraph universe.
pub open spec fn edge_admitted(
    num_nodes: usize,
    max_weight: u64,
    source: usize,
    target: usize,
    weight: u64,
) -> bool {
    source < num_nodes && target < num_nodes && weight <= max_weight
}

/// One adjacency relationship is admitted by a RelationshipGraph universe.
pub open spec fn adjacency_admitted(
    num_nodes: usize,
    source: usize,
    target: usize,
) -> bool {
    source < num_nodes && target < num_nodes
}

/// One adjacency answer agrees with its weighted-edge source projection.
pub open spec fn adjacency_consistent(
    adjacency_present: bool,
    edge_present: bool,
) -> bool {
    crate::connectives::projection::membership_consistent(
        adjacency_present,
        edge_present,
    )
}

/// A present relationship is not reflexive.
pub open spec fn edge_irreflexive(present: bool, source: usize, target: usize) -> bool {
    present ==> source != target
}

/// Whether a registry prefix contains any weighted edge from `source` to `target`.
pub open spec fn has_edge(
    entries: Seq<EdgeBinding>,
    n: int,
    source: usize,
    target: usize,
) -> bool {
    exists|index: int|
        0 <= index < n
            && entries[index].0.0 == source
            && entries[index].0.1 == target
}

/// Exact weighted-edge membership in a registry prefix.
pub open spec fn has_exact_edge(
    entries: Seq<EdgeBinding>,
    n: int,
    source: usize,
    target: usize,
    weight: u64,
) -> bool {
    crate::primitives::resource_registry::has_pair(
        entries,
        n,
        (source, target, weight),
        (),
    )
}

/// Extending the registry prefix exposes the new edge exactly once at the new position.
pub proof fn lemma_has_edge_extend(
    entries: Seq<EdgeBinding>,
    n: int,
    source: usize,
    target: usize,
)
    requires 0 <= n < entries.len(),
    ensures
        has_edge(entries, n + 1, source, target)
            == (has_edge(entries, n, source, target)
                || (entries[n].0.0 == source && entries[n].0.1 == target)),
{
    if has_edge(entries, n + 1, source, target) {
        let index = choose|index: int|
            0 <= index < n + 1
                && entries[index].0.0 == source
                && entries[index].0.1 == target;
        assert(index < n || index == n);
    }
    if has_edge(entries, n, source, target) {
        let index = choose|index: int|
            0 <= index < n
                && entries[index].0.0 == source
                && entries[index].0.1 == target;
        assert(0 <= index < n + 1);
    }
    if entries[n].0.0 == source && entries[n].0.1 == target {
        assert(0 <= n < n + 1);
    }
}

/// Appending one registered edge extends adjacency by exactly its endpoint pair.
pub proof fn lemma_push_has_edge(
    entries: Seq<(EdgeKey, ())>,
    added: EdgeKey,
    source: usize,
    target: usize,
)
    ensures has_edge(entries.push((added, ())), entries.len() as int + 1, source, target)
        == (has_edge(entries, entries.len() as int, source, target)
            || (added.0 == source && added.1 == target)),
{
    let pushed = entries.push((added, ()));
    if has_edge(pushed, pushed.len() as int, source, target) {
        let index = choose|index: int|
            0 <= index < pushed.len()
                && pushed[index].0.0 == source
                && pushed[index].0.1 == target;
        if index < entries.len() {
            assert(pushed[index] == entries[index]);
        } else {
            assert(index == entries.len());
        }
    }
    if has_edge(entries, entries.len() as int, source, target) {
        let index = choose|index: int|
            0 <= index < entries.len()
                && entries[index].0.0 == source
                && entries[index].0.1 == target;
        assert(pushed[index] == entries[index]);
    }
    if added.0 == source && added.1 == target {
        assert(pushed[entries.len() as int].0 == added);
    }
}

/// A weighted directed graph whose only mutable edge owner is ResourceRegistry.
pub struct RelationshipGraph {
    /// Number of nodes in the fixed universe.
    pub num_nodes: usize,
    /// Inclusive edge-weight ceiling.
    pub max_weight: u64,
    /// Owner of exact weighted edges.
    pub registry: ResourceRegistry<EdgeKey, ()>,
}

impl RelationshipGraph {
    /// Whether any registered weighted edge connects `source` to `target`.
    pub open spec fn edge_proj(&self, source: usize, target: usize) -> bool {
        has_edge(
            self.registry.entries@,
            self.registry.entries@.len() as int,
            source,
            target,
        )
    }

    /// Whether the exact weighted edge is registered.
    pub open spec fn exact_edge(&self, source: usize, target: usize, weight: u64) -> bool {
        self.registry.maps_to((source, target, weight), ())
    }

    /// Exact weighted membership projects to endpoint adjacency.
    pub proof fn exact_edge_implies_pair(&self, source: usize, target: usize, weight: u64)
        ensures self.exact_edge(source, target, weight) ==> self.edge_proj(source, target),
    {
        if self.exact_edge(source, target, weight) {
            let index = choose|index: int|
                0 <= index < self.registry.entries@.len()
                    && self.registry.entries@[index].0 == (source, target, weight)
                    && self.registry.entries@[index].1 == ();
            assert(self.registry.entries@[index].0.0 == source);
            assert(self.registry.entries@[index].0.1 == target);
        }
    }

    /// The formal adjacency variable is the edge registry's pair projection.
    pub open spec fn adj_proj(&self, source: usize, target: usize) -> bool {
        self.edge_proj(source, target)
    }

    /// The registry is unique and every registered edge is in the configured universe.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.registry.unique_mapping()
        &&& forall|index: int|
            #![trigger self.registry.entries@[index]]
            0 <= index < self.registry.entries@.len() ==> edge_admitted(
                self.num_nodes,
                self.max_weight,
                self.registry.entries@[index].0.0,
                self.registry.entries@[index].0.1,
                self.registry.entries@[index].0.2,
            )
    }

    /// The adjacency projection and weighted-edge projection are the same derived relation.
    pub open spec fn adjacency_consistency(&self) -> bool {
        forall|source: usize, target: usize|
            source < self.num_nodes && target < self.num_nodes ==> adjacency_consistent(
                #[trigger] self.adj_proj(source, target),
                self.edge_proj(source, target),
            )
    }

    /// No registered edge is a self-loop.
    pub open spec fn no_self_loops(&self) -> bool {
        forall|index: int|
            #![trigger self.registry.entries@[index]]
            0 <= index < self.registry.entries@.len() ==> edge_irreflexive(
                true,
                self.registry.entries@[index].0.0,
                self.registry.entries@[index].0.1,
            )
    }

    /// Whether the edge registry and its derived adjacency relation are valid.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.adjacency_consistency() && self.no_self_loops()
    }

    /// Storage facts needed by larger compositions using the graph owner.
    pub proof fn expose_storage_facts(&self)
        requires self.inv(),
        ensures
            self.registry.unique_mapping(),
            forall|index: int| #![trigger self.registry.entries@[index]]
                0 <= index < self.registry.entries@.len() ==>
                    self.registry.entries@[index].0.0 < self.num_nodes
                        && self.registry.entries@[index].0.1 < self.num_nodes
                        && self.registry.entries@[index].0.2 <= self.max_weight
                        && self.registry.entries@[index].0.0
                            != self.registry.entries@[index].0.1,
    {
        reveal(RelationshipGraph::inv);
        reveal(RelationshipGraph::type_invariant);
        reveal(RelationshipGraph::no_self_loops);
        reveal(edge_admitted);
        reveal(edge_irreflexive);
    }

    /// Construct an empty graph from an empty edge registry.
    pub fn new(num_nodes: usize, max_weight: u64) -> (graph: RelationshipGraph)
        ensures
            graph.num_nodes == num_nodes,
            graph.max_weight == max_weight,
            graph.registry.entries@.len() == 0,
            graph.inv(),
    {
        let registry = ResourceRegistry::new();
        RelationshipGraph { num_nodes, max_weight, registry }
    }

    /// Whether an exact weighted edge can be inserted.
    pub fn can_add_edge(&self, source: usize, target: usize, weight: u64) -> (enabled: bool)
        ensures enabled == (source < self.num_nodes
            && target < self.num_nodes
            && weight <= self.max_weight
            && source != target),
    {
        source < self.num_nodes
            && target < self.num_nodes
            && weight <= self.max_weight
            && source != target
    }

    /// Query exact membership through the ResourceRegistry owner.
    pub fn contains_exact_edge(
        &self,
        source: usize,
        target: usize,
        weight: u64,
    ) -> (present: bool)
        requires self.registry.unique_mapping(),
        ensures present == self.exact_edge(source, target, weight),
    {
        match self.registry.lookup((source, target, weight)) {
            Some(_) => true,
            None => false,
        }
    }

    /// Scan the edge registry to answer the derived adjacency query.
    pub fn contains_pair(&self, source: usize, target: usize) -> (present: bool)
        ensures present == self.edge_proj(source, target),
    {
        let length = self.registry.entries.len();
        let mut index: usize = 0;
        while index < length
            invariant
                index <= length,
                length == self.registry.entries.len(),
                !has_edge(self.registry.entries@, index as int, source, target),
            decreases length - index,
        {
            let key = self.registry.entries[index].0;
            if key.0 == source && key.1 == target {
                return true;
            }
            proof {
                lemma_has_edge_extend(
                    self.registry.entries@,
                    index as int,
                    source,
                    target,
                );
            }
            index = index + 1;
        }
        false
    }

    /// Register one exact weighted edge.
    pub fn add_edge(
        &mut self,
        source: usize,
        target: usize,
        weight: u64,
    ) -> (added: bool)
        requires
            old(self).inv(),
            source < old(self).num_nodes,
            target < old(self).num_nodes,
            weight <= old(self).max_weight,
            source != target,
        ensures
            final(self).inv(),
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_weight == old(self).max_weight,
            added == !old(self).exact_edge(source, target, weight),
            !added ==> final(self).registry.entries@ == old(self).registry.entries@,
            added ==> final(self).registry.entries@
                == old(self).registry.entries@.push(((source, target, weight), ())),
            forall|other_source: usize, other_target: usize|
                #[trigger] final(self).edge_proj(other_source, other_target)
                    == (old(self).edge_proj(other_source, other_target)
                        || (other_source == source && other_target == target)),
    {
        proof { self.expose_storage_facts(); }
        if self.contains_exact_edge(source, target, weight) {
            return false;
        }
        let ghost before = self.registry.entries@;
        self.registry.register((source, target, weight), ());
        assert(self.registry.entries@ == before.push(((source, target, weight), ())));
        assert forall|other_source: usize, other_target: usize|
            #[trigger] self.edge_proj(other_source, other_target)
                == (has_edge(before, before.len() as int, other_source, other_target)
                    || (other_source == source && other_target == target)) by {
            lemma_push_has_edge(
                before,
                (source, target, weight),
                other_source,
                other_target,
            );
        }
        assert(self.type_invariant()) by {
            assert forall|index: int| #![trigger self.registry.entries@[index]]
                0 <= index < self.registry.entries@.len() implies edge_admitted(
                    self.num_nodes,
                    self.max_weight,
                    self.registry.entries@[index].0.0,
                    self.registry.entries@[index].0.1,
                    self.registry.entries@[index].0.2,
                ) by {
                if index < before.len() {
                    assert(self.registry.entries@[index] == before[index]);
                } else {
                    assert(index == before.len());
                    assert(self.registry.entries@[index] == ((source, target, weight), ()));
                }
            }
        }
        assert(self.no_self_loops()) by {
            assert forall|index: int| #![trigger self.registry.entries@[index]]
                0 <= index < self.registry.entries@.len() implies edge_irreflexive(
                    true,
                    self.registry.entries@[index].0.0,
                    self.registry.entries@[index].0.1,
                ) by {
                if index < before.len() {
                    assert(self.registry.entries@[index] == before[index]);
                } else {
                    assert(index == before.len());
                    assert(self.registry.entries@[index] == ((source, target, weight), ()));
                }
            }
        }
        assert(self.adjacency_consistency()) by {
            reveal(RelationshipGraph::adjacency_consistency);
            reveal(RelationshipGraph::adj_proj);
            reveal(adjacency_consistent);
            reveal(crate::connectives::projection::membership_consistent);
        }
        true
    }

    /// Remove every registered weight for one source/destination pair.
    pub fn remove_edge(&mut self, source: usize, target: usize)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).num_nodes == old(self).num_nodes,
            final(self).max_weight == old(self).max_weight,
            forall|s: usize, d: usize, weight: u64|
                #[trigger] final(self).exact_edge(s, d, weight)
                    == (!(s == source && d == target)
                        && old(self).exact_edge(s, d, weight)),
            !final(self).edge_proj(source, target),
    {
        proof { self.expose_storage_facts(); }
        let ghost original = self.registry.entries@;
        let ghost original_num_nodes = self.num_nodes;
        let ghost original_max_weight = self.max_weight;
        let mut index: usize = 0;
        while index < self.registry.entries.len()
            invariant
                index <= self.registry.entries.len(),
                self.num_nodes == original_num_nodes,
                self.max_weight == original_max_weight,
                self.registry.unique_mapping(),
                forall|entry: int| #![trigger self.registry.entries@[entry]]
                    0 <= entry < self.registry.entries@.len() ==>
                        self.registry.entries@[entry].0.0 < self.num_nodes
                            && self.registry.entries@[entry].0.1 < self.num_nodes
                            && self.registry.entries@[entry].0.2 <= self.max_weight
                            && self.registry.entries@[entry].0.0
                                != self.registry.entries@[entry].0.1,
                forall|entry: int| #![trigger self.registry.entries@[entry]]
                    0 <= entry < index ==>
                        !(self.registry.entries@[entry].0.0 == source
                            && self.registry.entries@[entry].0.1 == target),
                forall|s: usize, d: usize, weight: u64|
                    !(s == source && d == target) ==>
                        (#[trigger] has_exact_edge(
                            self.registry.entries@,
                            self.registry.entries@.len() as int,
                            s,
                            d,
                            weight,
                        ) == has_exact_edge(
                            original,
                            original.len() as int,
                            s,
                            d,
                            weight,
                        )),
            decreases self.registry.entries.len() - index,
        {
            let key = self.registry.entries[index].0;
            if key.0 == source && key.1 == target {
                let ghost before = self.registry.entries@;
                let _removed = self.registry.deregister_at(index);
                assert(_removed.0 == key);
                assert forall|entry: int| #![trigger self.registry.entries@[entry]]
                    0 <= entry < self.registry.entries@.len() implies
                        self.registry.entries@[entry].0.0 < self.num_nodes
                            && self.registry.entries@[entry].0.1 < self.num_nodes
                            && self.registry.entries@[entry].0.2 <= self.max_weight
                            && self.registry.entries@[entry].0.0
                                != self.registry.entries@[entry].0.1 by {
                    before.remove_ensures(index as int);
                    let old_entry = if entry < index { entry } else { entry + 1 };
                    assert(0 <= old_entry < before.len());
                    assert(self.registry.entries@[entry] == before[old_entry]);
                }
                assert forall|entry: int| #![trigger self.registry.entries@[entry]]
                    0 <= entry < index implies
                        !(self.registry.entries@[entry].0.0 == source
                            && self.registry.entries@[entry].0.1 == target) by {
                    before.remove_ensures(index as int);
                    assert(self.registry.entries@[entry] == before[entry]);
                }
                assert forall|s: usize, d: usize, weight: u64|
                    !(s == source && d == target) implies
                        (#[trigger] has_exact_edge(
                            self.registry.entries@,
                            self.registry.entries@.len() as int,
                            s,
                            d,
                            weight,
                        ) == has_exact_edge(
                            original,
                            original.len() as int,
                            s,
                            d,
                            weight,
                    )) by {
                    assert((s, d, weight) != key);
                    assert(self.registry.maps_to((s, d, weight), ()) ==
                        (has_exact_edge(
                            before,
                            before.len() as int,
                            s,
                            d,
                            weight,
                        ) && (s, d, weight) != key));
                    assert(has_exact_edge(
                        before,
                        before.len() as int,
                        s,
                        d,
                        weight,
                    ) == has_exact_edge(
                        original,
                        original.len() as int,
                        s,
                        d,
                        weight,
                    ));
                }
            } else {
                index = index + 1;
            }
        }
        assert(!self.edge_proj(source, target)) by {
            if self.edge_proj(source, target) {
                let entry = choose|entry: int|
                    0 <= entry < self.registry.entries@.len()
                        && self.registry.entries@[entry].0.0 == source
                        && self.registry.entries@[entry].0.1 == target;
                assert(false);
            }
        }
        assert(self.type_invariant());
        assert(self.no_self_loops());
        assert(self.adjacency_consistency()) by {
            reveal(RelationshipGraph::adjacency_consistency);
            reveal(RelationshipGraph::adj_proj);
            reveal(adjacency_consistent);
            reveal(crate::connectives::projection::membership_consistent);
        }
        assert forall|s: usize, d: usize, weight: u64|
            #[trigger] self.exact_edge(s, d, weight)
                == (!(s == source && d == target)
                    && old(self).exact_edge(s, d, weight)) by {
            if s == source && d == target {
                if self.exact_edge(s, d, weight) {
                    let entry = choose|entry: int|
                        0 <= entry < self.registry.entries@.len()
                            && self.registry.entries@[entry].0 == (s, d, weight)
                            && self.registry.entries@[entry].1 == ();
                    assert(has_edge(
                        self.registry.entries@,
                        self.registry.entries@.len() as int,
                        source,
                        target,
                    ));
                    assert(self.edge_proj(source, target));
                }
            } else {
                assert(self.exact_edge(s, d, weight) == has_exact_edge(
                    self.registry.entries@,
                    self.registry.entries@.len() as int,
                    s,
                    d,
                    weight,
                ));
                assert(old(self).exact_edge(s, d, weight) == has_exact_edge(
                    original,
                    original.len() as int,
                    s,
                    d,
                    weight,
                ));
            }
        }
    }
}

}
