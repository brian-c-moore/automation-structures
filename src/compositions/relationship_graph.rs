// RelationshipGraph assembled from the ResourceRegistry owner.
//
// The formal reduction stores each weighted edge as one ResourceRegistry key. The graph's
// adjacency relation is the source/destination projection of those keys; it is not a second
// mutable graph representation. AddEdge and RemoveEdge therefore mutate registry state only by
// calling ResourceRegistry actions. The public carrier is the selected irreflexive profile and
// rejects self-loops; that policy is not asserted for every possible relationship structure.

use vstd::prelude::*;

use crate::connectives::ordering_pass::{IndexArrangement, PositionOrder};
use crate::connectives::{buffer::Buffer, counter::Counter, cursor::Cursor};
use crate::primitives::resource_registry::{RegistryPredicate, ResourceRegistry};
use crate::value_eq::ValueEq;

impl<H: Copy + ValueEq, D: EdgeHandleDomain<H>, P: RegistryPredicate<EdgeKey, ()>> core::fmt::Debug
    for MaterializedAdjacency<H, D, P>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MaterializedAdjacency")
            .field("num_nodes", &self.num_nodes())
            .field("edge_count", &self.edge_count())
            .finish_non_exhaustive()
    }
}

verus! {

/// `(source, destination, weight)` registry key.
pub type EdgeKey = (usize, usize, u64);
/// Registry entry used to retain an edge without a second payload.
pub type EdgeBinding = (EdgeKey, ());

/// The endpoint observed by an incident-edge query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeDirection {
    /// Match the edge's source endpoint.
    Outgoing,
    /// Match the edge's destination endpoint.
    Incoming,
}

/// Pure typed-handle data for the immutable authored edge universe.
/// The canonical graph profile owns traversal, ordering, coverage and storage.
pub trait EdgeHandleDomain<H: Copy + ValueEq> {
    /// Maximum authored universe representable by this immutable domain.
    spec fn domain_len(&self) -> nat;
    /// Typed handle representing one original edge position.
    spec fn handle_spec(&self, original: usize) -> H;
    /// Decode a handle's authored position in this domain.
    spec fn ordinal_spec(&self, handle: H) -> Option<usize>;
    /// Observe the admitted domain bound.
    fn len(&self) -> (length: usize) ensures length == self.domain_len();
    /// Whether this handle domain represents no positions.
    fn is_empty(&self) -> (empty: bool) ensures empty == (self.domain_len() == 0)
    { self.len() == 0 }
    /// Construct content for an in-domain position, without automation state.
    fn handle(&self, original: usize) -> (handle: H)
        requires original < self.domain_len(), ensures handle == self.handle_spec(original);
    /// Decode content; the graph separately checks the exact retained representation.
    fn ordinal(&self, handle: &H) -> (original: Option<usize>)
        ensures original == self.ordinal_spec(*handle);
    /// Every constructed handle resolves to the same original position.
    proof fn correspondence(&self, original: usize)
        requires original < self.domain_len(),
        ensures self.ordinal_spec(self.handle_spec(original)) == Some(original);
}

/// Positional edge handles over a caller-declared finite universe.
#[derive(Clone, Copy, Debug)]
pub struct PositionalEdgeHandles {
    /// Maximum number of original positions this domain represents.
    pub count: usize,
}
impl EdgeHandleDomain<usize> for PositionalEdgeHandles {
    open spec fn domain_len(&self) -> nat { self.count as nat }
    open spec fn handle_spec(&self, original: usize) -> usize { original }
    open spec fn ordinal_spec(&self, handle: usize) -> Option<usize> {
        if handle < self.count { Some(handle) } else { None }
    }
    fn len(&self) -> (length: usize) { self.count }
    fn handle(&self, original: usize) -> (handle: usize) { original }
    fn ordinal(&self, handle: &usize) -> (original: Option<usize>) {
        if *handle < self.count { Some(*handle) } else { None }
    }
    proof fn correspondence(&self, original: usize) {}
}

/// Pure policy retaining every authored weighted edge record.
#[derive(Clone, Copy, Debug)]
pub struct AllEdges;
impl RegistryPredicate<EdgeKey, ()> for AllEdges {
    open spec fn selected(&self, _key: EdgeKey, _value: ()) -> bool { true }
    fn test(&self, _key: &EdgeKey, _value: &()) -> (selected: bool) { true }
}

/// The endpoint grouped by an immutable adjacency direction.
pub open spec fn incidence_endpoint(key: EdgeKey, direction: EdgeDirection) -> usize {
    match direction { EdgeDirection::Outgoing => key.0, EdgeDirection::Incoming => key.1 }
}

/// Pure endpoint policy supplied to the canonical ordering certificate.
pub open spec fn incidence_key_le<P: RegistryPredicate<EdgeKey, ()>>(
    left: EdgeKey, right: EdgeKey, predicate: P, direction: EdgeDirection,
) -> bool {
    let left_selected = predicate.selected(left, ());
    let right_selected = predicate.selected(right, ());
    (left_selected && !right_selected) || (left_selected == right_selected
        && incidence_endpoint(left, direction) <= incidence_endpoint(right, direction))
}

/// The canonical arrangement order, including authored-position ties.
pub open spec fn incidence_ordered<P: RegistryPredicate<EdgeKey, ()>>(
    entries: Seq<EdgeBinding>, positions: Seq<usize>, predicate: P, direction: EdgeDirection,
) -> bool {
    forall|earlier: int, later: int| 0 <= earlier < later < positions.len() ==> {
        let left = #[trigger] positions[earlier];
        let right = #[trigger] positions[later];
        incidence_key_le(entries[left as int].0, entries[right as int].0, predicate, direction)
            && (incidence_key_le(entries[right as int].0, entries[left as int].0, predicate, direction)
                ==> left <= right)
    }
}

// Comparator content only. OrderingPass supplies permutation, ordering and
// authored-position ties; selected rows precede all excluded rows.
struct IncidenceOrder<'a, P: RegistryPredicate<EdgeKey, ()>> {
    bindings: &'a Vec<EdgeBinding>, predicate: &'a P, direction: EdgeDirection,
}
impl<'a, P: RegistryPredicate<EdgeKey, ()>> PositionOrder for IncidenceOrder<'a, P> {
    closed spec fn domain_len(&self) -> nat { self.bindings@.len() }
    closed spec fn key_le(&self, left: usize, right: usize) -> bool {
        incidence_key_le(self.bindings@[left as int].0, self.bindings@[right as int].0,
            *self.predicate, self.direction)
    }
    proof fn establish(&self) {
        assert forall|a: usize| a < self.domain_len() implies #[trigger] self.key_le(a, a) by {}
        assert forall|a: usize, b: usize| a < self.domain_len() && b < self.domain_len()
            implies #[trigger] self.key_le(a, b) || self.key_le(b, a) by {}
        assert forall|a: usize, b: usize, c: usize|
            a < self.domain_len() && b < self.domain_len() && c < self.domain_len()
            && #[trigger] self.key_le(a, b) && #[trigger] self.key_le(b, c)
            implies self.key_le(a, c) by {}
    }
    fn len(&self) -> (length: usize) { self.bindings.len() }
    #[expect(clippy::indexing_slicing, reason = "PositionOrder requires both input positions below the immutable bindings length")]
    fn compare(&self, left: usize, right: usize) -> (ordering: i8) {
        let left_key = &self.bindings[left].0;
        let right_key = &self.bindings[right].0;
        let left_selected = self.predicate.test(left_key, &());
        let right_selected = self.predicate.test(right_key, &());
        if left_selected && !right_selected { return -1; }
        if !left_selected && right_selected { return 1; }
        let left_endpoint = match self.direction { EdgeDirection::Outgoing => left_key.0, EdgeDirection::Incoming => left_key.1 };
        let right_endpoint = match self.direction { EdgeDirection::Outgoing => right_key.0, EdgeDirection::Incoming => right_key.1 };
        if left_endpoint < right_endpoint { -1 }
        else if left_endpoint > right_endpoint { 1 } else { 0 }
    }
}

/// An arranged position belongs strictly before this node's adjacency span.
pub open spec fn incidence_before<P: RegistryPredicate<EdgeKey, ()>>(
    entries: Seq<EdgeBinding>, positions: Seq<usize>, predicate: P,
    direction: EdgeDirection, node: int, rank: int,
) -> bool {
    let key = entries[positions[rank] as int].0;
    predicate.selected(key, ()) && incidence_endpoint(key, direction) < node
}

/// One offset separates exactly the selected endpoints below a node.
pub open spec fn incidence_boundary<P: RegistryPredicate<EdgeKey, ()>>(
    entries: Seq<EdgeBinding>, positions: Seq<usize>, predicate: P,
    direction: EdgeDirection, node: int, boundary: usize,
) -> bool {
    boundary <= positions.len() && forall|rank: int| 0 <= rank < positions.len() ==>
        (rank < boundary <==> #[trigger] incidence_before(entries, positions, predicate, direction, node, rank))
}

/// A failure to construct the immutable adjacency profile publishes no replacement graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum AdjacencyBuildError {
    /// The typed-handle domain cannot represent every authored edge.
    HandleDomain,
    /// The node-offset array length cannot be represented.
    NodeOffsetOverflow,
    /// A fallible arrangement or Buffer reservation was refused.
    StorageUnavailable,
}

/// Checked materialization outcome; refusal returns every original input.
pub type MaterializationResult<H, D, P> = Result<MaterializedAdjacency<H, D, P>,
    (AdjacencyBuildError, crate::composition_api::RelationshipGraph, D, P)>;

type CarrierMaterializationResult<H, D, P> = Result<MaterializedAdjacency<H, D, P>,
    (AdjacencyBuildError, RelationshipGraph, D, P)>;

// One certificate, not another mutable edge authority. All records retain a
// position and inverse; selected records form the prefix covered by node spans.
struct IncidenceView<H: Copy> {
    arrangement: IndexArrangement,
    handles: Buffer<H>,
    offsets: Buffer<usize>,
}

impl<H: Copy> IncidenceView<H> {
    closed spec fn consistent<P: RegistryPredicate<EdgeKey, ()>>(
        &self, entries: Seq<EdgeBinding>, original_handles: Seq<H>, nodes: usize,
        predicate: P, direction: EdgeDirection,
    ) -> bool {
        &&& self.arrangement.inv()
        &&& self.arrangement.positions_spec().len() == entries.len()
        &&& incidence_ordered(entries, self.arrangement.positions_spec(), predicate, direction)
        &&& original_handles.len() == entries.len()
        &&& self.handles.well_formed() && self.handles.values@.len() == entries.len()
        &&& forall|rank: int| 0 <= rank < entries.len() ==>
            #[trigger] self.handles.values@[rank]
                == original_handles[self.arrangement.positions_spec()[rank] as int]
        &&& self.offsets.well_formed() && self.offsets.values@.len() == nodes as int + 1
        &&& self.offsets.values@[0] == 0
        &&& forall|node: int| 0 <= node <= nodes ==>
            incidence_boundary(entries, self.arrangement.positions_spec(), predicate,
                direction, node, #[trigger] self.offsets.values@[node])
    }

    #[expect(clippy::indexing_slicing, reason = "the joint arrangement permutation and Cursor bounds prove every handle and edge access")]
    #[expect(clippy::arithmetic_side_effects, reason = "nodes < usize::MAX admits the terminal offset and each Cursor advances only while below its fixed length")]
    #[expect(clippy::cast_possible_truncation, reason = "the node Counter is bounded by graph.num_nodes: usize throughout materialization")]
    fn try_new<P: RegistryPredicate<EdgeKey, ()>>(
        graph: &RelationshipGraph, original_handles: &Buffer<H>, predicate: &P,
        direction: EdgeDirection,
    ) -> (result: Result<Self, AdjacencyBuildError>)
        requires graph.inv(), graph.num_nodes < usize::MAX,
            original_handles.well_formed(), original_handles.values@.len() == graph.registry.entries@.len(),
        ensures result is Ok ==> result->Ok_0.consistent(graph.registry.entries@,
            original_handles.values@, graph.num_nodes, *predicate, direction),
    {
        proof { graph.expose_storage_facts(); }
        let count = graph.registry.entries.len();
        let order = IncidenceOrder { bindings: &graph.registry.entries, predicate, direction };
        let arrangement = match IndexArrangement::try_new(count, &order) {
            Ok(arrangement) => arrangement,
            Err(_) => { return Err(AdjacencyBuildError::StorageUnavailable); },
        };
        proof { arrangement.expose_certificate(); }
        let mut handles = match Buffer::try_new(count) {
            Ok(handles) => handles,
            Err(_) => { return Err(AdjacencyBuildError::StorageUnavailable); },
        };
        let mut offsets = match Buffer::try_new(graph.num_nodes + 1) {
            Ok(offsets) => offsets,
            Err(_) => { return Err(AdjacencyBuildError::StorageUnavailable); },
        };
        let mut cursor = Cursor::new(0);
        while cursor.position < count
            invariant cursor.position <= count, arrangement.inv(),
                arrangement.positions_spec().len() == count,
                crate::connectives::ordering_pass::permutation(arrangement.positions_spec(), count as nat),
                crate::connectives::ordering_pass::arranged(arrangement.positions_spec(), &order),
                count == graph.registry.entries@.len(), original_handles.values@.len() == count,
                handles.well_formed(), handles.capacity == count, handles.values@.len() == cursor.position,
                forall|rank: int| 0 <= rank < cursor.position ==>
                    #[trigger] handles.values@[rank]
                        == original_handles.values@[arrangement.positions_spec()[rank] as int],
            decreases count - cursor.position,
        {
            let rank = cursor.position;
            let original = arrangement.positions()[rank];
            let _ = handles.push(original_handles.values[original]);
            cursor.advance_to(rank + 1);
        }
        let _ = offsets.push(0);
        let mut node = Counter::new(0);
        let mut edge = Cursor::new(0);
        while node.value < graph.num_nodes as u64
            invariant node.value <= graph.num_nodes, graph.num_nodes < usize::MAX,
                graph.inv(), count == graph.registry.entries@.len(),
                forall|i: int| 0 <= i < count ==> #[trigger] graph.registry.entries@[i].0.0 < graph.num_nodes
                    && graph.registry.entries@[i].0.1 < graph.num_nodes,
                arrangement.inv(), arrangement.positions_spec().len() == count,
                order.bindings@ == graph.registry.entries@,
                *order.predicate == *predicate, order.direction == direction,
                crate::connectives::ordering_pass::permutation(arrangement.positions_spec(), count as nat),
                crate::connectives::ordering_pass::arranged(arrangement.positions_spec(), &order),
                edge.position <= count,
                incidence_boundary(graph.registry.entries@, arrangement.positions_spec(), *predicate,
                    direction, node.value as int, edge.position),
                offsets.well_formed(), offsets.capacity == graph.num_nodes as int + 1,
                offsets.values@.len() == node.value as int + 1, offsets.values@[0] == 0,
                forall|n: int| 0 <= n <= node.value ==> incidence_boundary(graph.registry.entries@,
                    arrangement.positions_spec(), *predicate, direction, n, #[trigger] offsets.values@[n]),
            decreases graph.num_nodes - node.value,
        {
            let current = node.value as usize;
            proof {
                assert forall|rank: int| 0 <= rank < edge.position implies
                    #[trigger] incidence_before(graph.registry.entries@, arrangement.positions_spec(),
                        *predicate, direction, current as int + 1, rank) by {
                    assert(incidence_before(graph.registry.entries@, arrangement.positions_spec(),
                        *predicate, direction, current as int, rank));
                }
            }
            while edge.position < count && Self::matches_node(graph, &arrangement, predicate, direction, current, edge.position)
                invariant edge.position <= count, current == node.value,
                    arrangement.inv(), arrangement.positions_spec().len() == count,
                    order.bindings@ == graph.registry.entries@,
                    *order.predicate == *predicate, order.direction == direction,
                    crate::connectives::ordering_pass::permutation(arrangement.positions_spec(), count as nat),
                    crate::connectives::ordering_pass::arranged(arrangement.positions_spec(), &order),
                    count == graph.registry.entries@.len(),
                    forall|rank: int| 0 <= rank < edge.position ==> #[trigger] incidence_before(graph.registry.entries@,
                        arrangement.positions_spec(), *predicate, direction, current as int + 1, rank),
                    forall|rank: int| edge.position <= rank < count ==>
                        !#[trigger] incidence_before(graph.registry.entries@, arrangement.positions_spec(),
                            *predicate, direction, current as int, rank),
                decreases count - edge.position,
            {
                let rank = edge.position;
                edge.advance_to(rank + 1);
            }
            proof {
                assert forall|rank: int| edge.position <= rank < count implies
                    !#[trigger] incidence_before(graph.registry.entries@, arrangement.positions_spec(),
                        *predicate, direction, current as int + 1, rank) by {
                    if edge.position < count {
                        let first = arrangement.positions_spec()[edge.position as int];
                        let later = arrangement.positions_spec()[rank];
                        let first_key = graph.registry.entries@[first as int].0;
                        let later_key = graph.registry.entries@[later as int].0;
                        reveal(<IncidenceOrder<'_, _> as PositionOrder>::key_le);
                        assert(!incidence_before(graph.registry.entries@, arrangement.positions_spec(),
                            *predicate, direction, current as int, edge.position as int));
                        assert(!incident_selected(first_key, current, direction, *predicate));
                        if rank > edge.position {
                            assert(crate::connectives::ordering_pass::position_le(&order, first, later));
                            assert(order.key_le(first, later));
                        }
                        if predicate.selected(later_key, ()) {
                            assert(predicate.selected(first_key, ()));
                            assert(incidence_endpoint(first_key, direction) > current);
                            assert(incidence_endpoint(first_key, direction)
                                <= incidence_endpoint(later_key, direction));
                        }
                    }
                }
            }
            let _ = offsets.push(edge.position);
            let _ = node.try_increment();
        }
        proof {
            reveal(<IncidenceOrder<'_, _> as PositionOrder>::key_le);
            assert(incidence_ordered(graph.registry.entries@, arrangement.positions_spec(),
                *predicate, direction));
        }
        Ok(Self { arrangement, handles, offsets })
    }

    // Pure content comparison. Canonical Cursor remains the traversal owner.
    #[expect(clippy::indexing_slicing, reason = "the required in-range rank and exposed permutation certificate bound both dependent accesses")]
    fn matches_node<P: RegistryPredicate<EdgeKey, ()>>(graph: &RelationshipGraph,
        arrangement: &IndexArrangement, predicate: &P, direction: EdgeDirection,
        node: usize, rank: usize) -> (matches: bool)
        requires arrangement.inv(), arrangement.positions_spec().len() == graph.registry.entries@.len(),
            rank < arrangement.positions_spec().len(),
        ensures matches == incident_selected(graph.registry.entries@[arrangement.positions_spec()[rank as int] as int].0,
            node, direction, *predicate),
    {
        proof { arrangement.expose_certificate(); }
        let original = arrangement.positions()[rank];
        let key = &graph.registry.entries[original].0;
        predicate.test(key, &()) && (match direction {
            EdgeDirection::Outgoing => key.0, EdgeDirection::Incoming => key.1,
        }) == node
    }
}

/// Owning immutable adjacency with typed borrowed spans and exact edge resolution.
///
/// Registry remains the single edge owner. IndexArrangement certifies both
/// directions; Buffer retains their handles and boundaries. Canonical Cursor
/// and Counter advance materialization. Different weights remain separate edges.
/// Construction costs O(E log E + V + E); span and handle queries cost O(1).
/// Domain comparisons and handle conversion must be bounded pure content.
pub struct MaterializedAdjacency<H: Copy + ValueEq, D: EdgeHandleDomain<H>, P: RegistryPredicate<EdgeKey, ()>> {
    graph: RelationshipGraph,
    domain: D,
    predicate: P,
    original_handles: Buffer<H>,
    outgoing: IncidenceView<H>,
    incoming: IncidenceView<H>,
}

impl<H: Copy + ValueEq, D: EdgeHandleDomain<H>, P: RegistryPredicate<EdgeKey, ()>> MaterializedAdjacency<H, D, P> {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inv() }

    /// Exact original owner and jointly certified immutable views.
    pub closed spec fn inv(&self) -> bool {
        &&& self.graph.inv() && self.graph.num_nodes < usize::MAX
        &&& self.graph.registry.entries@.len() <= self.domain.domain_len()
        &&& self.original_handles.well_formed()
        &&& self.original_handles.values@.len() == self.graph.registry.entries@.len()
        &&& forall|i: int| 0 <= i < self.original_handles.values@.len() ==>
            #[trigger] self.original_handles.values@[i] == self.domain.handle_spec(i as usize)
                && self.domain.ordinal_spec(self.original_handles.values@[i]) == Some(i as usize)
        &&& self.outgoing.consistent(self.graph.registry.entries@, self.original_handles.values@,
            self.graph.num_nodes, self.predicate, EdgeDirection::Outgoing)
        &&& self.incoming.consistent(self.graph.registry.entries@, self.original_handles.values@,
            self.graph.num_nodes, self.predicate, EdgeDirection::Incoming)
    }

    /// Immutable content projection retained by this graph profile.
    pub closed spec fn handle_domain_spec(&self) -> D { self.domain }
    /// Immutable selection policy retained by this graph profile.
    pub closed spec fn predicate_spec(&self) -> P { self.predicate }

    /// Authored weighted records retained by the graph owner, including excluded records.
    pub closed spec fn edges_spec(&self) -> Seq<EdgeBinding> { self.graph.registry.entries@ }
    /// Handles in original edge order.
    pub closed spec fn original_handles_spec(&self) -> Seq<H> { self.original_handles.values@ }
    /// The retained immutable node universe.
    pub closed spec fn node_universe(&self) -> usize { self.graph.num_nodes }
    /// Original edge positions at each arranged rank.
    pub closed spec fn positions_spec(&self, direction: EdgeDirection) -> Seq<usize> {
        match direction { EdgeDirection::Outgoing => self.outgoing.arrangement.positions_spec(),
            EdgeDirection::Incoming => self.incoming.arrangement.positions_spec() }
    }
    /// Inverse ranks for every original record, including excluded records.
    pub closed spec fn inverse_spec(&self, direction: EdgeDirection) -> Seq<usize> {
        match direction { EdgeDirection::Outgoing => self.outgoing.arrangement.inverse_spec(),
            EdgeDirection::Incoming => self.incoming.arrangement.inverse_spec() }
    }
    /// Boundaries of selected edges, one per node plus the terminal boundary.
    pub closed spec fn offsets_spec(&self, direction: EdgeDirection) -> Seq<usize> {
        match direction { EdgeDirection::Outgoing => self.outgoing.offsets.values@,
            EdgeDirection::Incoming => self.incoming.offsets.values@ }
    }
    /// Handles in the complete arranged order; node spans cover its selected prefix.
    pub closed spec fn handles_spec(&self, direction: EdgeDirection) -> Seq<H> {
        match direction { EdgeDirection::Outgoing => self.outgoing.handles.values@,
            EdgeDirection::Incoming => self.incoming.handles.values@ }
    }
    /// Exact representation resolution, rejecting unknown or foreign handles.
    pub closed spec fn resolve_spec(&self, handle: H) -> Option<usize> {
        match self.domain.ordinal_spec(handle) {
            Some(original) => if original < self.original_handles.values@.len()
                && self.original_handles.values@[original as int] == handle { Some(original) } else { None },
            None => None,
        }
    }

    /// Export exact handle identity, including a foreign representation with a valid ordinal.
    pub proof fn expose_handle_resolution(&self, handle: H)
        requires self.inv(),
        ensures self.resolve_spec(handle) == match self.handle_domain_spec().ordinal_spec(handle) {
            Some(original) => if original < self.original_handles_spec().len()
                && self.original_handles_spec()[original as int] == handle { Some(original) } else { None },
            None => None,
        },
    {}

    /// Export the retained owners' joint certificate without exposing mutable storage.
    pub proof fn expose_adjacency(&self, direction: EdgeDirection)
        requires self.inv(),
        ensures
            crate::connectives::ordering_pass::inverse_permutation(
                self.positions_spec(direction), self.inverse_spec(direction)),
            self.positions_spec(direction).len() == self.edges_spec().len(),
            self.original_handles_spec().len() == self.edges_spec().len(),
            self.handles_spec(direction).len() == self.edges_spec().len(),
            self.offsets_spec(direction).len() == self.node_universe() as int + 1,
            self.offsets_spec(direction)[0] == 0,
            incidence_ordered(self.edges_spec(), self.positions_spec(direction),
                self.predicate_spec(), direction),
            forall|rank: int| 0 <= rank < self.edges_spec().len() ==>
                #[trigger] self.handles_spec(direction)[rank]
                    == self.original_handles_spec()[self.positions_spec(direction)[rank] as int],
            forall|node: int| 0 <= node <= self.node_universe() ==>
                incidence_boundary(self.edges_spec(), self.positions_spec(direction),
                    self.predicate_spec(), direction, node, #[trigger] self.offsets_spec(direction)[node]),
            forall|original: int| 0 <= original < self.original_handles_spec().len() ==>
                #[trigger] self.original_handles_spec()[original]
                    == self.handle_domain_spec().handle_spec(original as usize)
                && self.handle_domain_spec().ordinal_spec(self.original_handles_spec()[original])
                    == Some(original as usize),
    {
        match direction {
            EdgeDirection::Outgoing => self.outgoing.arrangement.expose_certificate(),
            EdgeDirection::Incoming => self.incoming.arrangement.expose_certificate(),
        }
    }

    #[expect(clippy::arithmetic_side_effects, reason = "the original-handle Cursor advances only while its position is strictly below the edge count")]
    pub(crate) fn try_new(graph: RelationshipGraph, domain: D, predicate: P)
        -> (result: CarrierMaterializationResult<H, D, P>)
        requires graph.inv(),
        ensures result is Ok ==> result->Ok_0.inv() && result->Ok_0.edges_spec() == graph.registry.entries@
            && result->Ok_0.node_universe() == graph.num_nodes
            && result->Ok_0.handle_domain_spec() == domain && result->Ok_0.predicate_spec() == predicate,
            result matches Err((_, returned, returned_domain, returned_predicate)) ==>
                returned == graph && returned_domain == domain && returned_predicate == predicate,
    {
        let count = graph.registry.entries.len();
        if count > domain.len() { return Err((AdjacencyBuildError::HandleDomain, graph, domain, predicate)); }
        if graph.num_nodes == usize::MAX { return Err((AdjacencyBuildError::NodeOffsetOverflow, graph, domain, predicate)); }
        let mut original_handles = match Buffer::try_new(count) {
            Ok(handles) => handles,
            Err(_) => { return Err((AdjacencyBuildError::StorageUnavailable, graph, domain, predicate)); },
        };
        let mut cursor = Cursor::new(0);
        while cursor.position < count
            invariant cursor.position <= count, count <= domain.domain_len(),
                original_handles.well_formed(), original_handles.capacity == count,
                original_handles.values@.len() == cursor.position,
                forall|i: int| 0 <= i < cursor.position ==>
                    #[trigger] original_handles.values@[i] == domain.handle_spec(i as usize)
                        && domain.ordinal_spec(original_handles.values@[i]) == Some(i as usize),
            decreases count - cursor.position,
        {
            let original = cursor.position;
            let handle = domain.handle(original);
            proof { domain.correspondence(original); }
            let _ = original_handles.push(handle);
            cursor.advance_to(original + 1);
        }
        let outgoing = match IncidenceView::try_new(&graph, &original_handles, &predicate, EdgeDirection::Outgoing) {
            Ok(view) => view,
            Err(reason) => { return Err((reason, graph, domain, predicate)); },
        };
        let incoming = match IncidenceView::try_new(&graph, &original_handles, &predicate, EdgeDirection::Incoming) {
            Ok(view) => view,
            Err(reason) => { return Err((reason, graph, domain, predicate)); },
        };
        Ok(Self { graph, domain, predicate, original_handles, outgoing, incoming })
    }

    /// Number of nodes in the fixed graph universe.
    pub fn num_nodes(&self) -> (count: usize) ensures count == self.node_universe(),
    { self.graph.num_nodes }
    /// Number of authored weighted records, including records excluded from spans.
    pub fn edge_count(&self) -> (count: usize) ensures count == self.edges_spec().len(),
    { self.graph.registry.entries.len() }
    /// Typed handle for an original edge position; foreign positions return None.
    #[expect(clippy::indexing_slicing, reason = "the branch checks the original position against retained handle length")]
    pub fn handle_at(&self, original: usize) -> (handle: Option<H>)
        ensures handle == if original < self.original_handles_spec().len()
            { Some(self.original_handles_spec()[original as int]) } else { None },
    { if original < self.original_handles.values.len() { Some(self.original_handles.values[original]) } else { None } }

    /// Resolve a retained typed handle to its exact authored weighted record.
    #[expect(clippy::indexing_slicing, reason = "the runtime handle-length guard and private invariant bind the same original position to a retained graph record")]
    pub fn edge(&self, handle: &H) -> (edge: Option<EdgeKey>)
        ensures edge == match self.resolve_spec(*handle) {
            Some(original) => Some(self.edges_spec()[original as int].0), None => None,
        },
    {
        proof { use_type_invariant(self); reveal(MaterializedAdjacency::inv); }
        let original = match self.domain.ordinal(handle) { Some(original) => original, None => { return None; } };
        if original < self.original_handles.values.len()
            && self.original_handles.values[original].value_eq(handle) {
            return Some(self.graph.registry.entries[original].0);
        }
        None
    }

    /// Borrow one node's selected outgoing or incoming handles in authored tie order.
    /// Out-of-universe nodes return None; admitted nodes with no edges return an empty slice.
    #[expect(clippy::indexing_slicing, reason = "the node guard and private invariant provide exactly num_nodes + 1 certified offsets")]
    #[expect(clippy::arithmetic_side_effects, reason = "node < num_nodes < usize::MAX proves the terminal offset index node + 1 is representable")]
    pub fn incident(&self, node: usize, direction: EdgeDirection) -> (handles: Option<&[H]>)
        ensures handles == None <==> node >= self.node_universe(),
            handles is Some ==> handles->Some_0@ == self.handles_spec(direction).subrange(
                self.offsets_spec(direction)[node as int] as int,
                self.offsets_spec(direction)[node as int + 1] as int),
    {
        proof { use_type_invariant(self); }
        if node >= self.graph.num_nodes { return None; }
        let view = match direction { EdgeDirection::Outgoing => &self.outgoing, EdgeDirection::Incoming => &self.incoming };
        let start = view.offsets.values[node];
        let end = view.offsets.values[node + 1];
        proof {
            if start > end {
                assert(incidence_before(self.graph.registry.entries@, view.arrangement.positions_spec(),
                    self.predicate, direction, node as int, end as int));
                assert(incidence_before(self.graph.registry.entries@, view.arrangement.positions_spec(),
                    self.predicate, direction, node as int + 1, end as int));
                assert(false);
            }
        }
        Some(vstd::slice::slice_subrange(view.handles.values.as_slice(), start, end))
    }

    /// Inverse rank of a selected handle in a direction's retained prefix.
    /// Excluded and foreign handles return None; every excluded original position
    /// remains represented by the complete private arrangement certificate.
    #[expect(clippy::indexing_slicing, reason = "the exact-handle guard, inverse certificate and private terminal-offset invariant bound all three accesses")]
    pub fn rank_of(&self, handle: &H, direction: EdgeDirection) -> (rank: Option<usize>)
        ensures rank == match self.resolve_spec(*handle) {
            Some(original) => {
                let actual = self.inverse_spec(direction)[original as int];
                let selected_end = self.offsets_spec(direction)[self.node_universe() as int];
                if actual < selected_end { Some(actual) } else { None }
            },
            None => None,
        },
    {
        proof { use_type_invariant(self); reveal(MaterializedAdjacency::inv); }
        let original = match self.domain.ordinal(handle) { Some(original) => original, None => { return None; } };
        if original >= self.original_handles.values.len()
            || !self.original_handles.values[original].value_eq(handle) { return None; }
        let view = match direction { EdgeDirection::Outgoing => &self.outgoing, EdgeDirection::Incoming => &self.incoming };
        proof { view.arrangement.expose_certificate(); }
        let rank = view.arrangement.inverse()[original];
        if rank < view.offsets.values[self.graph.num_nodes] { Some(rank) } else { None }
    }
}

/// Pure incident selection over the graph's existing weighted edge records.
pub open spec fn incident_selected<P: RegistryPredicate<EdgeKey, ()>>(
    key: EdgeKey, node: usize, direction: EdgeDirection, predicate: P,
) -> bool {
    (if direction == EdgeDirection::Outgoing { key.0 } else { key.1 }) == node
        && predicate.selected(key, ())
}

/// Exact weighted incident-edge count, including distinct weights on one endpoint pair.
pub open spec fn incident_count<P: RegistryPredicate<EdgeKey, ()>>(
    entries: Seq<EdgeBinding>, end: int, node: usize, direction: EdgeDirection, predicate: P,
) -> int
    decreases end,
{
    if end <= 0 || end > entries.len() { 0 }
    else { incident_count(entries, end - 1, node, direction, predicate)
        + if incident_selected(entries[end - 1].0, node, direction, predicate) { 1int } else { 0int } }
}

struct IncidentPredicate<'a, P: RegistryPredicate<EdgeKey, ()>> {
    node: usize,
    direction: EdgeDirection,
    predicate: &'a P,
}
impl<'a, P: RegistryPredicate<EdgeKey, ()>> RegistryPredicate<EdgeKey, ()> for IncidentPredicate<'a, P> {
    closed spec fn selected(&self, key: EdgeKey, _value: ()) -> bool {
        incident_selected(key, self.node, self.direction, *self.predicate)
    }
    fn test(&self, key: &EdgeKey, value: &()) -> (selected: bool) {
        (match self.direction { EdgeDirection::Outgoing => key.0, EdgeDirection::Incoming => key.1 }) == self.node
            && self.predicate.test(key, value)
    }
}
impl<'a, P: RegistryPredicate<EdgeKey, ()>> IncidentPredicate<'a, P> {
    proof fn count_matches(&self, entries: Seq<EdgeBinding>, end: int)
        requires 0 <= end <= entries.len(),
        ensures crate::primitives::resource_registry::selected_count(entries, end, *self)
            == incident_count(entries, end, self.node, self.direction, *self.predicate),
        decreases end,
    {
        if end > 0 { self.count_matches(entries, end - 1); }
    }
}

struct PairPredicate { source: usize, target: usize }
impl RegistryPredicate<EdgeKey, ()> for PairPredicate {
    closed spec fn selected(&self, key: EdgeKey, _value: ()) -> bool {
        key.0 == self.source && key.1 == self.target
    }
    fn test(&self, key: &EdgeKey, _value: &()) -> (selected: bool) {
        key.0 == self.source && key.1 == self.target
    }
}
impl PairPredicate {
    proof fn count_matches_pair(&self, entries: Seq<EdgeBinding>, end: int)
        requires 0 <= end <= entries.len(),
        ensures crate::primitives::resource_registry::selected_count(entries, end, *self) >= 0,
            (crate::primitives::resource_registry::selected_count(entries, end, *self) > 0)
                == has_edge(entries, end, self.source, self.target),
        decreases end,
    {
        if end > 0 {
            self.count_matches_pair(entries, end - 1);
            lemma_has_edge_extend(entries, end - 1, self.source, self.target);
        }
    }
}

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

    /// Query endpoint adjacency through the existing Registry-owned predicate fold.
    pub fn contains_pair(&self, source: usize, target: usize) -> (present: bool)
        ensures present == self.edge_proj(source, target),
    {
        let predicate = PairPredicate { source, target };
        let present = self.registry.any_matching(&predicate);
        proof { predicate.count_matches_pair(self.registry.entries@, self.registry.entries@.len() as int); }
        present
    }

    /// Count filtered incoming or outgoing weighted edges through their Registry owner.
    pub fn filtered_degree<P: RegistryPredicate<EdgeKey, ()>>(
        &self, node: usize, direction: EdgeDirection, predicate: &P,
    ) -> (count: usize)
        requires node < self.num_nodes,
        ensures count as int == incident_count(self.registry.entries@,
            self.registry.entries@.len() as int, node, direction, *predicate),
    {
        let selected = IncidentPredicate { node, direction, predicate };
        let count = self.registry.count_matching(&selected);
        proof { selected.count_matches(self.registry.entries@, self.registry.entries@.len() as int); }
        count
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
    #[expect(clippy::indexing_slicing, reason = "the removal loop guards each key read by the current retained Registry length")]
    #[expect(clippy::arithmetic_side_effects, reason = "the removal cursor advances only on a nonremoval step while strictly below current Registry length")]
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
                assert(_removed->Some_0.0 == key);
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
