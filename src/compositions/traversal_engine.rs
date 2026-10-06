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
use crate::connectives::cursor::Cursor;
use crate::connectives::marker::Marker;
use crate::connectives::ordering_pass::{IndexArrangement, PositionOrder};
use crate::primitives::budget::Budget;
use crate::primitives::quality_hierarchy::QualityHierarchy;
#[expect(
    unused_imports,
    reason = "KeyIdentity supplies the erased candidate Registry proof contract"
)]
use crate::primitives::resource_registry::KeyIdentity;

impl std::fmt::Display for CandidateTraversalError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        output.write_str(match self {
            Self::CandidateCapacity => "candidate storage ceiling reached",
            Self::Closed => "candidate admission is closed",
            Self::ForeignScope => "candidate belongs to another scope",
            Self::UnknownCandidate => "candidate is not retained",
            Self::ParentPending => "extension parent has not been visited",
            Self::InvalidExtension => "extension violates hierarchy level or cost order",
            Self::StorageUnavailable => "candidate owner storage reservation failed",
            Self::WorkBudgetOverflow => "candidate work universe or accounting overflows",
        })
    }
}
impl std::error::Error for CandidateTraversalError {}
use crate::primitives::resource_registry::ResourceRegistry;

verus! {

// Immutable level comparison is domain content; OrderingPass owns its arrangement.
struct HierarchyLevelOrder<'a> { hierarchy: &'a QualityHierarchy }
impl<'a> PositionOrder for HierarchyLevelOrder<'a> {
    closed spec fn domain_len(&self) -> nat { self.hierarchy.level@.len() }
    closed spec fn key_le(&self, left: usize, right: usize) -> bool {
        self.hierarchy.level@[left as int] >= self.hierarchy.level@[right as int]
    }
    proof fn establish(&self) {}
    fn len(&self) -> (n: usize) { self.hierarchy.level.len() }
    #[expect(clippy::indexing_slicing, reason = "PositionOrder requires both original positions within the immutable level universe")]
    fn compare(&self, left: usize, right: usize) -> (ordering: i8) {
        let left = self.hierarchy.level[left];
        let right = self.hierarchy.level[right];
        if left > right { -1 } else if left == right { 0 } else { 1 }
    }
}

/// Finite forest discovery through the retained TraversalEngine work owner.
/// The immutable hierarchy has its actual parent/edge and level/cost owners.
/// OrderingPass owns parent-before-child order; accepted-work length supplies progress. The synthetic
/// work root and checked nonbinding work Budget do not impose a domain quota.
pub struct RootedTraversal {
    hierarchy: QualityHierarchy,
    arrangement: IndexArrangement,
    work: TraversalEngine,
}

impl RootedTraversal {
    /// Unchanged hierarchy context retained by this profile.
    pub closed spec fn hierarchy_spec(&self) -> QualityHierarchy { self.hierarchy }
    /// Immutable parent-before-child arrangement.
    pub closed spec fn order_spec(&self) -> Seq<usize> { self.arrangement.positions_spec() }
    /// Inverse original-node rank under that same arrangement owner.
    pub closed spec fn ranks_spec(&self) -> Seq<usize> { self.arrangement.inverse_spec() }
    /// Considered prefix projected from the actual accepted-work owner after its synthetic root.
    pub closed spec fn considered_spec(&self) -> nat {
        (self.work.accepted.accumulated@.len() - 1) as nat
    }
    /// Actual work frontier, including the synthetic root only during construction.
    pub closed spec fn frontier_spec(&self) -> Seq<usize> { self.work.queue.values@ }
    /// Domain discovery is the actual work owner's visited projection.
    pub closed spec fn discovered_spec(&self, node: usize) -> bool {
        node < self.hierarchy.num_nodes && self.work.visited_contains_spec((node + 1) as usize)
    }
    /// Joint immutable-context, task-bijection and exact considered/frontier contract.
    pub closed spec fn inv(&self) -> bool {
        &&& self.hierarchy.type_invariant()
        &&& self.hierarchy.strict_level_descent()
        &&& self.hierarchy.parent_edge_agreement()
        &&& self.hierarchy.parent_has_edge()
        &&& self.hierarchy.cost_monotonicity()
        &&& self.arrangement.inv()
        &&& crate::connectives::ordering_pass::inverse_permutation(self.order_spec(), self.ranks_spec())
        &&& self.order_spec().len() == self.hierarchy.num_nodes
        &&& crate::connectives::ordering_pass::arranged(self.order_spec(),
            &HierarchyLevelOrder { hierarchy: &self.hierarchy })
        &&& self.considered_spec() <= self.hierarchy.num_nodes
        &&& self.work.inv()
        &&& self.work.root == 0
        &&& self.work.num_nodes as int == self.hierarchy.num_nodes as int + 1
        &&& self.work.budget.capacity as int == 2 * self.work.num_nodes as int
        &&& 1 <= self.work.accepted.accumulated@.len()
        &&& self.work.visited_contains_spec(0)
        &&& self.work.accepted_contains_spec(0)
        &&& !self.work.queue_contains_spec(0)
        &&& self.work.queue.values@.len() == self.hierarchy.num_nodes - self.considered_spec()
        &&& forall|node: usize| node < self.hierarchy.num_nodes ==> {
            &&& self.work.queue_contains_spec((node + 1) as usize)
                == (#[trigger] self.ranks_spec()[node as int] >= self.considered_spec())
            &&& self.work.visited_contains_spec((node + 1) as usize)
                == (self.ranks_spec()[node as int] < self.considered_spec())
            &&& self.work.accepted_contains_spec((node + 1) as usize)
                == (self.ranks_spec()[node as int] < self.considered_spec())
        }
    }

    /// Bind the unchanged finite forest to canonical work storage and ordering.
    ///
    /// # Errors
    /// Returns the original hierarchy on storage or checked task-budget overflow.
    pub(crate) fn try_new(hierarchy: QualityHierarchy)
        -> (result: Result<Self, (crate::composition_api::TraversalBuildError, QualityHierarchy)>)
        requires hierarchy.type_invariant(), hierarchy.strict_level_descent(),
            hierarchy.parent_edge_agreement(), hierarchy.parent_has_edge(), hierarchy.cost_monotonicity(),
        ensures result matches Ok(profile) ==> profile.inv() && profile.hierarchy_spec() == hierarchy
            && profile.considered_spec() == 0,
            result matches Err((_, original)) ==> original == hierarchy,
    {
        use crate::composition_api::TraversalBuildError;
        let count = hierarchy.num_nodes;
        let work_count = match count.checked_add(1) {
            Some(count) => count, None => return Err((TraversalBuildError::WorkBudgetOverflow, hierarchy)),
        };
        let budget = match (work_count as u64).checked_mul(2) {
            Some(budget) => budget,
            None => return Err((TraversalBuildError::WorkBudgetOverflow, hierarchy)),
        };
        let order = HierarchyLevelOrder { hierarchy: &hierarchy };
        let arrangement = match IndexArrangement::try_new(count, &order) {
            Ok(arrangement) => arrangement, Err(_) => return Err((TraversalBuildError::StorageUnavailable, hierarchy)),
        };
        let mut work = match TraversalEngine::try_new(work_count, 0, budget) {
            Ok(work) => work, Err(reason) => return Err((reason, hierarchy)),
        };
        proof {
            crate::connectives::buffer::indexed_value_contained(work.queue.values@, 0);
            assert(work.queue_contains_spec(0));
            assert(!work.visited_contains_spec(0));
        }
        work.visit_node(0);
        assert forall|node: usize| node < count implies
            #[trigger] work.queue_contains_spec((node + 1) as usize)
            && !work.visited_contains_spec((node + 1) as usize)
            && !work.accepted_contains_spec((node + 1) as usize) by {
            assert(0 < node + 1 < work_count);
        }
        Ok(Self { hierarchy, arrangement, work })
    }

    /// Discover the next actual forest node in stable parent-before-child order.
    /// None is returned only after actual work-frontier and arrangement exhaustion.
    #[expect(clippy::indexing_slicing, reason = "accepted-work progress and the arrangement permutation prove the selected original node is in range")]
    #[expect(clippy::arithmetic_side_effects, reason = "the accepted-work owner retains its synthetic root and task successors are within the admitted work universe")]
    pub fn step(&mut self) -> (node: Option<usize>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).hierarchy_spec() == old(self).hierarchy_spec(),
            final(self).order_spec() == old(self).order_spec(), final(self).ranks_spec() == old(self).ranks_spec(),
            node is Some ==> node.unwrap() == old(self).order_spec()[old(self).considered_spec() as int]
                && final(self).considered_spec() == old(self).considered_spec() + 1
                && final(self).discovered_spec(node.unwrap())
                && (old(self).hierarchy_spec().parent@[node.unwrap() as int] < old(self).hierarchy_spec().num_nodes
                    ==> old(self).discovered_spec(old(self).hierarchy_spec().parent@[node.unwrap() as int])),
            node is None ==> final(self).considered_spec() == old(self).considered_spec()
                && final(self).frontier_spec().len() == 0
                && final(self).considered_spec() == final(self).hierarchy_spec().num_nodes,
    {
        let count = self.hierarchy.num_nodes;
        let cursor = self.work.accepted.len() - 1;
        if cursor == count { return None; }
        let positions = self.arrangement.positions();
        let node = positions[cursor];
        let ghost before = *self;
        let parent = self.hierarchy.parent_of(node);
        let _ = parent;
        proof {
            self.arrangement.expose_certificate();
            assert(self.ranks_spec()[node as int] == cursor);
            if parent < count {
                self.hierarchy.expose_parent_edge(node);
                let edge = choose|edge: int| 0 <= edge < self.hierarchy.edges@.len()
                    && #[trigger] self.hierarchy.edges@[edge] == (parent, node);
                assert(self.hierarchy.level@[parent as int] > self.hierarchy.level@[node as int]);
                let parent_rank = self.ranks_spec()[parent as int];
                assert(self.order_spec()[parent_rank as int] == parent);
                if parent_rank > cursor {
                    assert(crate::connectives::ordering_pass::position_le(
                        &HierarchyLevelOrder { hierarchy: &self.hierarchy }, node, parent));
                    assert(self.hierarchy.level@[node as int] >= self.hierarchy.level@[parent as int]);
                    assert(false);
                } else if parent_rank == cursor {
                    assert(parent == node); assert(false);
                }
                assert(self.discovered_spec(parent));
            }
            self.work.expose();
            assert(self.work.budget.allocated as int == 2 * (cursor as int + 1));
            assert(self.work.budget.allocated as int + 2 <= self.work.budget.capacity);
            assert(self.work.queue_contains_spec((node + 1) as usize));
            assert(!self.work.visited_contains_spec((node + 1) as usize));
        }
        self.work.visit_node(node + 1);
        proof {
            assert forall|other: usize| other < count implies {
                &&& self.work.queue_contains_spec((other + 1) as usize)
                    == (#[trigger] self.ranks_spec()[other as int] >= self.considered_spec())
                &&& self.work.visited_contains_spec((other + 1) as usize)
                    == (self.ranks_spec()[other as int] < self.considered_spec())
                &&& self.work.accepted_contains_spec((other + 1) as usize)
                    == (self.ranks_spec()[other as int] < self.considered_spec())
            } by {
                if other != node {
                    assert(self.ranks_spec()[other as int] != cursor) by {
                        if self.ranks_spec()[other as int] == cursor {
                            assert(self.order_spec()[cursor as int] == other);
                            assert(false);
                        }
                    }
                }
                assert(before.work.queue_contains_spec((other + 1) as usize)
                    == (self.ranks_spec()[other as int] >= cursor));
                assert(before.work.visited_contains_spec((other + 1) as usize)
                    == (self.ranks_spec()[other as int] < cursor));
                assert(before.work.accepted_contains_spec((other + 1) as usize)
                    == (self.ranks_spec()[other as int] < cursor));
            }
        }
        Some(node)
    }

    /// Considered-node count projected from the actual accepted-work owner.
    #[expect(clippy::arithmetic_side_effects, reason = "the actual accepted-work owner always retains its synthetic root")]
    pub fn considered(&self) -> (count: usize)
        requires self.inv(), ensures count == self.considered_spec(),
    { self.work.accepted.len() - 1 }
    /// Remaining work under the actual frontier owner, without a caller fold.
    pub fn pending(&self) -> (count: usize)
        requires self.inv(), ensures count == self.frontier_spec().len(),
    { self.work.queue.len() }
    /// Borrow unchanged node levels in original identity order.
    pub fn levels(&self) -> (levels: &[u64])
        requires self.inv(), ensures levels@ == self.hierarchy_spec().level@,
    { self.hierarchy.level.as_slice() }
    /// Borrow unchanged costs, including zero-cost nodes.
    pub fn costs(&self) -> (costs: &[u64])
        requires self.inv(), ensures costs@ == self.hierarchy_spec().cost@,
    { self.hierarchy.cost.as_slice() }
    /// Read discovery from the actual work owner's visited Markers.
    #[expect(clippy::arithmetic_side_effects, reason = "node < hierarchy.num_nodes and the task-universe admission bound its mapped successor")]
    pub fn discovered(&self, node: usize) -> (yes: bool)
        requires self.inv(), ensures yes == self.discovered_spec(node),
    { node < self.hierarchy.num_nodes && self.work.visited_contains(node + 1) }

    /// Seal the unchanged context and discovery only after actual frontier exhaustion.
    ///
    /// # Errors
    /// Returns the original profile unchanged if any work remains.
    #[expect(clippy::result_large_err, reason = "early completion returns custody of the exact original canonical owners without allocation or dropping work")]
    pub fn finish(self) -> (result: Result<DiscoveredHierarchy, Self>)
        requires self.inv(),
        ensures result matches Ok(done) ==> done.inv() && done.profile_spec() == self,
            result matches Err(returned) ==> returned == self && self.frontier_spec().len() > 0,
    {
        if self.work.queue.is_empty() { Ok(DiscoveredHierarchy { profile: self }) }
        else { Err(self) }
    }
}

/// Immutable completed finite forest discovery, retaining the original owners.
pub struct DiscoveredHierarchy { profile: RootedTraversal }
impl DiscoveredHierarchy {
    /// Exact consumed profile, without an exposed mutator.
    pub closed spec fn profile_spec(&self) -> RootedTraversal { self.profile }
    /// Completion requires both actual canonical owners to be exhausted.
    pub closed spec fn inv(&self) -> bool {
        self.profile.inv() && self.profile.frontier_spec().len() == 0
            && self.profile.considered_spec() == self.profile.hierarchy_spec().num_nodes
    }
    /// Every original node, including every root, was discovered exactly once.
    pub proof fn expose_complete(&self)
        requires self.inv(),
        ensures forall|node: usize| node < self.profile_spec().hierarchy_spec().num_nodes
            ==> #[trigger] self.profile_spec().discovered_spec(node),
    {
        self.profile.arrangement.expose_certificate();
        assert forall|node: usize| node < self.profile.hierarchy.num_nodes implies
            #[trigger] self.profile.discovered_spec(node) by {
            assert(self.profile.ranks_spec()[node as int] < self.profile.hierarchy.num_nodes);
            assert(self.profile.work.visited_contains_spec((node + 1) as usize));
        }
    }
    /// Borrow the unchanged hierarchy's original levels.
    pub fn levels(&self) -> (levels: &[u64])
        requires self.inv(), ensures levels@ == self.profile_spec().hierarchy_spec().level@,
    { self.profile.levels() }
    /// Borrow the actual completed OrderingPass arrangement.
    pub fn discovery_order(&self) -> (positions: &[usize])
        requires self.inv(), ensures positions@ == self.profile_spec().order_spec(),
    { self.profile.arrangement.positions() }
}

/// The fixed cost used by the retained TraversalEngine model.
pub const NODE_COST: u64 = 2;

/// Scoped candidate identity issued only by a traversal's Registry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidateId { scope: u64, index: usize }
impl CandidateId {
    /// Caller-owned unique scope for this traversal instance.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Dense original candidate position.
    pub closed spec fn index_spec(&self) -> usize { self.index }
    /// Inspect the issued original position without exposing construction.
    pub fn index(&self) -> (index: usize) ensures index == self.index_spec(), { self.index }
}

/// Dynamic traversal admission and arrangement refusals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidateTraversalError {
    /// The explicit candidate storage ceiling has been reached.
    CandidateCapacity,
    /// Extension admission has been closed.
    Closed,
    /// The parent token belongs to another caller-owned scope.
    ForeignScope,
    /// No retained candidate has this issued position.
    UnknownCandidate,
    /// Extensions require a parent already visited by the work owner.
    ParentPending,
    /// Hierarchy level or cost does not satisfy the actual AddChild guard.
    InvalidExtension,
    /// A canonical owner's storage reservation failed before publication.
    StorageUnavailable,
    /// The synthetic-root universe or its nonbinding work account overflows.
    WorkBudgetOverflow,
}

/// Dynamic typed candidate discovery, retaining one original context and no copied frontier.
///
/// The caller supplies a unique scope and a finite storage ceiling. Extensions can
/// be admitted after their parent is visited. Domain costs, including zero, are
/// distinct from the proved nonbinding work account. Payloads are retained once.
/// A context containing interior mutation requires the caller's frozen-version
/// binding; retaining arbitrary C does not establish a deep-freeze contract.
pub struct CandidateTraversal<C, T> {
    context: C,
    scope: u64,
    candidates: ResourceRegistry<usize, T>,
    hierarchy: QualityHierarchy,
    work: TraversalEngine,
    closed: Marker,
}

impl<C, T> CandidateTraversal<C, T> {
    /// Original context, never replaced by an admission or visit.
    pub closed spec fn context_spec(&self) -> C { self.context }
    /// Original typed candidate custody in dense Registry order.
    pub closed spec fn candidates_spec(&self) -> Seq<(usize, T)> { self.candidates.entries@ }
    /// Actual domain hierarchy, including unused admitted storage slots.
    pub closed spec fn hierarchy_spec(&self) -> QualityHierarchy { self.hierarchy }
    /// Scope supplied by the caller's identity owner.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Extension closure is the actual Marker.
    pub closed spec fn closed_spec(&self) -> bool { self.closed.marked }
    /// The actual work owner's discovery projection for an issued position.
    pub closed spec fn visited_spec(&self, index: usize) -> bool {
        index < self.candidates_spec().len() && self.work.visited_contains_spec((index + 1) as usize)
    }
    /// Unvisited registered candidates, derived by the work owner's aggregate.
    pub closed spec fn pending_spec(&self) -> int {
        self.candidates_spec().len() + 1 - marked_count(self.work.visited@, self.work.visited@.len() as int)
    }
    /// Retained frontier is the original TraversalEngine Buffer.
    pub closed spec fn frontier_spec(&self) -> Seq<usize> { self.work.queue.values@ }
    /// Dense original custody, parent discovery and exact work accounting.
    pub closed spec fn inv(&self) -> bool {
        &&& self.candidates.unique_identities()
        &&& self.candidates_spec().len() <= self.hierarchy.num_nodes
        &&& forall|i: int| 0 <= i < self.candidates_spec().len() ==> #[trigger] self.candidates_spec()[i].0 == i
        &&& self.hierarchy.type_invariant()
        &&& self.hierarchy.strict_level_descent()
        &&& self.hierarchy.parent_edge_agreement()
        &&& self.hierarchy.parent_has_edge()
        &&& self.hierarchy.cost_monotonicity()
        &&& self.hierarchy.max_level == u64::MAX
        &&& forall|e: int| 0 <= e < self.hierarchy.edges@.len() ==> {
            &&& #[trigger] self.hierarchy.edges@[e].0 < self.candidates_spec().len()
            &&& self.hierarchy.edges@[e].1 < self.candidates_spec().len()
        }
        &&& forall|i: usize| self.candidates_spec().len() <= i < self.hierarchy.num_nodes ==> {
            &&& #[trigger] self.hierarchy.parent@[i as int] == self.hierarchy.num_nodes
            &&& self.hierarchy.level@[i as int] == 0
            &&& self.hierarchy.cost@[i as int] == 0
        }
        &&& forall|i: usize| i < self.candidates_spec().len()
            && #[trigger] self.hierarchy.parent@[i as int] < self.hierarchy.num_nodes ==>
                self.visited_spec(self.hierarchy.parent@[i as int])
        &&& self.work.inv()
        &&& self.work.root == 0
        &&& self.work.num_nodes as int == self.hierarchy.num_nodes as int + 1
        &&& self.work.budget.capacity as int == 2 * self.work.num_nodes as int
        &&& self.work.visited_contains_spec(0) && self.work.accepted_contains_spec(0)
        &&& !self.work.queue_contains_spec(0)
        &&& self.work.accepted.accumulated@.len() == marked_count(self.work.visited@, self.work.visited@.len() as int)
        &&& forall|i: usize| i < self.hierarchy.num_nodes ==> {
            &&& #[trigger] self.work.visited_contains_spec((i + 1) as usize) == self.work.accepted_contains_spec((i + 1) as usize)
            &&& (i >= self.candidates_spec().len() ==> !self.work.visited_contains_spec((i + 1) as usize))
            &&& (i < self.candidates_spec().len() || !self.closed_spec()) ==>
                self.work.queue_contains_spec((i + 1) as usize) == !self.work.visited_contains_spec((i + 1) as usize)
        }
    }

    /// Pre-admit all hierarchy, payload and work storage before exposing an owner.
    ///
    /// # Errors
    /// Returns the unchanged original context on allocation or work-account overflow.
    pub fn try_new(context: C, scope: u64, candidate_ceiling: usize)
        -> (result: Result<Self, (CandidateTraversalError, C)>)
        ensures result matches Ok(owner) ==> owner.inv() && owner.context_spec() == context
            && owner.scope_spec() == scope && owner.candidates_spec().len() == 0 && !owner.closed_spec(),
            result matches Err((_, original)) ==> original == context,
    {
        use CandidateTraversalError::{StorageUnavailable, WorkBudgetOverflow};
        let work_count = match candidate_ceiling.checked_add(1) {
            Some(count) => count, None => return Err((WorkBudgetOverflow, context)),
        };
        let capacity = match (work_count as u64).checked_mul(2) {
            Some(capacity) => capacity, None => return Err((WorkBudgetOverflow, context)),
        };
        let hierarchy = match QualityHierarchy::try_new(candidate_ceiling, u64::MAX) {
            Ok(hierarchy) => hierarchy, Err(_) => return Err((StorageUnavailable, context)),
        };
        let mut candidates = ResourceRegistry::new();
        if candidates.try_reserve_entries(candidate_ceiling).is_err() { return Err((StorageUnavailable, context)); }
        let mut work = match TraversalEngine::try_new(work_count, 0, capacity) {
            Ok(work) => work, Err(_) => return Err((StorageUnavailable, context)),
        };
        proof { crate::connectives::buffer::indexed_value_contained(work.queue.values@, 0); }
        let ghost initial_markers = work.visited@;
        work.visit_node(0);
        proof {
            assert(work.visited_contains_spec(0));
            marked_count_zero(initial_markers, initial_markers.len() as int);
            assert forall|i: int| 0 <= i < initial_markers.len() && i != 0 implies
                #[trigger] work.visited@[i].marked == initial_markers[i].marked by {
                assert(work.visited_contains_spec(i as usize) == false);
            }
            marked_count_changed(initial_markers, work.visited@, 0, work.visited@.len() as int);
        }
        Ok(Self { context, scope, candidates, hierarchy, work, closed: Marker::new(false) })
    }

    /// Retain a root or an extension of an already discovered parent.
    ///
    /// # Errors
    /// Every refusal returns the exact original value and preserves logical owner state.
    #[expect(clippy::arithmetic_side_effects, reason = "a registered position is below the admitted hierarchy ceiling and its work successor fits")]
    pub fn admit(&mut self, parent: Option<CandidateId>, value: T, level: u64, cost: u64)
        -> (result: Result<CandidateId, (CandidateTraversalError, T)>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).context_spec() == old(self).context_spec(),
            final(self).scope_spec() == old(self).scope_spec(), final(self).closed_spec() == old(self).closed_spec(),
            result matches Err((_, original)) ==> original == value
                && final(self).candidates_spec() == old(self).candidates_spec()
                && final(self).hierarchy_spec() == old(self).hierarchy_spec()
                && final(self).frontier_spec() == old(self).frontier_spec(),
            result matches Ok(id) ==> id.scope_spec() == old(self).scope_spec()
                && id.index_spec() == old(self).candidates_spec().len()
                && final(self).candidates_spec() == old(self).candidates_spec().push((id.index_spec(), value))
                && !final(self).visited_spec(id.index_spec())
                && final(self).hierarchy_spec().level@[id.index_spec() as int] == level
                && final(self).hierarchy_spec().cost@[id.index_spec() as int] == cost,
    {
        use CandidateTraversalError::*;
        if self.closed.is_marked() { return Err((Closed, value)); }
        let index = self.candidates.entries.len();
        if index == self.hierarchy.num_nodes { return Err((CandidateCapacity, value)); }
        if let Some(parent) = parent {
            if parent.scope != self.scope { return Err((ForeignScope, value)); }
            if parent.index >= index { return Err((UnknownCandidate, value)); }
            if !self.work.visited_contains(parent.index + 1) { return Err((ParentPending, value)); }
            if self.hierarchy.level_of(parent.index) <= level || self.hierarchy.cost_of(parent.index) > cost {
                return Err((InvalidExtension, value));
            }
        }
        let ghost before = *self;
        proof {
            assert forall|e: int| 0 <= e < self.hierarchy.edges@.len() implies
                #[trigger] self.hierarchy.edges@[e].0 != index by {}
        }
        self.hierarchy.set_node_properties(index, level, cost);
        if let Some(parent) = parent {
            proof { assert(!self.hierarchy.edge_exists(parent.index, index)); }
            self.hierarchy.add_child(parent.index, index);
        }
        proof {
            assert forall|i: int| 0 <= i < self.candidates.entries@.len() implies
                #[trigger] self.candidates.entries@[i].0.identity() != index.identity() by {}
            crate::primitives::resource_registry::without_identity_to_absent(
                self.candidates.entries@, index, self.candidates.entries@.len() as int);
        }
        self.candidates.register_key(index, value);
        proof {
            assert forall|i: usize| i < self.candidates_spec().len()
                && #[trigger] self.hierarchy.parent@[i as int] < self.hierarchy.num_nodes implies
                    self.visited_spec(self.hierarchy.parent@[i as int]) by {
                if i < index { assert(before.visited_spec(before.hierarchy.parent@[i as int])); }
            }
        }
        Ok(CandidateId { scope: self.scope, index })
    }

    /// Visit the first unresolved registered candidate in stable descending level order.
    ///
    /// # Errors
    /// Arrangement storage refusal leaves every retained owner unchanged.
    #[expect(clippy::indexing_slicing, reason = "the local canonical Cursor is below the arrangement's admitted registered prefix")]
    #[expect(clippy::arithmetic_side_effects, reason = "registered indices and the arrangement cursor remain below their admitted finite ceilings")]
    pub fn step(&mut self) -> (result: Result<Option<CandidateId>, CandidateTraversalError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).context_spec() == old(self).context_spec(),
            final(self).scope_spec() == old(self).scope_spec(), final(self).closed_spec() == old(self).closed_spec(),
            final(self).candidates_spec() == old(self).candidates_spec(),
            final(self).hierarchy_spec() == old(self).hierarchy_spec(),
            result is Err ==> *final(self) == *old(self),
            result matches Ok(Some(id)) ==> id.scope_spec() == final(self).scope_spec()
                && !old(self).visited_spec(id.index_spec()) && final(self).visited_spec(id.index_spec())
                && final(self).pending_spec() == old(self).pending_spec() - 1
                && (forall|other: usize| other < old(self).candidates_spec().len() && !old(self).visited_spec(other) ==>
                    old(self).hierarchy_spec().level@[id.index_spec() as int] >= #[trigger] old(self).hierarchy_spec().level@[other as int]
                    && (old(self).hierarchy_spec().level@[id.index_spec() as int] == old(self).hierarchy_spec().level@[other as int]
                        ==> id.index_spec() <= other)),
            result matches Ok(None) ==> *final(self) == *old(self) && final(self).pending_spec() == 0,
    {
        let count = self.candidates.entries.len();
        let order = HierarchyLevelOrder { hierarchy: &self.hierarchy };
        let arrangement = match IndexArrangement::try_new(count, &order) {
            Ok(arrangement) => arrangement,
            Err(_) => return Err(CandidateTraversalError::StorageUnavailable),
        };
        let positions = arrangement.positions();
        let mut cursor = Cursor::new(0);
        while cursor.position < count
            invariant self.inv(), count == self.candidates_spec().len(), arrangement.inv(),
                *self == *old(self),
                arrangement.positions_spec().len() == count,
                crate::connectives::ordering_pass::permutation(arrangement.positions_spec(), count as nat),
                crate::connectives::ordering_pass::inverse_permutation(arrangement.positions_spec(), arrangement.inverse_spec()),
                crate::connectives::ordering_pass::arranged(arrangement.positions_spec(),
                    &HierarchyLevelOrder { hierarchy: &self.hierarchy }),
                cursor.position <= count, positions@ == arrangement.positions_spec(),
                forall|rank: int| 0 <= rank < cursor.position ==>
                    #[trigger] self.visited_spec(positions@[rank]),
            decreases count - cursor.position,
        {
            let index = positions[cursor.position];
            if !self.work.visited_contains(index + 1) {
                let ghost before_markers = self.work.visited@;
                proof {
                    assert forall|other: usize| other < count && !self.visited_spec(other) implies
                        self.hierarchy.level@[index as int] >= #[trigger] self.hierarchy.level@[other as int]
                        && (self.hierarchy.level@[index as int] == self.hierarchy.level@[other as int] ==> index <= other) by {
                        let rank = arrangement.inverse_spec()[other as int];
                        assert(positions@[rank as int] == other);
                        if rank < cursor.position { assert(self.visited_spec(other)); assert(false); }
                        else if rank == cursor.position { assert(other == index); }
                        else {
                            assert(crate::connectives::ordering_pass::position_le(
                                &HierarchyLevelOrder { hierarchy: &self.hierarchy }, index, other));
                        }
                    }
                    marked_count_missing(self.work.visited@, (index + 1) as int, self.work.visited@.len() as int);
                    assert(self.work.budget.allocated as int + 2 <= self.work.budget.capacity);
                }
                self.work.visit_node(index + 1);
                proof {
                    assert(self.work.visited_contains_spec((index + 1) as usize));
                    assert forall|i: int| 0 <= i < before_markers.len() && i != index + 1 implies
                        #[trigger] self.work.visited@[i].marked == before_markers[i].marked by {
                        assert(self.work.visited_contains_spec(i as usize) == before_markers[i].marked);
                    }
                    marked_count_changed(before_markers, self.work.visited@, (index + 1) as int, self.work.visited@.len() as int);
                }
                return Ok(Some(CandidateId { scope: self.scope, index }));
            }
            cursor.advance_to(cursor.position + 1);
        }
        proof {
            assert forall|index: usize| index < count implies #[trigger] self.visited_spec(index) by {
                let rank = arrangement.inverse_spec()[index as int];
                assert(positions@[rank as int] == index);
            }
            self.expose_pending();
            self.expose_unregistered();
            marked_count_prefix(self.work.visited@, (count + 1) as int, self.work.visited@.len() as int);
            assert forall|i: int| 0 <= i < count + 1 implies #[trigger] self.work.visited@[i].marked by {
                if i > 0 { assert(self.visited_spec((i - 1) as usize)); }
            }
            marked_count_full(self.work.visited@, (count + 1) as int);
        }
        Ok(None)
    }

    proof fn expose_pending(&self)
        requires self.inv(),
        ensures 0 <= self.pending_spec() <= self.candidates_spec().len(),
    {
        let count = self.candidates_spec().len() as int;
        self.expose_unregistered();
        marked_count_prefix(self.work.visited@, count + 1, self.work.visited@.len() as int);
        marked_count_bounds(self.work.visited@, count + 1);
        marked_count_has_root(self.work.visited@, count + 1);
    }
    proof fn expose_unregistered(&self)
        requires self.inv(),
        ensures forall|i: int| self.candidates_spec().len() + 1 <= i < self.work.visited@.len()
            ==> !#[trigger] self.work.visited@[i].marked,
    {
        assert forall|i: int| self.candidates_spec().len() + 1 <= i < self.work.visited@.len()
            implies !#[trigger] self.work.visited@[i].marked by {
            let node = (i - 1) as usize;
            assert(self.candidates_spec().len() <= node < self.hierarchy.num_nodes);
            assert(!self.work.visited_contains_spec((node + 1) as usize));
            assert(!self.work.visited_contains_spec(i as usize));
        }
    }
    /// Borrow the original immutable context.
    pub fn context(&self) -> (context: &C) ensures *context == self.context_spec(), { &self.context }
    /// Number of original candidates retained by Registry.
    pub fn len(&self) -> (count: usize) ensures count == self.candidates_spec().len(), { self.candidates.entries.len() }
    /// Whether Registry has no candidate.
    pub fn is_empty(&self) -> (empty: bool) ensures empty == (self.candidates_spec().len() == 0), { self.len() == 0 }
    /// Pending count from the actual work owner's visited aggregate.
    #[expect(clippy::arithmetic_side_effects, reason = "the joint registered-prefix proof bounds visited count between one and registered count plus the synthetic root")]
    pub fn pending(&self) -> (pending: usize)
        requires self.inv(), ensures pending == self.pending_spec(),
    {
        proof { self.expose_pending(); }
        self.candidates.entries.len() + 1 - self.work.visited_count()
    }
    /// Borrow a retained original value; foreign scope and unknown identities return None.
    pub fn get(&self, id: CandidateId) -> (value: Option<&T>)
        requires self.inv(),
        ensures value is Some <==> id.scope_spec() == self.scope_spec() && id.index_spec() < self.candidates_spec().len(),
            value matches Some(value) ==> id.scope_spec() == self.scope_spec()
            && id.index_spec() < self.candidates_spec().len()
            && *value == self.candidates_spec()[id.index_spec() as int].1,
    {
        if id.scope != self.scope || id.index >= self.candidates.entries.len() { return None; }
        proof { crate::primitives::resource_registry::identity_entry_at(self.candidates.entries@, id.index as int); }
        match self.candidates.lookup_key_ref(&id.index) {
            Some(value) => {
                proof { self.candidates.unique_identity_value(id.index, *value, self.candidates.entries@[id.index as int].1); }
                Some(value)
            },
            None => { assert(false); None },
        }
    }
    /// Close new extension admission while retaining all drainable work.
    pub fn close(&mut self)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).closed_spec(),
            final(self).candidates_spec() == old(self).candidates_spec(),
            final(self).context_spec() == old(self).context_spec(), final(self).pending_spec() == old(self).pending_spec(),
    { let _ = self.closed.set(); }

    /// Seal only a closed, completely discovered candidate set.
    ///
    /// # Errors
    /// Returns the original owner if admission remains open or any registered work remains.
    #[expect(clippy::result_large_err, reason = "refusal returns exact owner custody rather than allocating a box or dropping pending candidates")]
    #[expect(clippy::arithmetic_side_effects, reason = "the cleanup Cursor visits only inactive positions below the admitted hierarchy ceiling")]
    pub fn finish(self) -> (result: Result<DiscoveredCandidates<C, T>, Self>)
        requires self.inv(),
        ensures result matches Ok(done) ==> done.inv() && done.profile_spec().context_spec() == self.context_spec()
            && done.profile_spec().candidates_spec() == self.candidates_spec(),
            result matches Err(original) ==> original == self,
    {
        if !self.closed.is_marked() || self.pending() != 0 { return Err(self); }
        let mut owner = self;
        let count = owner.candidates.entries.len();
        let mut cursor = Cursor::new(count);
        while cursor.position < owner.hierarchy.num_nodes
            invariant owner.inv(), owner.closed_spec(), owner.pending_spec() == 0,
                owner.context_spec() == self.context_spec(), owner.candidates_spec() == self.candidates_spec(),
                count == owner.candidates_spec().len(), count <= cursor.position <= owner.hierarchy.num_nodes,
                forall|index: usize| count <= index < cursor.position ==>
                    !#[trigger] owner.work.queue_contains_spec((index + 1) as usize),
            decreases owner.hierarchy.num_nodes - cursor.position,
        {
            let ghost before = owner;
            if owner.work.queue_contains(cursor.position + 1) { owner.work.skip(cursor.position + 1); }
            proof {
                assert forall|i: usize| i < owner.hierarchy.num_nodes implies {
                    &&& #[trigger] owner.work.visited_contains_spec((i + 1) as usize) == owner.work.accepted_contains_spec((i + 1) as usize)
                    &&& (i >= owner.candidates_spec().len() ==> !owner.work.visited_contains_spec((i + 1) as usize))
                    &&& (i < owner.candidates_spec().len() || !owner.closed_spec()) ==>
                        owner.work.queue_contains_spec((i + 1) as usize) == !owner.work.visited_contains_spec((i + 1) as usize)
                } by {
                    assert(before.work.queue_contains_spec((i + 1) as usize) == !before.work.visited_contains_spec((i + 1) as usize)
                        || i >= count);
                }
                assert(owner.inv());
            }
            cursor.advance_to(cursor.position + 1);
        }
        proof {
            assert forall|index: usize| #[trigger] owner.work.queue_contains_spec(index) implies false by {
                owner.work.expose();
                let entry = choose|entry: int| 0 <= entry < owner.work.queue.values@.len()
                    && owner.work.queue.values@[entry] == index;
                assert(index < owner.work.num_nodes);
                if index > 0 && index <= count {
                    owner.expose_unregistered();
                    marked_count_prefix(owner.work.visited@, (count + 1) as int, owner.work.visited@.len() as int);
                    if !owner.work.visited_contains_spec(index) {
                        marked_count_missing(owner.work.visited@, index as int, (count + 1) as int);
                    }
                    assert(owner.work.visited_contains_spec(index));
                    let node = (index - 1) as usize;
                    assert(node < count);
                    assert(!owner.work.queue_contains_spec((node + 1) as usize));
                } else if index > count {
                    let node = (index - 1) as usize;
                    assert(count <= node < cursor.position);
                    assert(!owner.work.queue_contains_spec((node + 1) as usize));
                } else {
                    assert(!owner.work.queue_contains_spec(0));
                }
            }
            if owner.work.queue.values@.len() > 0 {
                crate::connectives::buffer::indexed_value_contained(owner.work.queue.values@, 0);
                assert(owner.work.queue_contains_spec(owner.work.queue.values@[0]));
                assert(false);
            }
            assert(owner.work.queue.values@.len() == 0);
        }
        Ok(DiscoveredCandidates { profile: owner })
    }
}

/// Completed immutable typed discovery retaining context, hierarchy and original payload owners.
pub struct DiscoveredCandidates<C, T> { profile: CandidateTraversal<C, T> }
impl<C, T> DiscoveredCandidates<C, T> {
    /// Exact retained profile without exposed mutation.
    pub closed spec fn profile_spec(&self) -> CandidateTraversal<C, T> { self.profile }
    /// Canonical closure and work exhaustion, with no unpublished accepted candidate.
    pub closed spec fn inv(&self) -> bool {
        self.profile.inv() && self.profile.closed_spec() && self.profile.pending_spec() == 0
            && self.profile.frontier_spec().len() == 0
    }
    /// Export closure, actual work exhaustion and discovery of every original candidate.
    pub proof fn expose_complete(&self)
        requires self.inv(),
        ensures self.profile_spec().closed_spec(), self.profile_spec().pending_spec() == 0,
            self.profile_spec().frontier_spec().len() == 0,
            forall|index: usize| index < self.profile_spec().candidates_spec().len() ==>
                #[trigger] self.profile_spec().visited_spec(index),
    {
        self.profile.expose_unregistered();
        let count = self.profile.candidates_spec().len() as int;
        marked_count_prefix(self.profile.work.visited@, count + 1, self.profile.work.visited@.len() as int);
        assert forall|index: usize| index < count implies #[trigger] self.profile.visited_spec(index) by {
            if !self.profile.work.visited_contains_spec((index + 1) as usize) {
                marked_count_missing(self.profile.work.visited@, index as int + 1, count + 1);
                assert(false);
            }
        }
    }
    /// Borrow the retained context.
    pub fn context(&self) -> (context: &C) ensures *context == self.profile_spec().context_spec(), { self.profile.context() }
    /// Borrow original candidates from the retained Registry.
    pub fn get(&self, id: CandidateId) -> (value: Option<&T>)
        requires self.inv(),
        ensures value matches Some(value) ==> *value == self.profile_spec().candidates_spec()[id.index_spec() as int].1,
    { self.profile.get(id) }
    /// Complete original candidate count.
    pub fn len(&self) -> (count: usize) ensures count == self.profile_spec().candidates_spec().len(), { self.profile.len() }
    /// Whether this completed set was empty.
    pub fn is_empty(&self) -> (empty: bool) ensures empty == (self.profile_spec().candidates_spec().len() == 0), { self.len() == 0 }
}

/// Number of set markers in the retained prefix.
pub open spec fn marked_count(markers: Seq<Marker>, n: int) -> int
    recommends 0 <= n <= markers.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        marked_count(markers, n - 1) + if markers[n - 1].marked { 1int } else { 0int }
    }
}

proof fn marked_count_bounds(markers: Seq<Marker>, n: int)
    requires 0 <= n <= markers.len(),
    ensures 0 <= marked_count(markers, n) <= n,
    decreases n,
{ if n > 0 { marked_count_bounds(markers, n - 1); } }

proof fn marked_count_zero(markers: Seq<Marker>, n: int)
    requires 0 <= n <= markers.len(), forall|i: int| 0 <= i < n ==> !#[trigger] markers[i].marked,
    ensures marked_count(markers, n) == 0,
    decreases n,
{ if n > 0 { marked_count_zero(markers, n - 1); } }

proof fn marked_count_full(markers: Seq<Marker>, n: int)
    requires 0 <= n <= markers.len(), forall|i: int| 0 <= i < n ==> #[trigger] markers[i].marked,
    ensures marked_count(markers, n) == n,
    decreases n,
{ if n > 0 { marked_count_full(markers, n - 1); } }

proof fn marked_count_prefix(markers: Seq<Marker>, prefix: int, n: int)
    requires 0 <= prefix <= n <= markers.len(),
        forall|i: int| prefix <= i < n ==> !#[trigger] markers[i].marked,
    ensures marked_count(markers, n) == marked_count(markers, prefix),
    decreases n - prefix,
{ if n > prefix { marked_count_prefix(markers, prefix, n - 1); } }

proof fn marked_count_missing(markers: Seq<Marker>, missing: int, n: int)
    requires 0 <= missing < n <= markers.len(), !markers[missing].marked,
    ensures marked_count(markers, n) < n,
    decreases n,
{
    if missing < n - 1 { marked_count_missing(markers, missing, n - 1); }
    else { marked_count_bounds(markers, n - 1); }
}

proof fn marked_count_has_root(markers: Seq<Marker>, n: int)
    requires 1 <= n <= markers.len(), markers[0].marked,
    ensures marked_count(markers, n) >= 1,
    decreases n,
{ if n > 1 { marked_count_has_root(markers, n - 1); } else { reveal_with_fuel(marked_count, 2); } }

proof fn marked_count_changed(before: Seq<Marker>, after: Seq<Marker>, changed: int, n: int)
    requires before.len() == after.len(), 0 <= changed < before.len(), 0 <= n <= before.len(),
        !before[changed].marked, after[changed].marked,
        forall|i: int| 0 <= i < before.len() && i != changed ==> #[trigger] after[i].marked == before[i].marked,
    ensures marked_count(after, n) == marked_count(before, n) + if changed < n { 1int } else { 0int },
    decreases n,
{ if n > 0 { marked_count_changed(before, after, changed, n - 1); } }

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

    /// Whether committed traversal cost exactly accounts for accepted nodes.
    pub open spec fn accepted_cost_accounting(&self) -> bool {
        self.budget.allocated as int
            == self.accepted.accumulated@.len() * NODE_COST as int
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

    /// Whether all component and cross-component traversal contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.budget_invariant()
        &&& self.accepted_cost_accounting()
        &&& self.accepted_subset_visited()
        &&& self.root_frontier_gate()
    }

    /// Expose the composition facts needed by checked facades and actions.
    pub proof fn expose(&self)
        requires self.inv(),
        ensures
            self.type_invariant(),
            self.budget_invariant(),
            self.accepted_cost_accounting(),
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
        reveal(TraversalEngine::accepted_cost_accounting);
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
            engine.accepted.original@.len() == 0,
            engine.accepted.accumulated@.len() == 0,
            engine.accepted.pending@.len() == 0,
            forall|node: int| 0 <= node < engine.visited@.len() ==>
                !#[trigger] engine.visited@[node].marked,
    {
        Self::initialize(num_nodes, root, max_budget, RelationshipGraph::new(num_nodes, 0),
            Vec::new(), Accumulator::from_accumulated(Vec::new()), Buffer::new(num_nodes))
    }

    /// Reserve every retained work owner before invoking the shared initialization.
    ///
    /// # Errors
    /// Returns the existing configuration refusals or StorageUnavailable before work publication.
    pub fn try_new(num_nodes: usize, root: usize, max_budget: u64)
        -> (result: Result<Self, crate::composition_api::TraversalBuildError>)
        ensures result matches Ok(engine) ==> engine.inv() && engine.num_nodes == num_nodes
            && engine.root == root && engine.budget.capacity == max_budget && engine.budget.allocated == 0
            && engine.queue.values@ == seq![root] && engine.accepted.accumulated@.len() == 0
            && forall|node: int| 0 <= node < engine.visited@.len() ==> !#[trigger] engine.visited@[node].marked,
    {
        use crate::composition_api::TraversalBuildError;
        if num_nodes == 0 { return Err(TraversalBuildError::NoNodes); }
        if root >= num_nodes { return Err(TraversalBuildError::RootOutOfRange); }
        let mut graph = RelationshipGraph::new(num_nodes, 0);
        if graph.registry.try_reserve_entries(num_nodes).is_err() { return Err(TraversalBuildError::StorageUnavailable); }
        let mut visited = Vec::new();
        if visited.try_reserve(num_nodes).is_err() { return Err(TraversalBuildError::StorageUnavailable); }
        let mut accepted_values = Vec::new();
        if accepted_values.try_reserve(num_nodes).is_err() { return Err(TraversalBuildError::StorageUnavailable); }
        let queue = match Buffer::try_new(num_nodes) {
            Ok(queue) => queue, Err(_) => return Err(TraversalBuildError::StorageUnavailable),
        };
        Ok(Self::initialize(num_nodes, root, max_budget, graph, visited,
            Accumulator::from_accumulated(accepted_values), queue))
    }

    #[expect(clippy::arithmetic_side_effects, reason = "both initialization cursors advance only while strictly below num_nodes")]
    fn initialize(num_nodes: usize, root: usize, max_budget: u64, mut graph: RelationshipGraph,
        mut visited: Vec<Marker>, accepted: Accumulator<usize>, mut queue: Buffer<usize>)
        -> (engine: TraversalEngine)
        requires root < num_nodes, graph.num_nodes == num_nodes, graph.max_weight == 0,
            graph.inv(), graph.registry.entries@.len() == 0, visited@.len() == 0,
            accepted.well_formed(), accepted.original@.len() == 0,
            accepted.accumulated@.len() == 0 && accepted.pending@.len() == 0,
            queue.well_formed(), queue.capacity == num_nodes, queue.values@.len() == 0,
        ensures engine.inv(), engine.num_nodes == num_nodes, engine.root == root,
            engine.budget.capacity == max_budget, engine.budget.allocated == 0,
            engine.queue.values@ == seq![root], engine.accepted.original@.len() == 0,
            engine.accepted.accumulated@.len() == 0, engine.accepted.pending@.len() == 0,
            forall|node: int| 0 <= node < engine.visited@.len() ==> !#[trigger] engine.visited@[node].marked,
    {
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
        assert(engine.accepted_cost_accounting());
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
    #[expect(clippy::indexing_slicing, reason = "the runtime node guard checks the retained visited-marker length")]
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
    #[expect(clippy::indexing_slicing, reason = "the visited-marker loop guards each marker read by the retained length")]
    #[expect(clippy::arithmetic_side_effects, reason = "count <= index < visited.len() bounds both count and cursor successors")]
    pub fn visited_count(&self) -> (count: usize)
        ensures count as int == marked_count(self.visited@, self.visited@.len() as int),
    {
        let mut count: usize = 0;
        let mut index: usize = 0;
        while index < self.visited.len()
            invariant
                index <= self.visited.len(),
                count <= index,
                count as int == marked_count(self.visited@, index as int),
            decreases self.visited.len() - index,
        {
            if self.visited[index].is_marked() {
                count = count + 1;
            }
            index = index + 1;
        }
        count
    }

    #[expect(clippy::arithmetic_side_effects, reason = "the child Cursor advances only while target < num_nodes, including its terminal boundary")]
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
            final(queue).values@.len() == num_nodes - 1,
            forall|index: int| 0 <= index < final(queue).values@.len() ==>
                #[trigger] final(queue).values@[index]
                    == if index < root as int {
                        index as usize
                    } else {
                        (index + 1) as usize
                    },
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
                queue.values@.len()
                    == target - if root < target { 1usize } else { 0usize },
                forall|index: int| 0 <= index < queue.values@.len() ==>
                    #[trigger] queue.values@[index]
                        == if index < root as int {
                            index as usize
                        } else {
                            (index + 1) as usize
                        },
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
            assert(queue.values@.len()
                == (target + 1) - if root < target + 1 { 1usize } else { 0usize });
            assert forall|index: int| 0 <= index < queue.values@.len() implies
                #[trigger] queue.values@[index]
                    == if index < root as int {
                        index as usize
                    } else {
                        (index + 1) as usize
                    } by {
                if edge && index == before_queue.len() {
                    assert(queue.values@[index] == target);
                    if target < root {
                        assert(index == target as int);
                    } else {
                        assert(target > root);
                        assert(index + 1 == target as int);
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
    #[expect(clippy::indexing_slicing, reason = "the enabled Visit precondition and representation invariant bound the node's retained marker index")]
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
            final(self).graph == old(self).graph,
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
            final(self).accepted.original@ == if old(self).budget.allocated as int
                    + NODE_COST as int <= old(self).budget.capacity as int {
                old(self).accepted.original@.push(node)
            } else {
                old(self).accepted.original@
            },
            final(self).accepted.accumulated@ == if old(self).budget.allocated as int
                    + NODE_COST as int <= old(self).budget.capacity as int {
                old(self).accepted.accumulated@.push(node)
            } else {
                old(self).accepted.accumulated@
            },
            final(self).accepted.pending@ == old(self).accepted.pending@,
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
            (old(self).budget.allocated as int + NODE_COST as int
                    <= old(self).budget.capacity as int
                && node == old(self).root) ==> {
                &&& final(self).queue.values@.len() == old(self).num_nodes - 1
                &&& forall|index: int| 0 <= index < final(self).queue.values@.len() ==>
                    #[trigger] final(self).queue.values@[index]
                        == if index < old(self).root as int {
                            index as usize
                        } else {
                            (index + 1) as usize
                        }
            },
            (!(old(self).budget.allocated as int + NODE_COST as int
                    <= old(self).budget.capacity as int
                && node == old(self).root)) ==> exists|index: int|
                    0 <= index < old(self).queue.values@.len()
                        && old(self).queue.values@[index] == node
                        && final(self).queue.values@
                            == old(self).queue.values@.remove(index),
            final(self).queue.capacity == old(self).queue.capacity,
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
        assert(self.accepted_cost_accounting()) by {
            reveal(TraversalEngine::accepted_cost_accounting);
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
            final(self).graph == old(self).graph,
            final(self).budget == old(self).budget,
            final(self).visited@ == old(self).visited@,
            final(self).accepted == old(self).accepted,
            final(self).queue.capacity == old(self).queue.capacity,
            exists|index: int|
                0 <= index < old(self).queue.values@.len()
                    && old(self).queue.values@[index] == node
                    && final(self).queue.values@
                        == old(self).queue.values@.remove(index),
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
        assert(self.accepted_cost_accounting());
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
