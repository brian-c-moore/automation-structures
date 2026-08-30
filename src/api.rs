//! Checked public entry points for ordinary Rust consumers.
//!
//! Proof-oriented carriers mirror formal actions and use Verus preconditions.
//! These public types keep their carrier invariants internal and convert every
//! caller-controlled action guard into an executable result.

use crate::connectives::cursor::Cursor as CursorCarrier;
use crate::primitives::actuation_pass::ActuationPass as ActuationPassCarrier;
use crate::primitives::audit_sink::AuditSink as AuditSinkCarrier;
use crate::primitives::backtracking_traversal::BacktrackingTraversal as BacktrackingTraversalCarrier;
use crate::primitives::budget::Budget as BudgetCarrier;
use crate::primitives::competitive_selection::{
    CompetitiveSelectionHard as CompetitiveSelectionHardCarrier,
    CompetitiveSelectionHardExclusive as CompetitiveSelectionHardExclusiveCarrier,
    CompetitiveSelectionRanked as CompetitiveSelectionRankedCarrier,
    CompetitiveSelectionSoft as CompetitiveSelectionSoftCarrier,
};
use crate::primitives::convergence_governor_phase_aware::ConvergenceGovernorPhaseAware as ConvergenceGovernorCarrier;
use crate::primitives::propagation_pass::PropagationPass as PropagationPassCarrier;
use crate::primitives::quality_hierarchy::QualityHierarchy as QualityHierarchyCarrier;
use crate::primitives::resource_registry::ResourceRegistry as RegistryCarrier;
use vstd::prelude::*;

pub use crate::primitives::convergence_governor_phase_aware::{
    GovState as ConvergenceState, Phase as ConvergencePhase,
};
pub use crate::primitives::propagation_pass::Round as PropagationRound;

verus! {

/// A disabled budget transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum BudgetError {
    /// The requested amount exceeds the held reservation.
    AmountExceedsReservation,
    /// The requested amount exceeds the committed allocation.
    AmountExceedsAllocation,
    /// The requested amount exceeds the pending eviction amount.
    AmountExceedsPendingEviction,
}

/// A checked budget whose three claims cannot exceed its fixed capacity.
pub struct Budget {
    inner: BudgetCarrier,
}

impl Budget {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.safety_invariant()
    }

    /// Construct an empty budget with `capacity` units.
    pub fn new(capacity: u64) -> (budget: Self) {
        let inner = BudgetCarrier::new(capacity);
        Self { inner }
    }

    /// Return the fixed budget ceiling.
    pub fn capacity(&self) -> u64 {
        self.inner.capacity
    }

    /// Return units committed for use.
    pub fn allocated(&self) -> u64 {
        self.inner.allocated
    }

    /// Return units held but not committed.
    pub fn reserved(&self) -> u64 {
        self.inner.reserved
    }

    /// Return units currently being reclaimed.
    pub fn pending_eviction(&self) -> u64 {
        self.inner.pending_eviction
    }

    /// Return units not claimed by any budget state.
    pub fn available(&self) -> (available: u64) {
        proof { use_type_invariant(&*self); }
        self.inner.available()
    }

    /// Try to commit unused capacity directly.
    #[must_use]
    pub fn try_allocate(&mut self, amount: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = budget_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.try_allocate(amount);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Try to reserve unused capacity.
    #[must_use]
    pub fn try_reserve(&mut self, amount: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = budget_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.reserve(amount);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Move held capacity into committed allocation.
    pub fn commit_reservation(&mut self, amount: u64) -> (result: Result<(), BudgetError>) {
        proof { use_type_invariant(&*self); }
        if amount <= self.inner.reserved {
            let mut carrier = budget_sentinel();
            core::mem::swap(&mut self.inner, &mut carrier);
            carrier.commit_reservation(amount);
            core::mem::swap(&mut self.inner, &mut carrier);
            Ok(())
        } else {
            Err(BudgetError::AmountExceedsReservation)
        }
    }

    /// Release committed allocation.
    pub fn release(&mut self, amount: u64) -> (result: Result<(), BudgetError>) {
        proof { use_type_invariant(&*self); }
        if amount <= self.inner.allocated {
            let mut carrier = budget_sentinel();
            core::mem::swap(&mut self.inner, &mut carrier);
            carrier.release(amount);
            core::mem::swap(&mut self.inner, &mut carrier);
            Ok(())
        } else {
            Err(BudgetError::AmountExceedsAllocation)
        }
    }

    /// Move committed allocation into pending eviction.
    pub fn mark_eviction(&mut self, amount: u64) -> (result: Result<(), BudgetError>) {
        proof { use_type_invariant(&*self); }
        if amount <= self.inner.allocated {
            let mut carrier = budget_sentinel();
            core::mem::swap(&mut self.inner, &mut carrier);
            carrier.mark_eviction(amount);
            core::mem::swap(&mut self.inner, &mut carrier);
            Ok(())
        } else {
            Err(BudgetError::AmountExceedsAllocation)
        }
    }

    /// Finish reclaiming pending eviction.
    pub fn complete_eviction(&mut self, amount: u64) -> (result: Result<(), BudgetError>) {
        proof { use_type_invariant(&*self); }
        if amount <= self.inner.pending_eviction {
            let mut carrier = budget_sentinel();
            core::mem::swap(&mut self.inner, &mut carrier);
            carrier.complete_eviction(amount);
            core::mem::swap(&mut self.inner, &mut carrier);
            Ok(())
        } else {
            Err(BudgetError::AmountExceedsPendingEviction)
        }
    }
}

/// A unique-key resource registry.
pub struct ResourceRegistry {
    inner: RegistryCarrier,
}

impl ResourceRegistry {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.unique_mapping()
    }

    /// Construct an empty registry.
    pub fn new() -> (registry: Self) {
        let inner = RegistryCarrier::new();
        Self { inner }
    }

    /// Number of registered keys.
    pub fn len(&self) -> usize {
        self.inner.entries.len()
    }

    /// Whether no keys are registered.
    pub fn is_empty(&self) -> bool {
        self.inner.entries.is_empty()
    }

    /// Look up a registered value.
    pub fn get(&self, key: u64) -> (value: Option<u64>) {
        proof { use_type_invariant(&*self); }
        self.inner.lookup(key)
    }

    /// Insert or replace a key and return its previous value.
    pub fn insert(&mut self, key: u64, value: u64) -> (previous: Option<u64>) {
        proof { use_type_invariant(&*self); }
        let previous = self.inner.lookup(key);
        let mut carrier = registry_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.register(key, value);
        core::mem::swap(&mut self.inner, &mut carrier);
        previous
    }

    /// Remove a key and return its previous value.
    pub fn remove(&mut self, key: u64) -> (previous: Option<u64>) {
        proof { use_type_invariant(&*self); }
        let previous = self.inner.lookup(key);
        match previous {
            Some(value) => {
                let mut carrier = registry_sentinel();
                core::mem::swap(&mut self.inner, &mut carrier);
                carrier.deregister(key);
                core::mem::swap(&mut self.inner, &mut carrier);
                Some(value)
            },
            None => None,
        }
    }

    /// Read an entry by storage index for deterministic inspection.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the registry index is in bounds")]
    pub fn entry(&self, index: usize) -> Option<(u64, u64)> {
        if index < self.inner.entries.len() {
            Some(self.inner.entries[index])
        } else {
            None
        }
    }
}

/// A public immutable audit record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AuditRecord {
    /// The operation recorded by the sink.
    pub operation: u64,
    /// The predecessor hash stored in this record.
    pub previous_hash: u64,
    /// The record's concrete model hash.
    pub hash: u64,
}

/// A bounded append-only audit chain.
pub struct AuditSink {
    inner: AuditSinkCarrier,
}

impl AuditSink {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv()
    }

    /// Construct an empty sink with a fixed record capacity.
    pub fn new(capacity: usize) -> (sink: Self) {
        let inner = AuditSinkCarrier::new(capacity);
        Self { inner }
    }

    /// Maximum number of retained records.
    pub fn capacity(&self) -> usize {
        self.inner.max_log_len
    }

    /// Number of retained records.
    pub fn len(&self) -> usize {
        self.inner.log.len()
    }

    /// Whether the sink contains no records.
    pub fn is_empty(&self) -> bool {
        self.inner.log.is_empty()
    }

    /// Current chain head.
    pub fn last_hash(&self) -> u64 {
        self.inner.last_hash
    }

    /// Append an operation if capacity remains.
    #[must_use]
    pub fn try_record(&mut self, operation: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = audit_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.record(operation);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Recompute and validate the concrete structural chain.
    pub fn validate(&self) -> (valid: bool) {
        proof { use_type_invariant(&*self); }
        self.inner.validate()
    }

    /// Read an immutable record by index.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the audit index is in bounds")]
    pub fn record(&self, index: usize) -> Option<AuditRecord> {
        if index < self.inner.log.len() {
            let entry = &self.inner.log[index];
            Some(AuditRecord {
                operation: entry.operation,
                previous_hash: entry.prev_hash,
                hash: entry.hash,
            })
        } else {
            None
        }
    }
}

/// A rejected monotone Cursor movement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum CursorError {
    /// The requested position precedes the retained position.
    Regression,
}

/// A checked retained position for consumer progress.
pub struct Cursor {
    inner: CursorCarrier,
}

impl Cursor {
    /// Construct a cursor at `position`.
    pub fn new(position: usize) -> (cursor: Self) {
        Self { inner: CursorCarrier::new(position) }
    }

    /// Read the retained position.
    pub fn position(&self) -> usize {
        self.inner.position
    }

    /// Move monotonically to `position`.
    pub fn advance_to(&mut self, position: usize) -> (result: Result<(), CursorError>) {
        if position < self.inner.position {
            return Err(CursorError::Regression);
        }
        self.inner.advance_to(position);
        Ok(())
    }
}

/// Invalid construction input for a propagation pass.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum PropagationBuildError {
    /// An initial value exceeds the declared value ceiling.
    InitialValueOutOfRange,
    /// An edge endpoint is not a node in the initial value vector.
    EdgeEndpointOutOfRange,
}

/// A disabled propagation transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum PropagationError {
    /// A node index is outside the admitted graph.
    NodeOutOfRange,
    /// A round is already running.
    RoundAlreadyRunning,
    /// The operation requires a running round.
    RoundNotRunning,
    /// The node has already committed its update in this round.
    NodeAlreadyUpdated,
    /// Not every node has committed an update.
    RoundIncomplete,
    /// The pass is settled or has exhausted its iteration ceiling.
    PassTerminated,
    /// The pass is not yet settled and has not reached its ceiling.
    PassStillRunning,
}

/// A snapshot-local bounded propagation pass.
pub struct PropagationPass {
    inner: PropagationPassCarrier,
}

impl PropagationPass {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv()
    }

    /// Validate and construct a pass. The node universe is the initial value length.
    pub fn new(
        max_iterations: u64,
        max_value: u64,
        edges: Vec<(usize, usize)>,
        initial_values: Vec<u64>,
    ) -> (result: Result<Self, PropagationBuildError>) {
        if !values_within_max(&initial_values, max_value) {
            return Err(PropagationBuildError::InitialValueOutOfRange);
        }
        let num_nodes = initial_values.len();
        if !edges_within_nodes(&edges, num_nodes) {
            return Err(PropagationBuildError::EdgeEndpointOutOfRange);
        }
        let inner = PropagationPassCarrier::new(
            num_nodes,
            max_iterations,
            max_value,
            edges,
            initial_values,
        );
        Ok(Self { inner })
    }

    /// Number of admitted nodes.
    pub fn num_nodes(&self) -> usize {
        self.inner.num_nodes
    }

    /// Maximum charged rounds.
    pub fn max_iterations(&self) -> u64 {
        self.inner.max_iterations
    }

    /// Largest admitted node value.
    pub fn max_value(&self) -> u64 {
        self.inner.max_value
    }

    /// Number of completed rounds.
    pub fn iteration(&self) -> u64 {
        self.inner.iteration
    }

    /// Current round phase.
    pub fn round(&self) -> PropagationRound {
        self.inner.round
    }

    /// Whether the previous completed round changed a value.
    pub fn changed(&self) -> bool {
        self.inner.changed
    }

    /// Read a current node value.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the node index is in bounds")]
    pub fn value(&self, node: usize) -> Option<u64> {
        if node < self.inner.values.len() {
            Some(self.inner.values[node])
        } else {
            None
        }
    }

    /// Read the round-start value for a node.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the snapshot index is in bounds")]
    pub fn snapshot_value(&self, node: usize) -> Option<u64> {
        if node < self.inner.snapshot.len() {
            Some(self.inner.snapshot[node])
        } else {
            None
        }
    }

    /// Whether a node has committed its update in the current round.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the update index is in bounds")]
    pub fn node_updated(&self, node: usize) -> Option<bool> {
        if node < self.inner.updated.len() {
            Some(self.inner.updated[node])
        } else {
            None
        }
    }

    /// Begin a new snapshot round.
    pub fn start_round(&mut self) -> (result: Result<(), PropagationError>) {
        proof { use_type_invariant(&*self); }
        match self.inner.round {
            PropagationRound::Running => {
                return Err(PropagationError::RoundAlreadyRunning);
            },
            PropagationRound::Idle => {},
        }
        if !self.inner.changed || self.inner.iteration >= self.inner.max_iterations {
            return Err(PropagationError::PassTerminated);
        }
        let mut carrier = propagation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.start_round();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Commit one node's snapshot-local update.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the update index is in bounds")]
    pub fn update_node(&mut self, node: usize) -> (result: Result<(), PropagationError>) {
        proof { use_type_invariant(&*self); }
        match self.inner.round {
            PropagationRound::Idle => {
                return Err(PropagationError::RoundNotRunning);
            },
            PropagationRound::Running => {},
        }
        if node >= self.inner.num_nodes {
            return Err(PropagationError::NodeOutOfRange);
        }
        if self.inner.updated[node] {
            return Err(PropagationError::NodeAlreadyUpdated);
        }
        let mut carrier = propagation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.update_node(node);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Finish a fully updated round and charge one iteration.
    pub fn end_round(&mut self) -> (result: Result<(), PropagationError>) {
        proof { use_type_invariant(&*self); }
        match self.inner.round {
            PropagationRound::Idle => {
                return Err(PropagationError::RoundNotRunning);
            },
            PropagationRound::Running => {},
        }
        if !self.inner.all_nodes_updated() {
            return Err(PropagationError::RoundIncomplete);
        }
        let mut carrier = propagation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.end_round();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Confirm the terminal self-loop at settlement or the iteration ceiling.
    pub fn terminate(&mut self) -> (result: Result<(), PropagationError>) {
        proof { use_type_invariant(&*self); }
        match self.inner.round {
            PropagationRound::Running => {
                return Err(PropagationError::RoundAlreadyRunning);
            },
            PropagationRound::Idle => {},
        }
        if self.inner.changed && self.inner.iteration != self.inner.max_iterations {
            return Err(PropagationError::PassStillRunning);
        }
        let mut carrier = propagation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.terminate();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// A disabled actuation transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ActuationError {
    /// A seat index is outside the admitted seat universe.
    SeatOutOfRange,
    /// The pass has already committed closure.
    PassComplete,
    /// The seat already holds a resource.
    SeatAlreadyAllocated,
    /// The seat holds no resource.
    SeatUnallocated,
    /// The seat has already committed its effect.
    SeatAlreadyActuated,
    /// At least one allocated seat has not committed its effect.
    PassIncomplete,
}

/// A governed resource actuation pass.
pub struct ActuationPass {
    inner: ActuationPassCarrier,
}

impl ActuationPass {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.invariant()
    }

    /// Construct a pass over the supplied allocation record.
    pub fn new(allocation: Vec<Option<u64>>) -> (pass: Self) {
        let num_seats = allocation.len();
        let inner = ActuationPassCarrier::new(allocation, num_seats);
        Self { inner }
    }

    /// Number of governed seats.
    pub fn len(&self) -> usize {
        self.inner.num_seats
    }

    /// Whether the pass has no seats.
    pub fn is_empty(&self) -> bool {
        self.inner.num_seats == 0
    }

    /// Whether closure has committed.
    pub fn is_complete(&self) -> bool {
        self.inner.complete
    }

    /// Read the current resource held by a seat.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the allocation index is in bounds")]
    pub fn allocation(&self, seat: usize) -> Option<Option<u64>> {
        if seat < self.inner.allocation.len() {
            Some(self.inner.allocation[seat])
        } else {
            None
        }
    }

    /// Read the resource whose effect has committed for a seat.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the effect index is in bounds")]
    pub fn effect(&self, seat: usize) -> Option<Option<u64>> {
        if seat < self.inner.effects.len() {
            Some(self.inner.effects[seat])
        } else {
            None
        }
    }

    /// Assign an unallocated seat.
    pub fn allocate(&mut self, seat: usize, resource: u64) -> (result: Result<(), ActuationError>) {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats {
            return Err(ActuationError::SeatOutOfRange);
        }
        if self.inner.complete {
            return Err(ActuationError::PassComplete);
        }
        if !self.inner.can_allocate(seat) {
            return Err(ActuationError::SeatAlreadyAllocated);
        }
        let mut carrier = actuation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.allocate(seat, resource);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Withdraw a seat that has not committed an effect.
    pub fn deallocate(&mut self, seat: usize) -> (result: Result<(), ActuationError>) {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats {
            return Err(ActuationError::SeatOutOfRange);
        }
        if self.inner.complete {
            return Err(ActuationError::PassComplete);
        }
        if !self.inner.is_allocated(seat) {
            return Err(ActuationError::SeatUnallocated);
        }
        if !self.inner.can_deallocate(seat) {
            return Err(ActuationError::SeatAlreadyActuated);
        }
        let mut carrier = actuation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.deallocate(seat);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Commit the effect for an allocated seat.
    pub fn actuate(&mut self, seat: usize) -> (result: Result<(), ActuationError>) {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats {
            return Err(ActuationError::SeatOutOfRange);
        }
        if self.inner.complete {
            return Err(ActuationError::PassComplete);
        }
        if !self.inner.is_allocated(seat) {
            return Err(ActuationError::SeatUnallocated);
        }
        if !self.inner.can_actuate(seat) {
            return Err(ActuationError::SeatAlreadyActuated);
        }
        let mut carrier = actuation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.actuate(seat);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Whether every allocated seat has committed an effect.
    pub fn ready_to_finish(&self) -> (ready: bool) {
        proof { use_type_invariant(&*self); }
        self.inner.ready_to_finish_exec()
    }

    /// Commit closure after every allocated seat has committed an effect.
    pub fn finish(&mut self) -> (result: Result<(), ActuationError>) {
        proof { use_type_invariant(&*self); }
        if self.inner.complete {
            return Err(ActuationError::PassComplete);
        }
        if !self.inner.ready_to_finish_exec() {
            return Err(ActuationError::PassIncomplete);
        }
        let mut carrier = actuation_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.finish();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// A disabled quality-hierarchy transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum QualityHierarchyError {
    /// A node index is outside the admitted node set.
    NodeOutOfRange,
    /// A proposed parent index is outside the admitted node set.
    ParentOutOfRange,
    /// A proposed child index is outside the admitted node set.
    ChildOutOfRange,
    /// A proposed level exceeds the hierarchy ceiling.
    LevelOutOfRange,
    /// A proposed cost exceeds the hierarchy ceiling.
    CostOutOfRange,
    /// Node-property updates require an isolated node.
    NodeNotIsolated,
    /// A node cannot be its own child.
    SelfEdge,
    /// The exact parent-child edge already exists.
    EdgeAlreadyExists,
    /// The proposed child already has a parent.
    ChildAlreadyParented,
    /// Parent level must strictly exceed child level.
    LevelOrderViolation,
    /// Parent cost must not exceed child cost.
    CostOrderViolation,
}

/// A checked refinement forest over levels, costs, parents, and child edges.
pub struct QualityHierarchy {
    inner: QualityHierarchyCarrier,
}

impl QualityHierarchy {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.type_invariant()
            && self.inner.strict_level_descent()
            && self.inner.parent_edge_agreement()
            && self.inner.cost_monotonicity()
    }

    /// Construct a discrete hierarchy with no parent-child edges.
    pub fn new(num_nodes: usize, max_level: u64) -> (hierarchy: Self) {
        let inner = QualityHierarchyCarrier::new(num_nodes, max_level);
        Self { inner }
    }

    /// Number of admitted nodes.
    pub fn len(&self) -> usize {
        self.inner.num_nodes
    }

    /// Whether the hierarchy has no nodes.
    pub fn is_empty(&self) -> bool {
        self.inner.num_nodes == 0
    }

    /// Maximum admitted level and cost value.
    pub fn max_level(&self) -> u64 {
        self.inner.max_level
    }

    /// Read one node level.
    pub fn level(&self, node: usize) -> Option<u64> {
        proof { use_type_invariant(&*self); }
        if node < self.inner.num_nodes {
            Some(self.inner.level_of(node))
        } else {
            None
        }
    }

    /// Read one node cost.
    pub fn cost(&self, node: usize) -> Option<u64> {
        proof { use_type_invariant(&*self); }
        if node < self.inner.num_nodes {
            Some(self.inner.cost_of(node))
        } else {
            None
        }
    }

    /// Read one parent, returning `None` for a root or an invalid node.
    pub fn parent(&self, node: usize) -> Option<usize> {
        proof { use_type_invariant(&*self); }
        if node >= self.inner.num_nodes {
            return None;
        }
        let parent = self.inner.parent_of(node);
        if parent == self.inner.num_nodes {
            None
        } else {
            Some(parent)
        }
    }

    /// Number of retained parent-child edges.
    pub fn edge_count(&self) -> usize {
        self.inner.edges.len()
    }

    /// Read one parent-child edge by deterministic carrier order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the hierarchy edge index is in bounds")]
    pub fn edge(&self, index: usize) -> Option<(usize, usize)> {
        if index < self.inner.edges.len() {
            Some(self.inner.edges[index])
        } else {
            None
        }
    }

    /// Set the level and cost of an isolated node.
    pub fn set_node_properties(
        &mut self,
        node: usize,
        level: u64,
        cost: u64,
    ) -> (result: Result<(), QualityHierarchyError>) {
        proof { use_type_invariant(&*self); }
        if node >= self.inner.num_nodes {
            return Err(QualityHierarchyError::NodeOutOfRange);
        }
        if level > self.inner.max_level {
            return Err(QualityHierarchyError::LevelOutOfRange);
        }
        if cost > self.inner.max_level {
            return Err(QualityHierarchyError::CostOutOfRange);
        }
        if !self.inner.can_set_node_properties(node, level, cost) {
            return Err(QualityHierarchyError::NodeNotIsolated);
        }
        let mut carrier = quality_hierarchy_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.set_node_properties(node, level, cost);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Add one admitted parent-child relation.
    pub fn add_child(
        &mut self,
        parent: usize,
        child: usize,
    ) -> (result: Result<(), QualityHierarchyError>) {
        proof { use_type_invariant(&*self); }
        if parent >= self.inner.num_nodes {
            return Err(QualityHierarchyError::ParentOutOfRange);
        }
        if child >= self.inner.num_nodes {
            return Err(QualityHierarchyError::ChildOutOfRange);
        }
        if self.inner.can_add_child(parent, child) {
            let mut carrier = quality_hierarchy_sentinel();
            core::mem::swap(&mut self.inner, &mut carrier);
            carrier.add_child(parent, child);
            core::mem::swap(&mut self.inner, &mut carrier);
            return Ok(());
        }
        if parent == child {
            Err(QualityHierarchyError::SelfEdge)
        } else if self.inner.has_edge(parent, child) {
            Err(QualityHierarchyError::EdgeAlreadyExists)
        } else if self.inner.parent_of(child) != self.inner.num_nodes {
            Err(QualityHierarchyError::ChildAlreadyParented)
        } else if self.inner.level_of(parent) <= self.inner.level_of(child) {
            Err(QualityHierarchyError::LevelOrderViolation)
        } else {
            Err(QualityHierarchyError::CostOrderViolation)
        }
    }
}

/// Invalid BacktrackingTraversal construction input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum BacktrackingBuildError {
    /// The initial auxiliary value must be in the canonical modulo-three domain.
    InitialAuxOutOfRange,
}

/// A disabled BacktrackingTraversal transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum BacktrackingError {
    /// Descent is disabled at a full-depth leaf.
    AtLeaf,
    /// The branch choice is outside the admitted branch set.
    ChoiceOutOfRange,
    /// The mutation delta is outside the canonical inverse-pair domain.
    DeltaOutOfRange,
    /// Visit requires a full-depth leaf.
    NotLeaf,
    /// The current leaf was already recorded.
    AlreadyVisited,
    /// Ascent is disabled at the root.
    AtRoot,
}

/// A checked paired do-undo backtracking traversal.
pub struct BacktrackingTraversal {
    inner: BacktrackingTraversalCarrier,
}

impl BacktrackingTraversal {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv()
    }

    /// Validate and construct an empty traversal.
    pub fn new(
        branch_factor: u64,
        max_depth: usize,
        initial_aux: u64,
    ) -> (result: Result<Self, BacktrackingBuildError>) {
        if initial_aux >= 3 {
            return Err(BacktrackingBuildError::InitialAuxOutOfRange);
        }
        let inner = BacktrackingTraversalCarrier::new(branch_factor, max_depth, initial_aux);
        Ok(Self { inner })
    }

    /// Maximum admitted traversal depth.
    pub fn max_depth(&self) -> usize {
        self.inner.max_depth
    }

    /// Current path depth.
    pub fn depth(&self) -> usize {
        self.inner.path.len()
    }

    /// Current auxiliary state.
    pub fn auxiliary(&self) -> u64 {
        self.inner.aux
    }

    /// Number of recorded leaves.
    pub fn visited_count(&self) -> usize {
        self.inner.visited.len()
    }

    /// Whether the current path is a full-depth leaf.
    pub fn is_leaf(&self) -> bool {
        self.inner.is_leaf_exec()
    }

    /// Read one current branch choice.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the path index is in bounds")]
    pub fn choice(&self, depth: usize) -> Option<u64> {
        if depth < self.inner.path.len() {
            Some(self.inner.path[depth])
        } else {
            None
        }
    }

    /// Descend one level and record the paired undo token.
    pub fn descend(&mut self, choice: u64, delta: u64) -> (result: Result<(), BacktrackingError>) {
        proof { use_type_invariant(&*self); }
        if self.inner.is_leaf_exec() {
            return Err(BacktrackingError::AtLeaf);
        }
        if choice < 1 || choice > self.inner.branch_factor {
            return Err(BacktrackingError::ChoiceOutOfRange);
        }
        if delta < 1 || delta > 2 {
            return Err(BacktrackingError::DeltaOutOfRange);
        }
        let mut carrier = backtracking_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.descend(choice, delta);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Record the current leaf when it has not been visited.
    pub fn visit(&mut self) -> (result: Result<(), BacktrackingError>) {
        proof { use_type_invariant(&*self); }
        if !self.inner.is_leaf_exec() {
            return Err(BacktrackingError::NotLeaf);
        }
        if !self.inner.can_visit() {
            return Err(BacktrackingError::AlreadyVisited);
        }
        let mut carrier = backtracking_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.visit();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Ascend one level and restore the paired auxiliary state.
    pub fn ascend(&mut self) -> (result: Result<(), BacktrackingError>) {
        proof { use_type_invariant(&*self); }
        if !self.inner.can_ascend() {
            return Err(BacktrackingError::AtRoot);
        }
        let mut carrier = backtracking_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.ascend();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// Invalid competitive-selection configuration or input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum CompetitiveSelectionError {
    /// At least one candidate is required by this selection mode.
    NoCandidates,
    /// A candidate index is outside the admitted candidate set.
    CandidateOutOfRange,
    /// A seat index is outside the admitted seat set.
    SeatOutOfRange,
    /// The selected seat already holds an allocation.
    SeatAlreadyAllocated,
    /// Every candidate is currently allocated to another seat.
    NoCandidateAvailable,
    /// A score is outside the admitted score domain.
    ScoreOutOfRange,
    /// A score replacement has a different candidate count.
    ScoreCountMismatch,
    /// The weight total is smaller than the reserved unit per candidate.
    WeightTotalBelowReservedFloor,
    /// The weight total exceeds the verified arithmetic ceiling.
    WeightTotalOutOfRange,
    /// The declared maximum score exceeds the verified arithmetic ceiling.
    MaxScoreOutOfRange,
    /// Every available soft-selection unit has already been assigned.
    AllocationComplete,
}

/// Lowest-index argmax selection for one set of candidate scores.
pub struct CompetitiveSelectionHard {
    inner: CompetitiveSelectionHardCarrier,
}

impl CompetitiveSelectionHard {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv() && self.inner.scores.len() >= 1
    }

    /// Construct a selection over `num_candidates` initially zero-valued scores.
    pub fn new(num_candidates: usize) -> (result: Result<Self, CompetitiveSelectionError>) {
        if num_candidates == 0 {
            return Err(CompetitiveSelectionError::NoCandidates);
        }
        let inner = CompetitiveSelectionHardCarrier::new(num_candidates);
        Ok(Self { inner })
    }

    /// Number of admitted candidates.
    pub fn len(&self) -> usize {
        self.inner.scores.len()
    }

    /// Whether no candidates are admitted. Checked construction makes this always false.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Read one candidate score.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the candidate index is in bounds")]
    pub fn score(&self, candidate: usize) -> Option<u64> {
        if candidate < self.inner.scores.len() {
            Some(self.inner.scores[candidate])
        } else {
            None
        }
    }

    /// Read the current winner, if the scores have been evaluated.
    pub fn winner(&self) -> Option<usize> {
        self.inner.allocation
    }

    /// Replace one candidate score and invalidate the previous winner.
    pub fn update_score(
        &mut self,
        candidate: usize,
        score: u64,
    ) -> (result: Result<(), CompetitiveSelectionError>) {
        proof { use_type_invariant(&*self); }
        if candidate >= self.inner.scores.len() {
            return Err(CompetitiveSelectionError::CandidateOutOfRange);
        }
        let mut carrier = hard_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.update_score(candidate, score);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Select the lowest-index candidate among those with the maximum score.
    #[expect(clippy::manual_unwrap_or_default, reason = "the explicit match is supported by the Verus boundary")]
    pub fn evaluate(&mut self) -> (winner: usize) {
        proof { use_type_invariant(&*self); }
        let mut carrier = hard_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.evaluate();
        let winner = match carrier.allocation {
            Some(value) => value,
            None => 0,
        };
        core::mem::swap(&mut self.inner, &mut carrier);
        winner
    }
}

/// Lowest-index argmax selection across seats with exclusive candidates.
pub struct CompetitiveSelectionHardExclusive {
    inner: CompetitiveSelectionHardExclusiveCarrier,
}

impl CompetitiveSelectionHardExclusive {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv()
    }

    /// Construct `num_seats` empty allocations over a nonempty candidate set.
    pub fn new(
        num_seats: usize,
        num_candidates: usize,
        max_score: u64,
    ) -> (result: Result<Self, CompetitiveSelectionError>) {
        if num_candidates == 0 {
            return Err(CompetitiveSelectionError::NoCandidates);
        }
        let inner = CompetitiveSelectionHardExclusiveCarrier::new(
            num_seats,
            num_candidates,
            max_score,
        );
        Ok(Self { inner })
    }

    /// Number of allocation seats.
    pub fn seat_count(&self) -> usize {
        self.inner.num_seats
    }

    /// Number of candidates.
    pub fn candidate_count(&self) -> usize {
        self.inner.num_candidates
    }

    /// Maximum admitted score.
    pub fn max_score(&self) -> u64 {
        self.inner.max_score
    }

    /// Read one seat allocation, or `None` when the seat is invalid or unallocated.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the seat index is in bounds")]
    #[expect(clippy::manual_map, reason = "the explicit match is supported by the Verus boundary")]
    pub fn allocation(&self, seat: usize) -> Option<usize> {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats {
            return None;
        }
        match self.inner.allocation[seat] {
            Some(candidate) => Some(candidate as usize),
            None => None,
        }
    }

    /// Read one seat-candidate score.
    #[expect(clippy::indexing_slicing, reason = "the branches prove both score indices are in bounds")]
    pub fn score(&self, seat: usize, candidate: usize) -> Option<u64> {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats || candidate >= self.inner.num_candidates {
            None
        } else {
            Some(self.inner.scores[seat][candidate])
        }
    }

    /// Whether a candidate is free for one seat.
    pub fn candidate_available(&self, seat: usize, candidate: usize) -> Option<bool> {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats || candidate >= self.inner.num_candidates {
            return None;
        }
        Some(self.inner.candidate_available(seat, candidate))
    }

    /// Replace one score and invalidate every coupled seat allocation.
    pub fn update_score(
        &mut self,
        seat: usize,
        candidate: usize,
        score: u64,
    ) -> (result: Result<(), CompetitiveSelectionError>) {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats {
            return Err(CompetitiveSelectionError::SeatOutOfRange);
        }
        if candidate >= self.inner.num_candidates {
            return Err(CompetitiveSelectionError::CandidateOutOfRange);
        }
        if score > self.inner.max_score {
            return Err(CompetitiveSelectionError::ScoreOutOfRange);
        }
        let mut carrier = hard_exclusive_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.update_score(seat, candidate, score);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Select the lowest-index available argmax for one empty seat.
    #[expect(clippy::indexing_slicing, reason = "the guards prove the seat index is in bounds")]
    pub fn evaluate(
        &mut self,
        seat: usize,
    ) -> (result: Result<usize, CompetitiveSelectionError>) {
        proof { use_type_invariant(&*self); }
        if seat >= self.inner.num_seats {
            return Err(CompetitiveSelectionError::SeatOutOfRange);
        }
        if self.inner.allocation[seat].is_some() {
            return Err(CompetitiveSelectionError::SeatAlreadyAllocated);
        }
        if !self.inner.has_available(seat) {
            return Err(CompetitiveSelectionError::NoCandidateAvailable);
        }
        let mut carrier = hard_exclusive_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.evaluate(seat);
        let winner = match carrier.allocation[seat] {
            Some(candidate) => candidate as usize,
            None => 0,
        };
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(winner)
    }
}

/// Reserved-floor sequential Webster apportionment over mutable scores.
pub struct CompetitiveSelectionSoft {
    inner: CompetitiveSelectionSoftCarrier,
}

impl CompetitiveSelectionSoft {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.mutable_score_inv()
    }

    /// Construct a complete apportionment for `weight_total` units.
    pub fn new(
        scores: Vec<u64>,
        weight_total: u64,
        max_score: u64,
    ) -> (result: Result<Self, CompetitiveSelectionError>) {
        if scores.is_empty() {
            return Err(CompetitiveSelectionError::NoCandidates);
        }
        if weight_total > 1_000_000_000 {
            return Err(CompetitiveSelectionError::WeightTotalOutOfRange);
        }
        if max_score > 1_000_000_000 {
            return Err(CompetitiveSelectionError::MaxScoreOutOfRange);
        }
        if weight_total < scores.len() as u64 {
            return Err(CompetitiveSelectionError::WeightTotalBelowReservedFloor);
        }
        if !positive_values_within_max(&scores, max_score) {
            return Err(CompetitiveSelectionError::ScoreOutOfRange);
        }
        let inner = CompetitiveSelectionSoftCarrier::new(scores, weight_total, max_score);
        Ok(Self { inner })
    }

    /// Construct only the reserved floor so awards can be assigned incrementally.
    pub fn begin(
        scores: Vec<u64>,
        weight_total: u64,
        max_score: u64,
    ) -> (result: Result<Self, CompetitiveSelectionError>) {
        if scores.is_empty() {
            return Err(CompetitiveSelectionError::NoCandidates);
        }
        if weight_total > 1_000_000_000 {
            return Err(CompetitiveSelectionError::WeightTotalOutOfRange);
        }
        if max_score > 1_000_000_000 {
            return Err(CompetitiveSelectionError::MaxScoreOutOfRange);
        }
        if weight_total < scores.len() as u64 {
            return Err(CompetitiveSelectionError::WeightTotalBelowReservedFloor);
        }
        if !positive_values_within_max(&scores, max_score) {
            return Err(CompetitiveSelectionError::ScoreOutOfRange);
        }
        let inner = CompetitiveSelectionSoftCarrier::init(scores, weight_total, max_score);
        Ok(Self { inner })
    }

    /// Number of candidates.
    pub fn len(&self) -> usize {
        self.inner.scores.len()
    }

    /// Whether no candidates are admitted. Checked construction makes this always false.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Total weight to apportion.
    pub fn weight_total(&self) -> u64 {
        self.inner.weight_total
    }

    /// Maximum admitted score.
    pub fn max_score(&self) -> u64 {
        self.inner.max_score
    }

    /// Read one candidate score.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the candidate index is in bounds")]
    pub fn score(&self, candidate: usize) -> Option<u64> {
        if candidate < self.inner.scores.len() {
            Some(self.inner.scores[candidate])
        } else {
            None
        }
    }

    /// Read one candidate's current derived weight.
    pub fn weight(&self, candidate: usize) -> Option<u64> {
        proof { use_type_invariant(&*self); }
        if candidate < self.inner.extra.len() {
            Some(self.inner.weight_at(candidate))
        } else {
            None
        }
    }

    /// Number of units assigned so far.
    pub fn assigned_weight(&self) -> u64 {
        proof { use_type_invariant(&*self); }
        self.inner.assigned_weight()
    }

    /// Whether every unit has been assigned.
    pub fn is_complete(&self) -> bool {
        self.assigned_weight() == self.inner.weight_total
    }

    /// Award the next available unit to the current lowest-index priority winner.
    pub fn assign_next(&mut self) -> (result: Result<usize, CompetitiveSelectionError>) {
        proof { use_type_invariant(&*self); }
        if self.inner.assigned_weight() >= self.inner.weight_total {
            return Err(CompetitiveSelectionError::AllocationComplete);
        }
        let mut carrier = soft_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let winner = carrier.assign_next();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(winner)
    }

    /// Replace one score and reset every candidate to its reserved unit.
    pub fn update_score(
        &mut self,
        candidate: usize,
        score: u64,
    ) -> (result: Result<(), CompetitiveSelectionError>) {
        proof { use_type_invariant(&*self); }
        if candidate >= self.inner.scores.len() {
            return Err(CompetitiveSelectionError::CandidateOutOfRange);
        }
        if score < 1 || score > self.inner.max_score {
            return Err(CompetitiveSelectionError::ScoreOutOfRange);
        }
        let mut carrier = soft_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.update_score(candidate, score);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// Stable top-k selection by descending score and ascending candidate index.
pub struct CompetitiveSelectionRanked {
    inner: CompetitiveSelectionRankedCarrier,
}

impl CompetitiveSelectionRanked {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv()
    }

    /// Construct an empty selection over the supplied scores.
    pub fn new(
        scores: Vec<u64>,
        k: usize,
        max_score: u64,
    ) -> (result: Result<Self, CompetitiveSelectionError>) {
        if !values_within_max(&scores, max_score) {
            return Err(CompetitiveSelectionError::ScoreOutOfRange);
        }
        let inner = CompetitiveSelectionRankedCarrier::new(scores, k, max_score);
        Ok(Self { inner })
    }

    /// Number of candidates.
    pub fn len(&self) -> usize {
        self.inner.scores.len()
    }

    /// Whether the ranked candidate set is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.scores.is_empty()
    }

    /// Requested maximum number of selected candidates.
    pub fn limit(&self) -> usize {
        self.inner.k
    }

    /// Maximum admitted score.
    pub fn max_score(&self) -> u64 {
        self.inner.max_score
    }

    /// Read one candidate score.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the candidate index is in bounds")]
    pub fn score(&self, candidate: usize) -> Option<u64> {
        if candidate < self.inner.scores.len() {
            Some(self.inner.scores[candidate])
        } else {
            None
        }
    }

    /// Whether one candidate is currently selected.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the candidate index is in bounds")]
    pub fn is_selected(&self, candidate: usize) -> Option<bool> {
        if candidate < self.inner.selected.len() {
            Some(self.inner.selected[candidate])
        } else {
            None
        }
    }

    /// Recompute the stable top-k selection.
    pub fn select(&mut self) {
        proof { use_type_invariant(&*self); }
        let mut carrier = ranked_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.select();
        core::mem::swap(&mut self.inner, &mut carrier);
    }

    /// Replace all scores and clear the current selection.
    pub fn update_scores(
        &mut self,
        scores: Vec<u64>,
    ) -> (result: Result<(), CompetitiveSelectionError>) {
        proof { use_type_invariant(&*self); }
        if scores.len() != self.inner.scores.len() {
            return Err(CompetitiveSelectionError::ScoreCountMismatch);
        }
        if !values_within_max(&scores, self.inner.max_score) {
            return Err(CompetitiveSelectionError::ScoreOutOfRange);
        }
        let mut carrier = ranked_selection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.update_scores(scores);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// Invalid convergence-governor construction input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ConvergenceBuildError {
    /// Doubling the convergence threshold would overflow the carrier arithmetic.
    ThresholdOutOfRange,
    /// A moving-average window must retain at least one delta.
    EmptyWindow,
    /// The largest admitted window sum would overflow `u64`.
    WindowSumOutOfRange,
}

/// A disabled convergence-governor transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ConvergenceError {
    /// The submitted delta exceeds the configured maximum.
    DeltaOutOfRange,
}

/// A moving-window convergence state machine with peak-aware phases.
pub struct ConvergenceGovernor {
    inner: ConvergenceGovernorCarrier,
}

impl ConvergenceGovernor {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.inv()
    }

    /// Validate arithmetic bounds and construct an active governor.
    pub fn new(
        threshold: u64,
        awaken_threshold: u64,
        window: usize,
        max_delta: u64,
    ) -> (result: Result<Self, ConvergenceBuildError>) {
        if threshold > u64::MAX / 2 {
            return Err(ConvergenceBuildError::ThresholdOutOfRange);
        }
        if window == 0 {
            return Err(ConvergenceBuildError::EmptyWindow);
        }
        if window > 1_000_000_000 || max_delta > 1_000_000_000 {
            return Err(ConvergenceBuildError::WindowSumOutOfRange);
        }
        proof {
            assert(window as int * max_delta as int <= u64::MAX as int) by (nonlinear_arith)
                requires
                    window <= 1_000_000_000,
                    max_delta <= 1_000_000_000,
                    u64::MAX >= 1_000_000_000 * 1_000_000_000;
        }
        let inner = ConvergenceGovernorCarrier::new(
            threshold,
            awaken_threshold,
            window,
            max_delta,
        );
        Ok(Self { inner })
    }

    /// Convergence threshold used by the state transition.
    pub fn threshold(&self) -> u64 {
        self.inner.threshold
    }

    /// Activity threshold that awakens a converged governor.
    pub fn awaken_threshold(&self) -> u64 {
        self.inner.awaken_threshold
    }

    /// Maximum retained history length.
    pub fn window(&self) -> usize {
        self.inner.window
    }

    /// Maximum admitted delta.
    pub fn max_delta(&self) -> u64 {
        self.inner.max_delta
    }

    /// Current convergence state.
    pub fn state(&self) -> ConvergenceState {
        self.inner.state
    }

    /// Current peak-aware gradient phase.
    pub fn phase(&self) -> ConvergencePhase {
        self.inner.gradient_phase
    }

    /// Whether a threshold event has ever been observed.
    pub fn peak_observed(&self) -> bool {
        self.inner.peak_observed
    }

    /// Number of retained deltas.
    pub fn history_len(&self) -> usize {
        self.inner.delta_history.len()
    }

    /// Read one retained delta from oldest to newest.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the history index is in bounds")]
    pub fn history(&self, index: usize) -> Option<u64> {
        if index < self.inner.delta_history.len() {
            Some(self.inner.delta_history[index])
        } else {
            None
        }
    }

    /// Submit one delta, returning the resulting moving-window average.
    pub fn update(&mut self, delta: u64) -> (result: Result<u64, ConvergenceError>) {
        proof { use_type_invariant(&*self); }
        if delta > self.inner.max_delta {
            return Err(ConvergenceError::DeltaOutOfRange);
        }
        let mut carrier = convergence_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let average = carrier.update(delta);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(average)
    }
}

fn budget_sentinel() -> (carrier: BudgetCarrier)
    ensures carrier.safety_invariant(),
{
    BudgetCarrier::new(0)
}

fn registry_sentinel() -> (carrier: RegistryCarrier)
    ensures carrier.unique_mapping(),
{
    RegistryCarrier::new()
}

fn audit_sentinel() -> (carrier: AuditSinkCarrier)
    ensures carrier.inv(),
{
    AuditSinkCarrier::new(0)
}

fn propagation_sentinel() -> (carrier: PropagationPassCarrier)
    ensures carrier.inv(),
{
    let edges: Vec<(usize, usize)> = Vec::new();
    let values: Vec<u64> = Vec::new();
    PropagationPassCarrier::new(0, 0, 0, edges, values)
}

fn actuation_sentinel() -> (carrier: ActuationPassCarrier)
    ensures carrier.invariant(),
{
    let allocation: Vec<Option<u64>> = Vec::new();
    ActuationPassCarrier::new(allocation, 0)
}

fn quality_hierarchy_sentinel() -> (carrier: QualityHierarchyCarrier)
    ensures
        carrier.type_invariant(),
        carrier.strict_level_descent(),
        carrier.parent_edge_agreement(),
        carrier.cost_monotonicity(),
{
    QualityHierarchyCarrier::new(0, 0)
}

fn backtracking_sentinel() -> (carrier: BacktrackingTraversalCarrier)
    ensures carrier.inv(),
{
    BacktrackingTraversalCarrier::new(0, 0, 0)
}

fn hard_selection_sentinel() -> (carrier: CompetitiveSelectionHardCarrier)
    ensures
        carrier.inv(),
        carrier.scores.len() >= 1,
{
    CompetitiveSelectionHardCarrier::new(1)
}

fn hard_exclusive_selection_sentinel() -> (carrier: CompetitiveSelectionHardExclusiveCarrier)
    ensures carrier.inv(),
{
    CompetitiveSelectionHardExclusiveCarrier::new(0, 1, 0)
}

fn soft_selection_sentinel() -> (carrier: CompetitiveSelectionSoftCarrier)
    ensures carrier.mutable_score_inv(),
{
    let mut scores: Vec<u64> = Vec::new();
    scores.push(1);
    CompetitiveSelectionSoftCarrier::init(scores, 1, 1)
}

fn ranked_selection_sentinel() -> (carrier: CompetitiveSelectionRankedCarrier)
    ensures carrier.inv(),
{
    let scores: Vec<u64> = Vec::new();
    CompetitiveSelectionRankedCarrier::new(scores, 0, 0)
}

fn convergence_sentinel() -> (carrier: ConvergenceGovernorCarrier)
    ensures carrier.inv(),
{
    ConvergenceGovernorCarrier::new(0, 0, 1, 0)
}

#[expect(clippy::indexing_slicing, reason = "the loop proves the value index is in bounds")]
#[expect(clippy::arithmetic_side_effects, reason = "the loop proves the cursor remains within the vector")]
#[expect(clippy::ptr_arg, reason = "Verus sequence-view contracts are stated over Vec in this checked boundary")]
pub(crate) fn values_within_max(values: &Vec<u64>, max_value: u64) -> (valid: bool)
    ensures
        valid == (forall|i: int| 0 <= i < values.len() ==> values@[i] <= max_value),
{
    let mut index: usize = 0;
    while index < values.len()
        invariant
            index <= values.len(),
            forall|i: int| 0 <= i < index ==> values@[i] <= max_value,
        decreases values.len() - index,
    {
        if values[index] > max_value {
            assert(!(forall|i: int| 0 <= i < values.len() ==> values@[i] <= max_value));
            return false;
        }
        index += 1;
    }
    true
}

#[expect(clippy::indexing_slicing, reason = "the loop proves the value index is in bounds")]
#[expect(clippy::arithmetic_side_effects, reason = "the loop proves the cursor remains within the vector")]
#[expect(clippy::ptr_arg, reason = "Verus sequence-view contracts are stated over Vec in this checked boundary")]
fn positive_values_within_max(values: &Vec<u64>, max_value: u64) -> (valid: bool)
    ensures
        valid == (forall|i: int| 0 <= i < values.len()
            ==> 1 <= #[trigger] values@[i] <= max_value),
{
    let mut index: usize = 0;
    while index < values.len()
        invariant
            index <= values.len(),
            forall|i: int| 0 <= i < index ==> 1 <= #[trigger] values@[i] <= max_value,
        decreases values.len() - index,
    {
        if values[index] < 1 || values[index] > max_value {
            assert(!(forall|i: int| 0 <= i < values.len()
                ==> 1 <= #[trigger] values@[i] <= max_value));
            return false;
        }
        index += 1;
    }
    true
}

#[expect(clippy::indexing_slicing, reason = "the loop proves the edge index is in bounds")]
#[expect(clippy::arithmetic_side_effects, reason = "the loop proves the cursor remains within the vector")]
#[expect(clippy::ptr_arg, reason = "Verus sequence-view contracts are stated over Vec in this checked boundary")]
fn edges_within_nodes(edges: &Vec<(usize, usize)>, num_nodes: usize) -> (valid: bool)
    ensures
        valid == (forall|i: int| 0 <= i < edges.len()
            ==> edges@[i].0 < num_nodes && edges@[i].1 < num_nodes),
{
    let mut index: usize = 0;
    while index < edges.len()
        invariant
            index <= edges.len(),
            forall|i: int| 0 <= i < index
                ==> edges@[i].0 < num_nodes && edges@[i].1 < num_nodes,
        decreases edges.len() - index,
    {
        if edges[index].0 >= num_nodes || edges[index].1 >= num_nodes {
            assert(!(forall|i: int| 0 <= i < edges.len()
                ==> edges@[i].0 < num_nodes && edges@[i].1 < num_nodes));
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

impl Default for ResourceRegistry {
    fn default() -> Self {
        Self::new()
    }
}

macro_rules! impl_observational_debug {
    ($type:ty, $name:literal, $($field:literal => $method:ident),+ $(,)?) => {
        impl core::fmt::Debug for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let mut state = formatter.debug_struct($name);
                $(state.field($field, &self.$method());)+
                state.finish()
            }
        }
    };
}

impl_observational_debug!(Budget, "Budget",
    "capacity" => capacity,
    "allocated" => allocated,
    "reserved" => reserved,
    "pending_eviction" => pending_eviction,
    "available" => available,
);
impl_observational_debug!(ResourceRegistry, "ResourceRegistry", "len" => len);
impl_observational_debug!(AuditSink, "AuditSink",
    "capacity" => capacity,
    "len" => len,
    "last_hash" => last_hash,
    "valid" => validate,
);
impl_observational_debug!(Cursor, "Cursor", "position" => position);
impl_observational_debug!(PropagationPass, "PropagationPass",
    "num_nodes" => num_nodes,
    "max_iterations" => max_iterations,
    "iteration" => iteration,
    "round" => round,
    "changed" => changed,
);
impl_observational_debug!(ActuationPass, "ActuationPass",
    "len" => len,
    "complete" => is_complete,
    "ready_to_finish" => ready_to_finish,
);
impl_observational_debug!(QualityHierarchy, "QualityHierarchy",
    "len" => len,
    "max_level" => max_level,
    "edge_count" => edge_count,
);
impl_observational_debug!(BacktrackingTraversal, "BacktrackingTraversal",
    "max_depth" => max_depth,
    "depth" => depth,
    "auxiliary" => auxiliary,
    "visited_count" => visited_count,
    "leaf" => is_leaf,
);
impl_observational_debug!(CompetitiveSelectionHard, "CompetitiveSelectionHard",
    "len" => len,
    "winner" => winner,
);
impl_observational_debug!(CompetitiveSelectionHardExclusive, "CompetitiveSelectionHardExclusive",
    "seat_count" => seat_count,
    "candidate_count" => candidate_count,
    "max_score" => max_score,
);
impl_observational_debug!(CompetitiveSelectionSoft, "CompetitiveSelectionSoft",
    "len" => len,
    "weight_total" => weight_total,
    "assigned_weight" => assigned_weight,
    "max_score" => max_score,
    "complete" => is_complete,
);
impl_observational_debug!(CompetitiveSelectionRanked, "CompetitiveSelectionRanked",
    "len" => len,
    "limit" => limit,
    "max_score" => max_score,
);
impl_observational_debug!(ConvergenceGovernor, "ConvergenceGovernor",
    "threshold" => threshold,
    "awaken_threshold" => awaken_threshold,
    "window" => window,
    "max_delta" => max_delta,
    "state" => state,
    "phase" => phase,
    "peak_observed" => peak_observed,
    "history_len" => history_len,
);

impl core::fmt::Display for BudgetError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::AmountExceedsReservation => "amount exceeds the held reservation",
            Self::AmountExceedsAllocation => "amount exceeds the committed allocation",
            Self::AmountExceedsPendingEviction => "amount exceeds pending eviction",
        })
    }
}

impl std::error::Error for BudgetError {}

impl core::fmt::Display for CursorError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::Regression => "cursor movement would regress the retained position",
        })
    }
}

impl std::error::Error for CursorError {}

impl core::fmt::Display for PropagationBuildError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::InitialValueOutOfRange => "an initial value exceeds the declared value ceiling",
            Self::EdgeEndpointOutOfRange => "an edge endpoint is outside the admitted node set",
        })
    }
}

impl std::error::Error for PropagationBuildError {}

impl core::fmt::Display for PropagationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::NodeOutOfRange => "node is outside the admitted graph",
            Self::RoundAlreadyRunning => "a propagation round is already running",
            Self::RoundNotRunning => "no propagation round is running",
            Self::NodeAlreadyUpdated => "node already committed an update in this round",
            Self::RoundIncomplete => "not every node committed an update",
            Self::PassTerminated => "propagation pass is settled or exhausted",
            Self::PassStillRunning => "propagation pass has not reached a terminal state",
        })
    }
}

impl std::error::Error for PropagationError {}

impl core::fmt::Display for ActuationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::SeatOutOfRange => "seat is outside the admitted seat set",
            Self::PassComplete => "actuation pass is already complete",
            Self::SeatAlreadyAllocated => "seat already holds a resource",
            Self::SeatUnallocated => "seat holds no resource",
            Self::SeatAlreadyActuated => "seat already committed its effect",
            Self::PassIncomplete => "an allocated seat has not committed its effect",
        })
    }
}

impl std::error::Error for ActuationError {}

impl core::fmt::Display for QualityHierarchyError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::NodeOutOfRange => "node is outside the admitted hierarchy",
            Self::ParentOutOfRange => "parent is outside the admitted hierarchy",
            Self::ChildOutOfRange => "child is outside the admitted hierarchy",
            Self::LevelOutOfRange => "level exceeds the hierarchy ceiling",
            Self::CostOutOfRange => "cost exceeds the hierarchy ceiling",
            Self::NodeNotIsolated => "node properties may change only while the node is isolated",
            Self::SelfEdge => "a hierarchy node cannot be its own child",
            Self::EdgeAlreadyExists => "the parent-child edge already exists",
            Self::ChildAlreadyParented => "the child already has a parent",
            Self::LevelOrderViolation => "parent level must strictly exceed child level",
            Self::CostOrderViolation => "parent cost must not exceed child cost",
        })
    }
}

impl std::error::Error for QualityHierarchyError {}

impl core::fmt::Display for BacktrackingBuildError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::InitialAuxOutOfRange => {
                "initial auxiliary value is outside the modulo-three domain"
            }
        })
    }
}

impl std::error::Error for BacktrackingBuildError {}

impl core::fmt::Display for BacktrackingError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::AtLeaf => "descent is disabled at a leaf",
            Self::ChoiceOutOfRange => "branch choice is outside the admitted branch set",
            Self::DeltaOutOfRange => "mutation delta must be one or two",
            Self::NotLeaf => "visit requires a full-depth leaf",
            Self::AlreadyVisited => "the current leaf was already visited",
            Self::AtRoot => "ascent is disabled at the root",
        })
    }
}

impl std::error::Error for BacktrackingError {}

impl core::fmt::Display for CompetitiveSelectionError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::NoCandidates => "at least one candidate is required",
            Self::CandidateOutOfRange => "candidate is outside the admitted candidate set",
            Self::SeatOutOfRange => "seat is outside the admitted seat set",
            Self::SeatAlreadyAllocated => "seat already holds an allocation",
            Self::NoCandidateAvailable => "no candidate is available for the seat",
            Self::ScoreOutOfRange => "score is outside the admitted score domain",
            Self::ScoreCountMismatch => "replacement scores have a different candidate count",
            Self::WeightTotalBelowReservedFloor => {
                "weight total is smaller than the reserved candidate floor"
            }
            Self::WeightTotalOutOfRange => "weight total exceeds the verified arithmetic ceiling",
            Self::MaxScoreOutOfRange => "maximum score exceeds the verified arithmetic ceiling",
            Self::AllocationComplete => "all soft-selection weight has been assigned",
        })
    }
}

impl std::error::Error for CompetitiveSelectionError {}

impl core::fmt::Display for ConvergenceBuildError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::ThresholdOutOfRange => "convergence threshold cannot be doubled safely",
            Self::EmptyWindow => "convergence history window must be nonempty",
            Self::WindowSumOutOfRange => "maximum convergence window sum exceeds u64",
        })
    }
}

impl std::error::Error for ConvergenceBuildError {}

impl core::fmt::Display for ConvergenceError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::DeltaOutOfRange => "delta exceeds the configured maximum",
        })
    }
}

impl std::error::Error for ConvergenceError {}
