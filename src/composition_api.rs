//! Checked public entry points for reusable named compositions.

use crate::api::values_within_max;
use crate::compositions::allocation_snapshot::AllocationSnapshot as AllocationSnapshotCarrier;
use crate::compositions::bisection::Bisection as BisectionCarrier;
use crate::compositions::equivalence_class::EquivalenceClass as EquivalenceClassCarrier;
use crate::compositions::federated_budget::FederatedBudget as FederatedBudgetCarrier;
use crate::compositions::rate_limit::RateLimit as RateLimitCarrier;
use crate::compositions::reduction::Reducer as ReductionCarrier;
use crate::compositions::relationship_graph::RelationshipGraph as RelationshipGraphCarrier;
use crate::compositions::sampler::Sampler as SamplerCarrier;
use crate::compositions::signal::Signal as SignalCarrier;
use crate::compositions::traversal_engine::TraversalEngine as TraversalEngineCarrier;
use vstd::prelude::*;

verus! {

/// A disabled allocation-snapshot transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AllocationSnapshotError {
    /// The node is outside the configured node universe.
    NodeOutOfRange,
    /// The node is already present in the snapshot.
    NodeAlreadyAccepted,
    /// Accepted nodes must have a positive cost.
    ZeroCost,
    /// The node cost exceeds the remaining budget.
    InsufficientBudget,
}

/// A reusable accepted-node snapshot coupled to one capacity budget.
pub struct AllocationSnapshot {
    inner: AllocationSnapshotCarrier,
}

impl AllocationSnapshot {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.type_invariant() && self.inner.budget_consistency()
    }

    /// Construct an empty snapshot.
    pub fn new(capacity: u64, num_nodes: u64) -> (snapshot: Self) {
        Self { inner: AllocationSnapshotCarrier::new(capacity, num_nodes) }
    }

    /// Fixed capacity ceiling.
    pub fn capacity(&self) -> u64 { self.inner.capacity }

    /// Size of the admitted node universe.
    pub fn num_nodes(&self) -> u64 { self.inner.num_nodes }

    /// Cost accepted into the snapshot.
    pub fn total_cost(&self) -> u64 { self.inner.total_cost }

    /// Capacity not yet consumed.
    pub fn budget_remaining(&self) -> u64 { self.inner.budget_remaining }

    /// Number of accepted nodes.
    pub fn len(&self) -> usize { self.inner.accepted.len() }

    /// Whether no nodes have been accepted.
    pub fn is_empty(&self) -> bool { self.inner.accepted.is_empty() }

    /// Whether a node has been accepted.
    pub fn contains(&self, node: u64) -> bool { self.inner.contains_exec(node) }

    /// Read one accepted node by insertion order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the accepted-node index is in bounds")]
    pub fn accepted(&self, index: usize) -> Option<u64> {
        if index < self.inner.accepted.len() { Some(self.inner.accepted[index]) } else { None }
    }

    /// Accept a fresh node whose positive cost fits the remaining capacity.
    pub fn accept(&mut self, node: u64, cost: u64) -> (result: Result<(), AllocationSnapshotError>) {
        proof { use_type_invariant(&*self); }
        if node >= self.inner.num_nodes { return Err(AllocationSnapshotError::NodeOutOfRange); }
        if self.inner.contains_exec(node) { return Err(AllocationSnapshotError::NodeAlreadyAccepted); }
        if cost == 0 { return Err(AllocationSnapshotError::ZeroCost); }
        if cost > self.inner.budget_remaining { return Err(AllocationSnapshotError::InsufficientBudget); }
        let mut carrier = allocation_snapshot_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.accept_node(node, cost);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// A master capacity pool divided into reusable sub-pools.
pub struct FederatedBudget {
    inner: FederatedBudgetCarrier,
}

impl FederatedBudget {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Construct an empty federation with `num_pools` sub-pools.
    pub fn new(master_capacity: u64, num_pools: usize) -> (budget: Self) {
        Self { inner: FederatedBudgetCarrier::new(master_capacity, num_pools) }
    }

    /// Fixed master capacity.
    pub fn master_capacity(&self) -> u64 { self.inner.master_capacity }

    /// Master capacity currently delegated to sub-pools.
    pub fn master_allocated(&self) -> u64 { self.inner.master_allocated }

    /// Number of sub-pools.
    pub fn len(&self) -> usize { self.inner.sub_capacities.len() }

    /// Whether no sub-pools are configured.
    pub fn is_empty(&self) -> bool { self.inner.sub_capacities.is_empty() }

    /// Read one sub-pool capacity.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the pool index is in bounds")]
    pub fn pool_capacity(&self, pool: usize) -> Option<u64> {
        if pool < self.inner.sub_capacities.len() { Some(self.inner.sub_capacities[pool]) } else { None }
    }

    /// Read one sub-pool allocation.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the pool index is in bounds")]
    pub fn pool_allocated(&self, pool: usize) -> Option<u64> {
        if pool < self.inner.sub_allocated.len() { Some(self.inner.sub_allocated[pool]) } else { None }
    }

    /// Try to delegate master capacity to a sub-pool.
    #[must_use]
    pub fn try_delegate(&mut self, pool: usize, amount: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = federated_budget_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.allocate_sub_pool(pool, amount);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Try to consume capacity within a sub-pool.
    #[must_use]
    pub fn try_allocate(&mut self, pool: usize, amount: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = federated_budget_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.allocate_from_sub_pool(pool, amount);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Try to release capacity consumed within a sub-pool.
    #[must_use]
    pub fn try_release(&mut self, pool: usize, amount: u64) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = federated_budget_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.release_from_sub_pool(pool, amount);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }
}

/// Invalid bisection configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum BisectionBuildError {
    /// The ordered domain must contain at least two points.
    DomainTooSmall,
    /// The threshold must be inside `1..domain_size`.
    ThresholdOutOfRange,
}

/// A disabled bisection transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum BisectionError {
    /// The candidate interval is already converged.
    AlreadyConverged,
}

/// A bounded monotone-boundary bisection machine.
pub struct Bisection {
    inner: BisectionCarrier,
}

impl Bisection {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.invariant() }

    /// Construct a full-domain bisection using the complete `u64` probe budget.
    pub fn new(domain_size: u64, threshold: u64) -> (result: Result<Self, BisectionBuildError>) {
        if domain_size < 2 { return Err(BisectionBuildError::DomainTooSmall); }
        if threshold < 1 || threshold >= domain_size {
            return Err(BisectionBuildError::ThresholdOutOfRange);
        }
        proof { lemma_u64_domain_fits_64(domain_size); }
        let inner = BisectionCarrier::new(0, domain_size, threshold, domain_size, 64);
        Ok(Self { inner })
    }

    /// Current lower bound.
    pub fn lower(&self) -> u64 { self.inner.lo }

    /// Current upper bound.
    pub fn upper(&self) -> u64 { self.inner.hi }

    /// Hidden monotone boundary used by this executable carrier.
    pub fn threshold(&self) -> u64 { self.inner.threshold }

    /// Number of probes taken.
    pub fn probes_taken(&self) -> u64 { self.inner.probes_taken }

    /// Maximum number of probes.
    pub fn max_probes(&self) -> u64 { self.inner.max_probes }

    /// Whether the candidate interval has width less than two.
    pub fn is_converged(&self) -> bool {
        proof { use_type_invariant(&*self); }
        self.inner.converged()
    }

    /// Perform one midpoint probe.
    pub fn probe(&mut self) -> (result: Result<(), BisectionError>) {
        proof { use_type_invariant(&*self); }
        if self.inner.hi - self.inner.lo < 2 { return Err(BisectionError::AlreadyConverged); }
        let mut carrier = bisection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.probe();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Drive midpoint probes until the interval converges.
    pub fn converge(&mut self) {
        proof { use_type_invariant(&*self); }
        let mut carrier = bisection_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.bisect();
        core::mem::swap(&mut self.inner, &mut carrier);
    }
}

/// An invalid equivalence-class element index.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum EquivalenceClassError {
    /// The element is outside the configured universe.
    ElementOutOfRange,
}

/// A bounded union-by-rank equivalence-class partition.
pub struct EquivalenceClass {
    inner: EquivalenceClassCarrier,
}

impl EquivalenceClass {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Construct a singleton partition with a merge-operation ceiling.
    pub fn new(elements: usize, max_unions: u64) -> (classes: Self) {
        Self { inner: EquivalenceClassCarrier::new(elements, max_unions) }
    }

    /// Number of elements in the partition.
    pub fn len(&self) -> usize { self.inner.n }

    /// Whether the partition contains no elements.
    pub fn is_empty(&self) -> bool { self.inner.n == 0 }

    /// Successful union operations performed.
    pub fn unions_performed(&self) -> u64 { self.inner.ops_done }

    /// Configured union-operation ceiling.
    pub fn max_unions(&self) -> u64 { self.inner.max_ops }

    /// Find an element's representative.
    pub fn representative(&self, element: usize) -> (result: Result<usize, EquivalenceClassError>) {
        proof { use_type_invariant(&*self); }
        if element >= self.inner.n { return Err(EquivalenceClassError::ElementOutOfRange); }
        Ok(self.inner.find(element))
    }

    /// Merge two classes, returning false if equal or the operation ceiling is exhausted.
    pub fn union(&mut self, left: usize, right: usize) -> (result: Result<bool, EquivalenceClassError>) {
        proof { use_type_invariant(&*self); }
        if left >= self.inner.n || right >= self.inner.n {
            return Err(EquivalenceClassError::ElementOutOfRange);
        }
        let mut carrier = equivalence_class_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let merged = carrier.union(left, right);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(merged)
    }

    /// Test whether two elements have the same representative.
    pub fn equivalent(&self, left: usize, right: usize) -> (result: Result<bool, EquivalenceClassError>) {
        proof { use_type_invariant(&*self); }
        if left >= self.inner.n || right >= self.inner.n {
            return Err(EquivalenceClassError::ElementOutOfRange);
        }
        Ok(self.inner.same(left, right))
    }
}

/// Invalid rate-limit configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum RateLimitBuildError {
    /// A rate limit must admit at least one operation per window.
    ZeroLimit,
}

/// A disabled rate-limit transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum RateLimitError {
    /// The bounded logical clock has reached its configured maximum.
    ClockExhausted,
}

/// A logical-clock, fixed-window rate limit.
pub struct RateLimit {
    inner: RateLimitCarrier,
}

impl RateLimit {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.type_invariant() && self.inner.window_start_not_future()
    }

    /// Construct a rate limit at logical clock zero.
    pub fn new(max_per_window: u64, window_duration: u64, max_clock: u64)
        -> (result: Result<Self, RateLimitBuildError>) {
        if max_per_window == 0 { return Err(RateLimitBuildError::ZeroLimit); }
        Ok(Self { inner: RateLimitCarrier::new(max_per_window, window_duration, max_clock) })
    }

    /// Per-window admission ceiling.
    pub fn max_per_window(&self) -> u64 { self.inner.max_per_window }

    /// Window duration in logical-clock units.
    pub fn window_duration(&self) -> u64 { self.inner.window_duration }

    /// Acquisitions admitted in the current window.
    pub fn count(&self) -> u64 { self.inner.count }

    /// Current logical clock.
    pub fn clock(&self) -> u64 { self.inner.clock }

    /// Current window anchor.
    pub fn window_start(&self) -> u64 { self.inner.window_start }

    /// Try to acquire one unit in the current or newly rolled window.
    #[must_use]
    pub fn try_acquire(&mut self) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = rate_limit_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.try_acquire();
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Advance the bounded logical clock by one.
    pub fn tick(&mut self) -> (result: Result<(), RateLimitError>) {
        proof { use_type_invariant(&*self); }
        if self.inner.clock >= self.inner.max_clock { return Err(RateLimitError::ClockExhausted); }
        let mut carrier = rate_limit_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.tick();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// Invalid reduction input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ReductionBuildError {
    /// The input exceeds the verified one-billion-item ceiling.
    TooManyItems,
    /// An input value exceeds the verified one-billion-unit ceiling.
    ValueOutOfRange,
}

/// A disabled incremental reduction transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ReductionError {
    /// Every input item has already been consumed.
    Complete,
}

/// An incremental additive ordered-prefix reduction.
pub struct Reduction {
    inner: ReductionCarrier,
}

impl Reduction {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.partition() && self.inner.aggregate() && self.inner.bounded()
    }

    /// Validate and construct an incremental sum reduction.
    pub fn new(items: Vec<u64>) -> (result: Result<Self, ReductionBuildError>) {
        if items.len() > 1_000_000_000 { return Err(ReductionBuildError::TooManyItems); }
        if !values_within_max(&items, 1_000_000_000) {
            return Err(ReductionBuildError::ValueOutOfRange);
        }
        Ok(Self { inner: ReductionCarrier::new(items) })
    }

    /// Current additive result.
    pub fn result(&self) -> u64 { self.inner.result }

    /// Number of consumed items.
    pub fn processed_len(&self) -> usize { self.inner.processed.len() }

    /// Number of pending items.
    pub fn remaining_len(&self) -> usize { self.inner.remaining.len() }

    /// Whether the whole input has been consumed.
    pub fn is_complete(&self) -> bool { self.inner.done() }

    /// Consume the next item in original order.
    pub fn process_next(&mut self) -> (result: Result<(), ReductionError>) {
        proof { use_type_invariant(&*self); }
        if self.inner.remaining.is_empty() { return Err(ReductionError::Complete); }
        let mut carrier = reduction_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.process();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// A disabled relationship-graph transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum RelationshipGraphError {
    /// A source or destination node is outside the configured graph.
    NodeOutOfRange,
    /// The edge weight exceeds the configured maximum.
    WeightOutOfRange,
    /// Self-loops are not admitted.
    SelfLoop,
}

/// A weighted directed graph with a consistent adjacency projection.
pub struct RelationshipGraph {
    inner: RelationshipGraphCarrier,
}

impl RelationshipGraph {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Construct an empty graph.
    pub fn new(num_nodes: usize, max_weight: u64) -> (graph: Self) {
        Self { inner: RelationshipGraphCarrier::new(num_nodes, max_weight) }
    }

    /// Number of nodes.
    pub fn num_nodes(&self) -> usize { self.inner.num_nodes }

    /// Maximum admitted edge weight.
    pub fn max_weight(&self) -> u64 { self.inner.max_weight }

    /// Number of concrete weighted edges.
    pub fn edge_count(&self) -> usize { self.inner.edges.len() }

    /// Read a concrete weighted edge by insertion order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the edge index is in bounds")]
    pub fn edge(&self, index: usize) -> Option<(usize, usize, u64)> {
        if index < self.inner.edges.len() { Some(self.inner.edges[index]) } else { None }
    }

    /// Whether any weighted edge exists for a source-destination pair.
    pub fn contains(&self, source: usize, destination: usize) -> bool {
        self.inner.contains_pair(source, destination)
    }

    /// Add one concrete weighted edge if it is not already present.
    pub fn add_edge(&mut self, source: usize, destination: usize, weight: u64)
        -> (result: Result<bool, RelationshipGraphError>) {
        proof { use_type_invariant(&*self); }
        if source >= self.inner.num_nodes || destination >= self.inner.num_nodes {
            return Err(RelationshipGraphError::NodeOutOfRange);
        }
        if weight > self.inner.max_weight { return Err(RelationshipGraphError::WeightOutOfRange); }
        if source == destination { return Err(RelationshipGraphError::SelfLoop); }
        let mut carrier = relationship_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let added = carrier.add_edge(source, destination, weight);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(added)
    }

    /// Remove every weighted edge for one source-destination pair.
    pub fn remove_edges(&mut self, source: usize, destination: usize) {
        proof { use_type_invariant(&*self); }
        let mut carrier = relationship_graph_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.remove_edge(source, destination);
        core::mem::swap(&mut self.inner, &mut carrier);
    }
}

/// A disabled sampler transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SamplerError {
    /// The item index is outside the distribution.
    ItemOutOfRange,
    /// The bounded sample is full.
    SampleFull,
    /// The item has zero support weight.
    OutsideSupport,
    /// The item has already been selected.
    AlreadySelected,
}

/// A bounded without-replacement sampler over caller-supplied proposals.
pub struct Sampler {
    inner: SamplerCarrier,
}

impl Sampler {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool { self.inner.inv() }

    /// Construct an empty sample over a weight distribution.
    pub fn new(distribution: Vec<u64>, sample_size: usize) -> (sampler: Self) {
        Self { inner: SamplerCarrier::new(distribution, sample_size) }
    }

    /// Number of distribution items.
    pub fn len(&self) -> usize { self.inner.num_items }

    /// Whether the distribution contains no items.
    pub fn is_empty(&self) -> bool { self.inner.num_items == 0 }

    /// Maximum selected cardinality.
    pub fn sample_size(&self) -> usize { self.inner.sample_size }

    /// Number of selected items.
    pub fn selected_len(&self) -> usize { self.inner.selected.len() }

    /// Read one distribution weight.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the item index is in bounds")]
    pub fn weight(&self, item: usize) -> Option<u64> {
        if item < self.inner.distribution.len() { Some(self.inner.distribution[item]) } else { None }
    }

    /// Whether an item has already been selected.
    pub fn contains(&self, item: usize) -> bool { self.inner.contains_exec(item) }

    /// Admit one supported item directly.
    pub fn sample(&mut self, item: usize) -> (result: Result<(), SamplerError>) {
        proof { use_type_invariant(&*self); }
        if item >= self.inner.num_items { return Err(SamplerError::ItemOutOfRange); }
        if self.inner.selected.len() >= self.inner.sample_size { return Err(SamplerError::SampleFull); }
        if self.inner.distribution[item] == 0 { return Err(SamplerError::OutsideSupport); }
        if self.inner.contains_exec(item) { return Err(SamplerError::AlreadySelected); }
        let mut carrier = sampler_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.sample(item);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Remove an unselected item from the live support.
    #[must_use]
    pub fn zero(&mut self, item: usize) -> (accepted: bool) {
        proof { use_type_invariant(&*self); }
        let mut carrier = sampler_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.zero(item);
        core::mem::swap(&mut self.inner, &mut carrier);
        accepted
    }

    /// Apply weighted rejection to an externally proposed item and entropy value.
    pub fn draw_weighted(&mut self, item: usize, entropy: u64) -> (result: Result<bool, SamplerError>) {
        proof { use_type_invariant(&*self); }
        if item >= self.inner.num_items { return Err(SamplerError::ItemOutOfRange); }
        let mut carrier = sampler_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.draw_weighted(item, entropy);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(accepted)
    }

    /// Apply uniform-support admission to an externally proposed item.
    pub fn draw_uniform(&mut self, item: usize) -> (result: Result<bool, SamplerError>) {
        proof { use_type_invariant(&*self); }
        if item >= self.inner.num_items { return Err(SamplerError::ItemOutOfRange); }
        let mut carrier = sampler_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let accepted = carrier.draw_uniform(item);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(accepted)
    }
}

/// Invalid signal configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SignalBuildError {
    /// The initial value is outside the configured value universe.
    InitialValueOutOfRange,
}

/// A disabled signal transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SignalError {
    /// A value is outside the configured value universe.
    ValueOutOfRange,
    /// A listener is outside the configured listener universe.
    ListenerOutOfRange,
    /// The listener has no pending notification.
    ListenerNotPending,
}

/// A change-detecting signal with per-listener notification provenance.
pub struct Signal {
    inner: SignalCarrier,
}

impl Signal {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.type_invariant()
            && self.inner.pending_notified_disjointness()
            && self.inner.notification_provenance()
    }

    /// Construct a signal with no pending notification.
    pub fn new(initial_value: u64, num_values: u64, num_listeners: usize)
        -> (result: Result<Self, SignalBuildError>) {
        if initial_value >= num_values { return Err(SignalBuildError::InitialValueOutOfRange); }
        Ok(Self { inner: SignalCarrier::new(initial_value, num_values, num_listeners) })
    }

    /// Current retained value.
    pub fn value(&self) -> u64 { self.inner.current_value }

    /// Number of listeners.
    pub fn listener_count(&self) -> usize { self.inner.num_listeners }

    /// Whether any actual value change has occurred.
    pub fn change_observed(&self) -> bool { self.inner.change_observed }

    /// Whether one listener has a pending notification.
    pub fn is_pending(&self, listener: usize) -> Option<bool> {
        proof { use_type_invariant(&*self); }
        if listener < self.inner.num_listeners { Some(self.inner.is_pending(listener)) } else { None }
    }

    /// Whether one listener has received the latest notification.
    pub fn is_notified(&self, listener: usize) -> Option<bool> {
        proof { use_type_invariant(&*self); }
        if listener < self.inner.num_listeners { Some(self.inner.is_notified(listener)) } else { None }
    }

    /// Set a value, returning false for an unchanged value.
    pub fn set_value(&mut self, value: u64) -> (result: Result<bool, SignalError>) {
        proof { use_type_invariant(&*self); }
        if value >= self.inner.num_values { return Err(SignalError::ValueOutOfRange); }
        let mut carrier = signal_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        let changed = carrier.set_value(value);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(changed)
    }

    /// Move one listener's pending notification into delivered state.
    pub fn notify(&mut self, listener: usize) -> (result: Result<(), SignalError>) {
        proof { use_type_invariant(&*self); }
        if listener >= self.inner.num_listeners { return Err(SignalError::ListenerOutOfRange); }
        if !self.inner.is_pending(listener) { return Err(SignalError::ListenerNotPending); }
        let mut carrier = signal_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.notify_listener(listener);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

/// Invalid traversal-engine configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum TraversalBuildError {
    /// At least one node is required.
    NoNodes,
    /// The root is outside the node universe.
    RootOutOfRange,
}

/// A disabled traversal-engine transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum TraversalError {
    /// The node is outside the configured universe.
    NodeOutOfRange,
    /// The node is not queued.
    NodeNotQueued,
    /// The node has already been visited.
    NodeAlreadyVisited,
    /// Termination is enabled only when the queue is empty.
    QueueNotEmpty,
}

/// A budgeted star-graph traversal with accepted-subset tracking.
pub struct TraversalEngine {
    inner: TraversalEngineCarrier,
}

impl TraversalEngine {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        self.inner.type_invariant()
            && self.inner.budget_invariant()
            && self.inner.accepted_subset_visited()
            && self.inner.root < self.inner.num_nodes
    }

    /// Construct a traversal rooted in the configured node universe.
    pub fn new(num_nodes: usize, root: usize, budget: u64)
        -> (result: Result<Self, TraversalBuildError>) {
        if num_nodes == 0 { return Err(TraversalBuildError::NoNodes); }
        if root >= num_nodes { return Err(TraversalBuildError::RootOutOfRange); }
        Ok(Self { inner: TraversalEngineCarrier::new(num_nodes, root, budget) })
    }

    /// Number of nodes.
    pub fn num_nodes(&self) -> usize { self.inner.num_nodes }

    /// Traversal root.
    pub fn root(&self) -> usize { self.inner.root }

    /// Remaining traversal budget.
    pub fn budget_remaining(&self) -> u64 { self.inner.budget_remaining }

    /// Number of queued nodes.
    pub fn queued_len(&self) -> usize { self.inner.queue.len() }

    /// Number of visited nodes.
    pub fn visited_len(&self) -> usize { self.inner.visited.len() }

    /// Number of budget-accepted nodes.
    pub fn accepted_len(&self) -> usize { self.inner.accepted.len() }

    /// Whether a node is queued.
    pub fn is_queued(&self, node: usize) -> bool { self.inner.queue_contains(node) }

    /// Whether a node was visited.
    pub fn is_visited(&self, node: usize) -> bool { self.inner.visited_contains(node) }

    /// Whether a node was accepted under the budget.
    pub fn is_accepted(&self, node: usize) -> bool { self.inner.accepted_contains(node) }

    /// Visit one queued, unvisited node.
    pub fn visit(&mut self, node: usize) -> (result: Result<(), TraversalError>) {
        proof { use_type_invariant(&*self); }
        if node >= self.inner.num_nodes { return Err(TraversalError::NodeOutOfRange); }
        if !self.inner.queue_contains(node) { return Err(TraversalError::NodeNotQueued); }
        if self.inner.visited_contains(node) { return Err(TraversalError::NodeAlreadyVisited); }
        let mut carrier = traversal_engine_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.visit_node(node);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Remove one queued node without visiting it.
    pub fn skip(&mut self, node: usize) -> (result: Result<(), TraversalError>) {
        proof { use_type_invariant(&*self); }
        if node >= self.inner.num_nodes { return Err(TraversalError::NodeOutOfRange); }
        if !self.inner.queue_contains(node) { return Err(TraversalError::NodeNotQueued); }
        let mut carrier = traversal_engine_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.skip(node);
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }

    /// Confirm the terminal stutter when no queued work remains.
    pub fn terminate(&mut self) -> (result: Result<(), TraversalError>) {
        proof { use_type_invariant(&*self); }
        if !self.inner.queue.is_empty() { return Err(TraversalError::QueueNotEmpty); }
        let mut carrier = traversal_engine_sentinel();
        core::mem::swap(&mut self.inner, &mut carrier);
        carrier.terminate();
        core::mem::swap(&mut self.inner, &mut carrier);
        Ok(())
    }
}

proof fn lemma_u64_domain_fits_64(value: u64)
    ensures value as int <= crate::compositions::bisection::pow2(64),
{
    assert(crate::compositions::bisection::pow2(64) == 18_446_744_073_709_551_616int) by (compute);
}

fn allocation_snapshot_sentinel() -> (carrier: AllocationSnapshotCarrier)
    ensures carrier.type_invariant(), carrier.budget_consistency(),
{ AllocationSnapshotCarrier::new(0, 0) }

fn federated_budget_sentinel() -> (carrier: FederatedBudgetCarrier)
    ensures carrier.inv(),
{ FederatedBudgetCarrier::new(0, 0) }

fn bisection_sentinel() -> (carrier: BisectionCarrier)
    ensures carrier.invariant(),
{
    proof {
        assert(crate::compositions::bisection::pow2(1) == 2) by (compute);
    }
    BisectionCarrier::new(0, 2, 1, 2, 1)
}

fn equivalence_class_sentinel() -> (carrier: EquivalenceClassCarrier)
    ensures carrier.inv(),
{ EquivalenceClassCarrier::new(0, 0) }

fn rate_limit_sentinel() -> (carrier: RateLimitCarrier)
    ensures carrier.type_invariant(), carrier.window_start_not_future(),
{ RateLimitCarrier::new(1, 1, 0) }

fn reduction_sentinel() -> (carrier: ReductionCarrier)
    ensures carrier.partition(), carrier.aggregate(), carrier.bounded(),
{
    let values: Vec<u64> = Vec::new();
    ReductionCarrier::new(values)
}

fn relationship_graph_sentinel() -> (carrier: RelationshipGraphCarrier)
    ensures carrier.inv(),
{ RelationshipGraphCarrier::new(0, 0) }

fn sampler_sentinel() -> (carrier: SamplerCarrier)
    ensures carrier.inv(),
{
    let distribution: Vec<u64> = Vec::new();
    SamplerCarrier::new(distribution, 0)
}

fn signal_sentinel() -> (carrier: SignalCarrier)
    ensures
        carrier.type_invariant(),
        carrier.pending_notified_disjointness(),
        carrier.notification_provenance(),
{ SignalCarrier::new(0, 1, 0) }

fn traversal_engine_sentinel() -> (carrier: TraversalEngineCarrier)
    ensures
        carrier.type_invariant(),
        carrier.budget_invariant(),
        carrier.accepted_subset_visited(),
        carrier.root < carrier.num_nodes,
{ TraversalEngineCarrier::new(1, 0, 0) }

}

macro_rules! impl_error {
    ($type:ty, { $($variant:path => $message:literal),+ $(,)? }) => {
        impl core::fmt::Display for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str(match self { $($variant => $message),+ })
            }
        }
        impl std::error::Error for $type {}
    };
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

impl_observational_debug!(AllocationSnapshot, "AllocationSnapshot",
    "capacity" => capacity,
    "num_nodes" => num_nodes,
    "total_cost" => total_cost,
    "budget_remaining" => budget_remaining,
    "len" => len,
);
impl_observational_debug!(FederatedBudget, "FederatedBudget",
    "master_capacity" => master_capacity,
    "master_allocated" => master_allocated,
    "len" => len,
);
impl_observational_debug!(Bisection, "Bisection",
    "lower" => lower,
    "upper" => upper,
    "threshold" => threshold,
    "probes_taken" => probes_taken,
    "max_probes" => max_probes,
    "converged" => is_converged,
);
impl_observational_debug!(EquivalenceClass, "EquivalenceClass",
    "len" => len,
    "unions_performed" => unions_performed,
    "max_unions" => max_unions,
);
impl_observational_debug!(RateLimit, "RateLimit",
    "max_per_window" => max_per_window,
    "window_duration" => window_duration,
    "count" => count,
    "clock" => clock,
    "window_start" => window_start,
);
impl_observational_debug!(Reduction, "Reduction",
    "result" => result,
    "processed_len" => processed_len,
    "remaining_len" => remaining_len,
    "complete" => is_complete,
);
impl_observational_debug!(RelationshipGraph, "RelationshipGraph",
    "num_nodes" => num_nodes,
    "max_weight" => max_weight,
    "edge_count" => edge_count,
);
impl_observational_debug!(Sampler, "Sampler",
    "len" => len,
    "sample_size" => sample_size,
    "selected_len" => selected_len,
);
impl_observational_debug!(Signal, "Signal",
    "value" => value,
    "listener_count" => listener_count,
    "change_observed" => change_observed,
);
impl_observational_debug!(TraversalEngine, "TraversalEngine",
    "num_nodes" => num_nodes,
    "root" => root,
    "budget_remaining" => budget_remaining,
    "queued_len" => queued_len,
    "visited_len" => visited_len,
    "accepted_len" => accepted_len,
);

impl_error!(AllocationSnapshotError, {
    Self::NodeOutOfRange => "node is outside the snapshot universe",
    Self::NodeAlreadyAccepted => "node is already accepted",
    Self::ZeroCost => "accepted node cost must be positive",
    Self::InsufficientBudget => "node cost exceeds the remaining budget",
});
impl_error!(BisectionBuildError, {
    Self::DomainTooSmall => "bisection domain must contain at least two points",
    Self::ThresholdOutOfRange => "bisection threshold is outside the domain",
});
impl_error!(BisectionError, { Self::AlreadyConverged => "bisection is already converged" });
impl_error!(EquivalenceClassError, { Self::ElementOutOfRange => "element is outside the partition" });
impl_error!(RateLimitBuildError, { Self::ZeroLimit => "rate limit must admit at least one operation" });
impl_error!(RateLimitError, { Self::ClockExhausted => "rate-limit logical clock is exhausted" });
impl_error!(ReductionBuildError, {
    Self::TooManyItems => "reduction input exceeds the verified item ceiling",
    Self::ValueOutOfRange => "reduction input exceeds the verified value ceiling",
});
impl_error!(ReductionError, { Self::Complete => "reduction is already complete" });
impl_error!(RelationshipGraphError, {
    Self::NodeOutOfRange => "graph node is outside the configured universe",
    Self::WeightOutOfRange => "edge weight exceeds the configured maximum",
    Self::SelfLoop => "relationship graph does not admit self-loops",
});
impl_error!(SamplerError, {
    Self::ItemOutOfRange => "sample item is outside the distribution",
    Self::SampleFull => "bounded sample is full",
    Self::OutsideSupport => "sample item has zero support weight",
    Self::AlreadySelected => "sample item is already selected",
});
impl_error!(SignalBuildError, { Self::InitialValueOutOfRange => "initial signal value is outside its universe" });
impl_error!(SignalError, {
    Self::ValueOutOfRange => "signal value is outside its universe",
    Self::ListenerOutOfRange => "listener is outside the signal universe",
    Self::ListenerNotPending => "listener has no pending notification",
});
impl_error!(TraversalBuildError, {
    Self::NoNodes => "traversal requires at least one node",
    Self::RootOutOfRange => "traversal root is outside the node universe",
});
impl_error!(TraversalError, {
    Self::NodeOutOfRange => "traversal node is outside the configured universe",
    Self::NodeNotQueued => "traversal node is not queued",
    Self::NodeAlreadyVisited => "traversal node was already visited",
    Self::QueueNotEmpty => "traversal queue is not empty",
});
