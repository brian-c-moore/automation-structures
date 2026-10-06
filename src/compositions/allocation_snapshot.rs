// Executable carrier for AllocationSnapshot.tla. The allocation decision has
// three state variables: `accepted`, `total_cost`, and `budget_remaining`.
// `accept_node` implements the guarded `AcceptNode(n, cost)` transition and
// maintains:
//
//   TypeInvariant     == accepted ⊆ Nodes /\ total_cost ∈ Nat
//                                          /\ budget_remaining ∈ Nat
//   BudgetConsistency == total_cost + budget_remaining <= BudgetCapacity
//
// `new` implements `Init`. `capture` folds a request sequence through the same
// guarded transition and returns a record with no exposed mutator.
// Representation mapping:
//   - Nodes is the index universe 0..num_nodes; `accepted ⊆ Nodes` becomes
//     "every accepted id < num_nodes".
//   - `accepted` is a TLA+ set variable; it is modelled as a Vec<u64> carrying
//     a no-duplicates invariant, preserving the `n ∉ accepted` guard.
//   - total_cost, budget_remaining ∈ Nat are carried by u64; the spec arithmetic
//     is lifted to `int` to state BudgetConsistency without overflow noise.

use crate::compositions::reduction::{ReductionColumns, ReductionRowError};
use crate::connectives::buffer::Buffer;
use crate::connectives::cursor::Cursor;
use crate::primitives::audit_sink::AdditiveChain;
#[expect(
    unused_imports,
    reason = "TypedChainOperation is used only by erased proof contracts"
)]
use crate::primitives::audit_sink::TypedChainOperation;
use crate::primitives::budget::Budget;
use crate::primitives::resource_registry::{KeyIdentity, RegistryQuery, ResourceRegistry};
use vstd::prelude::*;

verus! {

/// Sum of the registered costs in the first `n` entries.
pub open spec fn cost_sum_to(entries: Seq<(u64, u64)>, n: int) -> int
    decreases n,
{
    if n <= 0 || n > entries.len() {
        0
    } else {
        entries[n - 1].1 as int + cost_sum_to(entries, n - 1)
    }
}

/// Appending one registry entry leaves every prior cost-sum prefix unchanged.
proof fn cost_sum_push_prefix(entries: Seq<(u64, u64)>, entry: (u64, u64), n: int)
    requires 0 <= n <= entries.len(),
    ensures cost_sum_to(entries.push(entry), n) == cost_sum_to(entries, n),
    decreases n,
{
    if n > 0 {
        cost_sum_push_prefix(entries, entry, n - 1);
        assert(entries.push(entry)[n - 1] == entries[n - 1]);
    }
}

/// Appending one cost extends the registered cost sum by exactly that cost.
pub proof fn cost_sum_push(entries: Seq<(u64, u64)>, key: u64, cost: u64)
    ensures
        cost_sum_to(entries.push((key, cost)), entries.len() as int + 1)
            == cost_sum_to(entries, entries.len() as int) + cost as int,
{
    cost_sum_push_prefix(entries, (key, cost), entries.len() as int);
    assert(entries.push((key, cost))[entries.len() as int].1 == cost);
}

/// Exact accepted-entry sequence after folding the first `n` requests.
pub open spec fn capture_entries_to(
    capacity: u64,
    num_nodes: u64,
    nodes: Seq<u64>,
    costs: Seq<u64>,
    n: int,
) -> Seq<(u64, u64)>
    decreases n,
{
    if n <= 0 || n > nodes.len() || n > costs.len() {
        Seq::empty()
    } else {
        let before = capture_entries_to(capacity, num_nodes, nodes, costs, n - 1);
        let node = nodes[n - 1];
        let cost = costs[n - 1];
        if node < num_nodes
            && cost >= 1
            && !crate::primitives::resource_registry::has_key(
                before,
                before.len() as int,
                node,
            )
            && cost_sum_to(before, before.len() as int) + cost as int
                <= capacity as int
        {
            before.push((node, cost))
        } else {
            before
        }
    }
}

/// An allocation snapshot: the accepted node set plus the running cost / budget
/// figures, over a node universe `0..num_nodes` bounded by `capacity`.
pub struct AllocationSnapshot {
    /// |Nodes|: the node universe is the index range `0..num_nodes`.
    pub num_nodes: u64,
    /// ResourceRegistry component mapping accepted nodes to their costs.
    pub registry: crate::primitives::resource_registry::ResourceRegistry<u64, u64>,
    /// Budget component charged by the registered costs.
    pub budget: crate::primitives::budget::Budget,
}

impl AllocationSnapshot {
    // ── Specifications ──────────────────────────────────────────────────

    /// `accepted ⊆ Nodes`: every accepted id is a valid node index.
    pub open spec fn accepted_subset_nodes(&self) -> bool {
        forall|i: int|
            0 <= i < self.registry.entries.len()
                ==> #[trigger] self.registry.entries@[i].0 < self.num_nodes
    }

    /// `accepted` is a set: no duplicate node ids. This encodes the TLA+ set
    /// variable and makes the AcceptNode `n ∉ accepted` guard enforceable.
    pub open spec fn accepted_distinct(&self) -> bool {
        self.registry.unique_mapping()
    }

    /// Every ResourceRegistry value is an admitted positive node cost.
    pub open spec fn costs_valid(&self) -> bool {
        forall|i: int| 0 <= i < self.registry.entries.len()
            ==> #[trigger] self.registry.entries@[i].1 > 0
    }

    /// TLA+ `TypeInvariant` (the structural clauses; the Nat clauses are carried
    /// by the u64 typing of total_cost / budget_remaining).
    pub open spec fn type_invariant(&self) -> bool {
        self.accepted_subset_nodes() && self.accepted_distinct() && self.costs_valid()
    }

    /// TLA+ `BudgetConsistency`.
    pub open spec fn budget_consistency(&self) -> bool {
        &&& self.budget.safety_invariant()
        &&& self.budget.reserved == 0
        &&& self.budget.pending_eviction == 0
        &&& self.budget.allocated as int
            == cost_sum_to(self.registry.entries@, self.registry.entries.len() as int)
    }

    /// `n ∈ accepted`.
    pub open spec fn contains(&self, n: u64) -> bool {
        self.registry.contains_key(n)
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Construct the empty snapshot: nothing accepted, full budget remaining.
    /// Realises the TLA+ `Init` predicate and establishes both invariants.
    pub fn new(capacity: u64, num_nodes: u64) -> (s: AllocationSnapshot)
        ensures
            s.num_nodes == num_nodes,
            s.registry.entries@.len() == 0,
            s.budget.capacity == capacity,
            s.budget.allocated == 0,
            s.budget.reserved == 0,
            s.budget.pending_eviction == 0,
            s.type_invariant(),
            s.budget_consistency(),
    {
        AllocationSnapshot {
            num_nodes,
            registry: crate::primitives::resource_registry::ResourceRegistry::new(),
            budget: crate::primitives::budget::Budget::new(capacity),
        }
    }

    // ── Membership (executable) ─────────────────────────────────────────

    /// Executable membership test; links to the `contains` spec so callers can
    /// discharge the `n ∉ accepted` precondition of `accept_node`.
    pub fn contains_exec(&self, n: u64) -> (b: bool)
        requires self.registry.unique_mapping(),
        ensures
            b == self.contains(n),
    {
        match self.registry.lookup(n) {
            Some(_) => true,
            None => false,
        }
    }

    // ── AcceptNode (TLA+ AcceptNode) ────────────────────────────────────

    /// Accept node `n` at cost `node_cost`. Realises the TLA+ `AcceptNode`
    /// action: its three guards are `requires`, and both invariants are
    /// re-established as `ensures` (the inductive preservation step).
    pub fn accept_node(&mut self, n: u64, node_cost: u64)
        requires
            old(self).type_invariant(),
            old(self).budget_consistency(),
            n < old(self).num_nodes,                  // n ∈ Nodes
            !old(self).contains(n),                   // n ∉ accepted
            1 <= node_cost,                           // c is positive
            old(self).budget.used() + node_cost as int <= old(self).budget.capacity as int,
        ensures
            final(self).num_nodes == old(self).num_nodes,
            final(self).registry.entries@
                == old(self).registry.entries@.push((n, node_cost)),
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).budget.allocated == old(self).budget.allocated + node_cost,
            final(self).contains(n),
            final(self).type_invariant(),
            final(self).budget_consistency(),
    {
        let _accepted = self.budget.try_allocate(node_cost);
        assert(_accepted);
        let ghost prior_entries = self.registry.entries@;
        self.registry.register(n, node_cost);
        proof { cost_sum_push(prior_entries, n, node_cost); }
        // Re-establish the set invariant: the pushed element n was absent
        // (precondition) and is a valid node, so distinctness and the subset
        // bound both carry to the extended sequence.
        assert(self.contains(n)) by {
            assert(self.registry.maps_to(n, node_cost));
        }
    }

    /// Consume the builder into an immutable captured allocation.
    pub fn seal(self) -> (captured: CapturedAllocationSnapshot)
        requires self.type_invariant(), self.budget_consistency(),
        ensures captured.valid(), captured.entries_spec() == self.registry.entries@,
            captured.capacity_spec() == self.budget.capacity,
            captured.num_nodes_spec() == self.num_nodes,
            captured.total_cost_spec() == self.budget.allocated,
            captured.remaining_spec() == self.budget.capacity - self.budget.allocated,
    {
        CapturedAllocationSnapshot { inner: self }
    }
}

/// A captured allocation with no mutable owner access or admission action.
/// The original Registry and Budget move here; no second state is retained.
///
/// ```compile_fail
/// use automation_structures::compositions::allocation_snapshot::capture;
/// let mut captured = capture(10, 3, &[0], &[3]);
/// captured.inner.accept_node(1, 2);
/// ```
pub struct CapturedAllocationSnapshot {
    inner: AllocationSnapshot,
}

impl CapturedAllocationSnapshot {
    /// The retained builder invariants hold after the consuming seal.
    pub closed spec fn valid(&self) -> bool {
        self.inner.type_invariant() && self.inner.budget_consistency()
    }
    /// Accepted membership and costs at the seal boundary.
    pub closed spec fn entries_spec(&self) -> Seq<(u64, u64)> { self.inner.registry.entries@ }
    /// Fixed admitted capacity.
    pub closed spec fn capacity_spec(&self) -> u64 { self.inner.budget.capacity }
    /// Fixed node universe.
    pub closed spec fn num_nodes_spec(&self) -> u64 { self.inner.num_nodes }
    /// Fixed accepted cost.
    pub closed spec fn total_cost_spec(&self) -> u64 { self.inner.budget.allocated }
    /// Fixed unconsumed capacity.
    pub closed spec fn remaining_spec(&self) -> u64 {
        (self.inner.budget.capacity - self.inner.budget.allocated) as u64
    }
    /// Borrow the immutable accepted entries in insertion order.
    pub fn accepted_entries(&self) -> (entries: &Vec<(u64, u64)>)
        ensures entries@ == self.entries_spec(),
    { &self.inner.registry.entries }
    /// Read the fixed admitted capacity.
    pub fn capacity(&self) -> (capacity: u64) ensures capacity == self.capacity_spec(),
    { self.inner.budget.capacity }
    /// Read the fixed node universe.
    pub fn num_nodes(&self) -> (nodes: u64) ensures nodes == self.num_nodes_spec(),
    { self.inner.num_nodes }
    /// Read the fixed accepted cost.
    pub fn total_cost(&self) -> (cost: u64) ensures cost == self.total_cost_spec(),
    { self.inner.budget.allocated }
    /// Read the fixed unconsumed capacity.
    pub fn budget_remaining(&self) -> (remaining: u64)
        requires self.valid(), ensures remaining == self.remaining_spec(),
    { self.inner.budget.available() }
    /// Ask the retained Registry whether a node was accepted.
    pub fn contains(&self, node: u64) -> (present: bool)
        requires self.valid(),
        ensures present == crate::primitives::resource_registry::has_key(
            self.entries_spec(), self.entries_spec().len() as int, node),
    { self.inner.contains_exec(node) }
}

// ── capture (fold a whole acceptance sequence into a snapshot) ───────────

/// Build a finished snapshot by folding a sequence of (node, cost) requests
/// through the guarded `AcceptNode` action: a request is accepted iff it is a
/// fresh, valid node whose cost fits the remaining budget (exactly the TLA+
/// guards), otherwise it is skipped. The builder satisfies both invariants;
/// public capture consumes it into the sealed result. `nodes[i]` pairs with `costs[i]`.
#[expect(clippy::indexing_slicing, reason = "the required equal slice lengths and guarded request cursor bound both paired reads")]
#[expect(clippy::arithmetic_side_effects, reason = "the request cursor advances only while strictly below the nodes slice length")]
pub(crate) fn capture_builder(capacity: u64, num_nodes: u64, nodes: &[u64], costs: &[u64])
    -> (s: AllocationSnapshot)
    requires
        nodes@.len() == costs@.len(),
    ensures
        s.budget.capacity == capacity,
        s.num_nodes == num_nodes,
        s.registry.entries@ == capture_entries_to(
            capacity,
            num_nodes,
            nodes@,
            costs@,
            nodes@.len() as int,
        ),
        s.budget.allocated as int
            == cost_sum_to(s.registry.entries@, s.registry.entries@.len() as int),
        s.type_invariant(),
        s.budget_consistency(),
{
    let mut s = AllocationSnapshot::new(capacity, num_nodes);
    let n_reqs = nodes.len();
    let mut i: usize = 0;
    while i < n_reqs
        invariant
            i <= n_reqs,
            n_reqs == nodes@.len(),
            nodes@.len() == costs@.len(),
            s.budget.capacity == capacity,
            s.num_nodes == num_nodes,
            s.registry.entries@ == capture_entries_to(
                capacity,
                num_nodes,
                nodes@,
                costs@,
                i as int,
            ),
            s.type_invariant(),
            s.budget_consistency(),
        decreases n_reqs - i,
    {
        let n = nodes[i];
        let c = costs[i];
        let available = s.budget.available();
        if n < num_nodes && 1 <= c && c <= available && !s.contains_exec(n) {
            s.accept_node(n, c);
        }
        assert(s.registry.entries@ == capture_entries_to(
            capacity,
            num_nodes,
            nodes@,
            costs@,
            i as int + 1,
        ));
        i = i + 1;
    }
    s
}

/// Capture a finished allocation with immutable accepted membership and costs.
/// Invalid, duplicate, zero-cost and unaffordable requests are skipped by the
/// existing acceptance fold. The returned value exposes no admission action.
pub fn capture(capacity: u64, num_nodes: u64, nodes: &[u64], costs: &[u64])
    -> (captured: CapturedAllocationSnapshot)
    requires nodes@.len() == costs@.len(),
    ensures captured.valid(), captured.capacity_spec() == capacity,
        captured.num_nodes_spec() == num_nodes,
        captured.entries_spec() == capture_entries_to(
            capacity, num_nodes, nodes@, costs@, nodes@.len() as int),
        captured.total_cost_spec() as int == cost_sum_to(
            captured.entries_spec(), captured.entries_spec().len() as int),
{
    capture_builder(capacity, num_nodes, nodes, costs).seal()
}

/// Pure domain validation of a key, owned payload and declared resource charges.
/// The shared profile separately enforces unique membership and every capacity.
pub trait AllocationDomain<K, V> {
    /// The immutable domain's universe, payload and charge correspondence.
    spec fn admits(&self, key: K, value: V, charges: Seq<u64>) -> bool;
    /// Evaluate domain content without publishing or retaining admission state.
    fn admits_exec(&self, key: &K, value: &V, charges: &Vec<u64>) -> (admitted: bool)
        ensures admitted == self.admits(*key, *value, charges@);
}

/// Domain policy imposing no content constraints beyond shared admission guards.
#[derive(Clone, Copy, Debug)]
pub struct UnrestrictedAllocation;
impl<K, V> AllocationDomain<K, V> for UnrestrictedAllocation {
    open spec fn admits(&self, _key: K, _value: V, _charges: Seq<u64>) -> bool { true }
    fn admits_exec(&self, _key: &K, _value: &V, _charges: &Vec<u64>) -> (admitted: bool) { true }
}

/// Refusal before any typed membership or logical budget publication.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypedAllocationError {
    /// The fixed schema must contain a membership dimension.
    EmptySchema,
    /// The charge vector does not match the fixed schema.
    WidthMismatch,
    /// Dimension zero must charge exactly one membership unit.
    MembershipCharge,
    /// The logical identity already has a retained binding.
    DuplicateKey,
    /// The domain rejected its universe, payload or charge data.
    OutsideDomain,
    /// One existing Budget refused its declared charge.
    Capacity,
    /// Physical entry storage could not be reserved.
    StorageUnavailable,
}

/// Unconsumed admission data returned on refusal or cancellation.
pub struct RefusedTypedAdmission<K, V> {
    /// Exact preparation refusal, or None for cancellation.
    pub reason: Option<TypedAllocationError>,
    /// First refusing Budget position, present only for Capacity.
    pub dimension: Option<usize>,
    /// Original owned key, without cloning or replacement.
    pub key: K,
    /// Original owned payload, without cloning or replacement.
    pub value: V,
    /// Original owned charge data, without cloning or replacement.
    pub charges: Vec<u64>,
}

/// Mathematical charged total for one dimension of a retained entry prefix.
pub open spec fn typed_charge_to<K, V>(
    entries: Seq<(K, (V, Vec<u64>))>, end: int, dimension: int,
) -> int
    decreases end,
{
    if end <= 0 || end > entries.len() { 0 }
    else { typed_charge_to(entries, end - 1, dimension) + entries[end - 1].1.1@[dimension] as int }
}

proof fn typed_charge_push_prefix<K, V>(
    entries: Seq<(K, (V, Vec<u64>))>, entry: (K, (V, Vec<u64>)), end: int, dimension: int,
)
    requires 0 <= end <= entries.len(),
    ensures typed_charge_to(entries.push(entry), end, dimension) == typed_charge_to(entries, end, dimension),
    decreases end,
{
    if end > 0 { typed_charge_push_prefix(entries, entry, end - 1, dimension); }
}

proof fn typed_charge_push<K, V>(entries: Seq<(K, (V, Vec<u64>))>, entry: (K, (V, Vec<u64>)), dimension: int)
    ensures typed_charge_to(entries.push(entry), entries.len() as int + 1, dimension)
        == typed_charge_to(entries, entries.len() as int, dimension) + entry.1.1@[dimension] as int,
{
    typed_charge_push_prefix(entries, entry, entries.len() as int, dimension);
}

proof fn typed_charge_append<K, V>(left: Seq<(K, (V, Vec<u64>))>, right: Seq<(K, (V, Vec<u64>))>, end: int, dimension: int)
    requires 0 <= end <= right.len(),
    ensures typed_charge_to(left + right.subrange(0, end), (left.len() + end) as int, dimension)
        == typed_charge_to(left, left.len() as int, dimension) + typed_charge_to(right, end, dimension),
    decreases end,
{
    if end > 0 {
        typed_charge_append(left, right, end - 1, dimension);
        let prior = left + right.subrange(0, end - 1);
        assert(left + right.subrange(0, end) =~= prior.push(right[end - 1]));
        typed_charge_push(prior, right[end - 1], dimension);
    } else { assert(left + right.subrange(0, end) =~= left); }
}

proof fn typed_charge_monotone<K, V>(items: Seq<(K, (V, Vec<u64>))>, earlier: int, later: int, dimension: int)
    requires 0 <= earlier <= later <= items.len(),
    ensures 0 <= typed_charge_to(items, earlier, dimension) <= typed_charge_to(items, later, dimension),
    decreases later,
{
    if later > 0 {
        if earlier < later { typed_charge_monotone(items, earlier, later - 1, dimension); }
        else { typed_charge_monotone(items, earlier - 1, later - 1, dimension); }
    }
}

// Borrowed key content for the temporary preparation Registry. The retained
// payload and key stay in their original owned Buffer/Vec until every guard passes.
struct BorrowedAdmissionKey<'a, K: KeyIdentity> { key: &'a K }
impl<'a, K: KeyIdentity> KeyIdentity for BorrowedAdmissionKey<'a, K> {
    type Identity = K::Identity;
    closed spec fn identity(&self) -> K::Identity { self.key.identity() }
    fn key_equal(&self, other: &Self) -> (equal: bool) { self.key.key_equal(other.key) }
}

/// Exact charge shape; unit membership exists only in a budgeted profile.
pub open spec fn typed_member_charge(dimensions: int, charges: Seq<u64>) -> bool {
    charges.len() == dimensions && (dimensions == 0 || charges[0] == 1)
}

/// Every item in an authored prefix passes the shared content and identity guards.
pub open spec fn typed_batch_content<K: KeyIdentity, V, P: AllocationDomain<K, V>>(
    allocation: TypedAllocation<K,V,P>, items: Seq<(K,(V,Vec<u64>))>, end: int,
) -> bool {
    &&& 0 <= end <= items.len()
    &&& forall|entry: int| 0 <= entry < end ==> {
        let item = #[trigger] items[entry];
        &&& typed_member_charge(allocation.budgets_spec().len() as int, item.1.1@)
        &&& !allocation.contains_spec(item.0)
        &&& allocation.domain_spec().admits(item.0, item.1.0, item.1.1@)
    }
    &&& forall|left: int, right: int| 0 <= left < end && 0 <= right < end && left != right ==>
        #[trigger] items[left].0.identity() != #[trigger] items[right].0.identity()
}

/// The exact batch fits every unchanged actual Budget, including its membership dimension.
pub open spec fn typed_batch_admitted<K: KeyIdentity, V, P: AllocationDomain<K, V>>(
    allocation: TypedAllocation<K,V,P>, items: Seq<(K,(V,Vec<u64>))>, end: int,
) -> bool {
    &&& typed_batch_content(allocation, items, end)
    &&& forall|dimension: int| 0 <= dimension < allocation.budgets_spec().len() ==>
        #[trigger] allocation.budgets_spec()[dimension].1.allocated as int
            + typed_charge_to(items, end, dimension) <= allocation.budgets_spec()[dimension].1.capacity as int
}

/// Mathematical reason for a prepublication batch refusal.
pub open spec fn typed_batch_refusal<K: KeyIdentity, V, P: AllocationDomain<K,V>>(
    allocation: TypedAllocation<K,V,P>, items: Seq<(K,(V,Vec<u64>))>,
    reason: TypedAllocationError, entry: Option<usize>, dimension: Option<usize>,
) -> bool {
    if reason == TypedAllocationError::StorageUnavailable {
        entry == None && dimension == None
    } else {
        &&& entry is Some && entry.unwrap() < items.len()
        &&& typed_batch_admitted(allocation, items, entry.unwrap() as int)
        &&& match reason {
            TypedAllocationError::WidthMismatch => dimension == None
                && items[entry.unwrap() as int].1.1@.len() != allocation.budgets_spec().len(),
            TypedAllocationError::MembershipCharge => dimension == None
                && allocation.budgets_spec().len() > 0
                && items[entry.unwrap() as int].1.1@.len() == allocation.budgets_spec().len()
                && items[entry.unwrap() as int].1.1@[0] != 1,
            TypedAllocationError::DuplicateKey => dimension == None
                && (allocation.contains_spec(items[entry.unwrap() as int].0)
                    || exists|prior: int| 0 <= prior < entry.unwrap()
                        && (#[trigger] items[prior]).0.identity() == items[entry.unwrap() as int].0.identity()),
            TypedAllocationError::OutsideDomain => dimension == None
                && !allocation.domain_spec().admits(items[entry.unwrap() as int].0,
                    items[entry.unwrap() as int].1.0, items[entry.unwrap() as int].1.1@),
            TypedAllocationError::Capacity => dimension is Some
                && dimension.unwrap() < allocation.budgets_spec().len()
                && typed_batch_content(allocation, items, entry.unwrap() as int + 1)
                && typed_charge_to(items, entry.unwrap() as int + 1, dimension.unwrap() as int)
                    + allocation.budgets_spec()[dimension.unwrap() as int].1.allocated as int
                    > allocation.budgets_spec()[dimension.unwrap() as int].1.capacity as int
                && forall|d: int| 0 <= d < dimension.unwrap() ==>
                    #[trigger] allocation.budgets_spec()[d].1.allocated as int
                        + typed_charge_to(items, entry.unwrap() as int + 1, d)
                            <= allocation.budgets_spec()[d].1.capacity as int,
            _ => false,
        }
    }
}

/// Exact owned batch returned before any membership or Budget publication.
pub struct RefusedTypedBatch<K, V> {
    /// Preparation refusal, or None for cancellation.
    pub reason: Option<TypedAllocationError>,
    /// Authored item position when an item guard refused; None for storage refusal.
    pub entry: Option<usize>,
    /// First refusing resource dimension for a capacity refusal.
    pub dimension: Option<usize>,
    /// Original keys, payloads and charge vectors, without cloning or reordering.
    pub items: Vec<(K, (V, Vec<u64>))>,
}

/// One-use, exclusive preparation of the complete authored batch.
pub struct PreparedTypedBatch<'a, K: KeyIdentity, V, P: AllocationDomain<K,V>> {
    allocation: &'a mut TypedAllocation<K,V,P>,
    pending: Buffer<(K,(V,Vec<u64>))>,
}

/// Mathematical payload correspondence in the retained Registry representation.
pub open spec fn typed_payload_matches<K: KeyIdentity, V>(
    entries: Seq<(K, (V, Vec<u64>))>, key: K, value: V,
) -> bool {
    typed_identity_payload_matches(entries, key.identity(), value)
}

/// Payload correspondence using the retained key domain's borrowed identity.
pub open spec fn typed_identity_payload_matches<K: KeyIdentity, V>(
    entries: Seq<(K, (V, Vec<u64>))>, identity: K::Identity, value: V,
) -> bool {
    exists|entry: int| 0 <= entry < entries.len()
        && entries[entry].0.identity() == identity && entries[entry].1.0 == value
}

/// Typed AllocationSnapshot profile with unique membership and fixed scoped Budgets.
/// In the budgeted profile, dimension zero counts members and remaining charges
/// use declared domain units, including zero resource costs. The unbudgeted
/// profile has no resource dimensions or membership quota. Physical allocator
/// limits are separate in both profiles.
///
/// ```rust
/// use automation_structures::{TypedAllocation, UnrestrictedAllocation};
/// let mut allocation = TypedAllocation::try_new(&vec![2, 8], UnrestrictedAllocation)?;
/// allocation.prepare(7u64, vec![3u8], vec![1, 1])?.commit();
/// assert_eq!(allocation.budget(1), Some((8, 1)));
/// let sealed = allocation.seal();
/// assert_eq!(sealed.get(&7), Some(&vec![3u8]));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct TypedAllocation<K: KeyIdentity, V, P: AllocationDomain<K, V> = UnrestrictedAllocation> {
    entries: ResourceRegistry<K, (V, Vec<u64>)>,
    budgets: ResourceRegistry<usize, Budget>,
    domain: P,
}

impl<K: KeyIdentity, V, P: AllocationDomain<K, V>> TypedAllocation<K, V, P> {
    // Shared ordered content guard; both single and batch entry paths use it.
    #[expect(clippy::indexing_slicing, reason = "the width and nonempty schema guards prove charges[0] exists")]
    fn check_content(&self, key: &K, value: &V, charges: &Vec<u64>) -> (result: Result<(), TypedAllocationError>)
        requires self.inv(),
        ensures result is Ok <==> typed_member_charge(self.budgets_spec().len() as int, charges@)
            && !self.contains_spec(*key) && self.domain_spec().admits(*key, *value, charges@),
            result is Err ==> match result.unwrap_err() {
                TypedAllocationError::WidthMismatch => charges@.len() != self.budgets_spec().len(),
                TypedAllocationError::MembershipCharge => self.budgets_spec().len() > 0
                    && charges@.len() == self.budgets_spec().len() && charges@[0] != 1,
                TypedAllocationError::DuplicateKey => typed_member_charge(self.budgets_spec().len() as int, charges@)
                    && self.contains_spec(*key),
                TypedAllocationError::OutsideDomain => typed_member_charge(self.budgets_spec().len() as int, charges@)
                    && !self.contains_spec(*key) && !self.domain_spec().admits(*key, *value, charges@),
                _ => false,
            },
    {
        if charges.len() != self.budgets.entries.len() { return Err(TypedAllocationError::WidthMismatch); }
        if !self.budgets.entries.is_empty() && charges[0] != 1 { return Err(TypedAllocationError::MembershipCharge); }
        if self.entries.lookup_key_ref(key).is_some() { return Err(TypedAllocationError::DuplicateKey); }
        if !self.domain.admits_exec(key, value, charges) { return Err(TypedAllocationError::OutsideDomain); }
        Ok(())
    }

    // Only preparation owners change here. The actual accepted owners are borrowed
    // immutably until every item, identity, dimension and physical reservation passes.
    #[expect(clippy::indexing_slicing, reason = "the pending Registry prefix bounds each item and checked charge width equals the guarded Budget dimension universe")]
    #[expect(clippy::arithmetic_side_effects, reason = "both schema Cursors advance only while below the fixed dimension count")]
    fn check_batch(&self, items: &Vec<(K,(V,Vec<u64>))>)
        -> (result: Result<(), (TypedAllocationError, Option<usize>, Option<usize>)>)
        requires self.inv(),
        ensures result is Ok ==> typed_batch_admitted(*self, items@, items@.len() as int),
            result is Err ==> typed_batch_refusal(*self, items@,
                result.unwrap_err().0, result.unwrap_err().1, result.unwrap_err().2),
    {
        if items.is_empty() { return Ok(()); }
        let dimensions = self.budgets.entries.len();
        let mut operators = match Buffer::try_new(dimensions) {
            Ok(buffer) => buffer,
            Err(_) => return Err((TypedAllocationError::StorageUnavailable, None, None)),
        };
        let mut schema = Cursor::new(0);
        while schema.position < dimensions
            invariant schema.position <= dimensions, dimensions == self.budgets_spec().len(),
                operators.well_formed(), operators.capacity == dimensions,
                operators.values@.len() == schema.position,
                forall|d: int| 0 <= d < schema.position ==> #[trigger] operators.values@[d] == AdditiveChain,
            decreases dimensions - schema.position,
        {
            let _accepted = operators.push(AdditiveChain); assert(_accepted is Ok);
            schema.advance_to(schema.position + 1);
        }
        let mut totals = match ReductionColumns::try_new(&operators.values, items.len()) {
            Ok(columns) => columns,
            Err(_) => return Err((TypedAllocationError::StorageUnavailable, None, None)),
        };
        let mut pending = ResourceRegistry::<BorrowedAdmissionKey<K>, ()>::new();
        if pending.try_reserve_entries(items.len()).is_err() {
            return Err((TypedAllocationError::StorageUnavailable, None, None));
        }
        while pending.entries.len() < items.len()
            invariant self.inv(), dimensions == self.budgets_spec().len(),
                totals.inv(), totals.columns_spec().len() == dimensions,
                pending.unique_identities(), pending.entries@.len() <= items.len(),
                typed_batch_admitted(*self, items@, pending.entries@.len() as int),
                forall|entry: int| 0 <= entry < pending.entries@.len() ==>
                    #[trigger] pending.entries@[entry].0.identity() == items@[entry].0.identity(),
                forall|d: int| 0 <= d < dimensions ==> {
                    let column = (#[trigger] totals.columns_spec()[d]).1;
                    &&& column.operator_spec() == AdditiveChain
                    &&& column.processed_spec() == pending.entries@.len()
                    &&& column.limit_spec() == items.len()
                    &&& column.result_spec() as int == typed_charge_to(items@, column.processed_spec() as int, d)
                },
            decreases items.len() - pending.entries@.len(),
        {
            let position = pending.entries.len();
            let item = &items[position];
            if let Err(reason) = self.check_content(&item.0, &item.1.0, &item.1.1) {
                return Err((reason, Some(position), None));
            }
            let key = BorrowedAdmissionKey { key: &item.0 };
            if pending.lookup_key_ref(&key).is_some() {
                proof {
                    let projected = crate::primitives::resource_registry::identity_entries(pending.entries@);
                    let prior = choose|prior: int| 0 <= prior < projected.len() && projected[prior].0 == key.identity();
                    crate::primitives::resource_registry::identity_entry_at(pending.entries@, prior);
                    assert(items@[prior].0.identity() == items@[position as int].0.identity());
                }
                return Err((TypedAllocationError::DuplicateKey, Some(position), None));
            }
            proof {
                assert forall|prior: int| 0 <= prior < position implies
                    (#[trigger] items@[prior]).0.identity() != items@[position as int].0.identity() by {
                    crate::primitives::resource_registry::identity_entry_at(pending.entries@, prior);
                    if items@[prior].0.identity() == key.identity() {
                        assert(pending.contains_key_identity(key));
                        assert(false);
                    }
                }
                assert(typed_batch_content(*self, items@, position as int + 1));
            }
            let mut schema = Cursor::new(0);
            while schema.position < dimensions
                invariant self.inv(), dimensions == self.budgets_spec().len(),
                    position < items.len(), typed_batch_admitted(*self, items@, position as int),
                    typed_batch_content(*self, items@, position as int + 1),
                    totals.inv(), totals.columns_spec().len() == dimensions,
                    *item == items@[position as int], item.1.1@.len() == dimensions,
                    schema.position <= dimensions,
                    forall|d: int| 0 <= d < dimensions ==>
                        (#[trigger] totals.columns_spec()[d]).1.result_spec() as int == typed_charge_to(items@, position as int, d)
                        && totals.columns_spec()[d].1.operator_spec() == AdditiveChain
                        && totals.columns_spec()[d].1.processed_spec() == position
                        && totals.columns_spec()[d].1.limit_spec() == items.len(),
                    forall|d: int| 0 <= d < schema.position ==>
                        #[trigger] self.budgets_spec()[d].1.allocated as int
                            + typed_charge_to(items@, position as int + 1, d) <= self.budgets_spec()[d].1.capacity as int,
                decreases dimensions - schema.position,
            {
                let dimension = schema.position;
                let total = match totals.column_result(dimension) {
                    Some(total) => total,
                    None => { proof { assert(false); } return Err((TypedAllocationError::StorageUnavailable, None, None)); },
                };
                if !self.budgets.entries[dimension].1.admits_additional(total, item.1.1[dimension]) {
                    return Err((TypedAllocationError::Capacity, Some(position), Some(dimension)));
                }
                schema.advance_to(dimension + 1);
            }
            let ghost before_columns = totals.columns_spec();
            proof {
                assert forall|d: int| 0 <= d < dimensions implies
                    (#[trigger] before_columns[d]).1.processed_spec() < before_columns[d].1.limit_spec()
                    && before_columns[d].1.operator_spec().accepts(before_columns[d].1.result_spec(), item.1.1@[d]) by {
                    assert(before_columns[d].1.result_spec() as int + item.1.1@[d] as int
                        == typed_charge_to(items@, position as int + 1, d));
                    assert(typed_charge_to(items@, position as int + 1, d)
                        <= self.budgets_spec()[d].1.capacity as int);
                }
            }
            match totals.prepare_row(&item.1.1) {
                Ok(row) => row.commit(),
                Err(ReductionRowError::StorageUnavailable) => return Err((TypedAllocationError::StorageUnavailable, None, None)),
                Err(_) => { assert(false); return Err((TypedAllocationError::StorageUnavailable, None, None)); },
            }
            pending.register_key(key, ());
            proof {
                assert forall|d: int| 0 <= d < dimensions implies
                    totals.columns_spec()[d].1.result_spec() as int == typed_charge_to(items@, position as int + 1, d) by {
                    assert(totals.columns_spec()[d].1.result_spec() == AdditiveChain.combined(
                        before_columns[d].1.result_spec(), item.1.1@[d]));
                }
                assert(typed_batch_admitted(*self, items@, position as int + 1));
            }
        }
        Ok(())
    }

    /// Prepare the complete owned batch before publishing any key or charge.
    /// Each item is `(key, (payload, charges))` in authored order. Budgeted
    /// allocations charge one member in dimension zero; unbudgeted allocations
    /// require empty charges. All refusals return the original owned vector.
    ///
    /// # Errors
    /// Returns the first authored content/identity/capacity refusal, or storage
    /// refusal before commit. Logical membership and all Budget owners remain fixed.
    pub fn prepare_batch<'a>(&'a mut self, items: Vec<(K,(V,Vec<u64>))>)
        -> (result: Result<PreparedTypedBatch<'a,K,V,P>, RefusedTypedBatch<K,V>>)
        requires old(self).inv(),
        ensures match result {
            Ok(prepared) => prepared.inv() && prepared.before_spec().entries_spec() == old(self).entries_spec()
                && prepared.before_spec().budgets_spec() == old(self).budgets_spec()
                && prepared.before_spec().domain_spec() == old(self).domain_spec()
                && prepared.items_spec() == items@
                && typed_batch_admitted(*old(self), items@, items@.len() as int)
                && *final(self) == prepared.after_spec(),
            Err(refused) => refused.items == items && refused.reason is Some
                && typed_batch_refusal(*old(self), items@, refused.reason.unwrap(), refused.entry, refused.dimension)
                && final(self).inv() && final(self).entries_spec() == old(self).entries_spec()
                && final(self).budgets_spec() == old(self).budgets_spec()
                && final(self).domain_spec() == old(self).domain_spec(),
        },
    {
        if let Err((reason, entry, dimension)) = self.check_batch(&items) {
            return Err(RefusedTypedBatch { reason: Some(reason), entry, dimension, items });
        }
        if self.entries.try_reserve_entries(items.len()).is_err() {
            return Err(RefusedTypedBatch { reason: Some(TypedAllocationError::StorageUnavailable), entry: None, dimension: None, items });
        }
        Ok(PreparedTypedBatch { allocation: self, pending: Buffer::from_values(items) })
    }
    /// Retained unique membership, payload and charge data in authored order.
    pub closed spec fn entries_spec(&self) -> Seq<(K, (V, Vec<u64>))> { self.entries.entries@ }
    /// Actual scoped Budget owners in fixed dimension order.
    pub closed spec fn budgets_spec(&self) -> Seq<(usize, Budget)> { self.budgets.entries@ }
    /// Immutable domain policy bound to this allocation.
    pub closed spec fn domain_spec(&self) -> P { self.domain }
    /// Membership at one exact logical key identity.
    pub open spec fn contains_spec(&self, key: K) -> bool {
        crate::primitives::resource_registry::has_key(
            crate::primitives::resource_registry::identity_entries(self.entries_spec()),
            self.entries_spec().len() as int, key.identity())
    }
    /// Retained payload correspondence at one exact logical identity.
    pub open spec fn maps_payload(&self, key: K, value: V) -> bool {
        typed_payload_matches(self.entries_spec(), key, value)
    }
    /// Every retained charge is coupled to its sole Budget owner.
    pub closed spec fn inv(&self) -> bool {
        &&& self.entries.unique_identities()
        &&& self.budgets.unique_identities()
        &&& forall|entry: int| 0 <= entry < self.entries.entries@.len() ==> {
            let retained = #[trigger] self.entries.entries@[entry];
            &&& typed_member_charge(self.budgets.entries@.len() as int, retained.1.1@)
            &&& self.domain.admits(retained.0, retained.1.0, retained.1.1@)
        }
        &&& forall|dimension: int| 0 <= dimension < self.budgets.entries@.len() ==> {
            let scoped = #[trigger] self.budgets.entries@[dimension];
            &&& scoped.0 == dimension
            &&& scoped.1.safety_invariant()
            &&& scoped.1.reserved == 0 && scoped.1.pending_eviction == 0
            &&& scoped.1.allocated as int == typed_charge_to(self.entries.entries@,
                self.entries.entries@.len() as int, dimension)
        }
    }

    /// Construct unique typed membership without a resource or route-slot quota.
    /// Every admission uses an empty charge vector. Registry storage is reserved
    /// fallibly during preparation, before any membership publication.
    pub fn unbudgeted(domain: P) -> (allocation: Self)
        ensures allocation.inv(), allocation.entries_spec().len() == 0,
            allocation.budgets_spec().len() == 0, allocation.domain_spec() == domain,
    { Self { entries: ResourceRegistry::new(), budgets: ResourceRegistry::new(), domain } }

    /// Reserve only the fixed Budget schema; the member Registry begins empty.
    ///
    /// # Errors
    /// Refuses an empty schema or its physical owner-storage reservation.
    #[expect(clippy::indexing_slicing, reason = "the schema Cursor is guarded by capacities.len() before each capacity read")]
    #[expect(clippy::arithmetic_side_effects, reason = "the schema Cursor advances only while strictly below capacities.len()")]
    pub fn try_new(capacities: &Vec<u64>, domain: P) -> (result: Result<Self, TypedAllocationError>)
        ensures result is Ok ==> result.unwrap().inv() && result.unwrap().entries_spec().len() == 0
            && result.unwrap().domain_spec() == domain
            && result.unwrap().budgets_spec().len() == capacities@.len()
            && forall|dimension: int| 0 <= dimension < capacities@.len() ==>
                #[trigger] result.unwrap().budgets_spec()[dimension].1.capacity == capacities@[dimension]
                && result.unwrap().budgets_spec()[dimension].1.allocated == 0,
            (result matches Err(TypedAllocationError::EmptySchema)) == (capacities@.len() == 0),
            result is Err ==> result == Err(TypedAllocationError::EmptySchema)
                || result == Err(TypedAllocationError::StorageUnavailable),
    {
        if capacities.is_empty() { return Err(TypedAllocationError::EmptySchema); }
        let mut budgets = ResourceRegistry::<usize, Budget>::new();
        if budgets.try_reserve_entries(capacities.len()).is_err() { return Err(TypedAllocationError::StorageUnavailable); }
        let mut cursor = Cursor::new(0);
        while cursor.position < capacities.len()
            invariant cursor.position <= capacities@.len(), budgets.unique_identities(),
                budgets.entries@.len() == cursor.position,
                forall|dimension: int| 0 <= dimension < cursor.position ==> {
                    let scoped = #[trigger] budgets.entries@[dimension];
                    &&& scoped.0 == dimension && scoped.1.capacity == capacities@[dimension]
                    &&& scoped.1.safety_invariant() && scoped.1.allocated == 0
                    &&& scoped.1.reserved == 0 && scoped.1.pending_eviction == 0
                },
            decreases capacities.len() - cursor.position,
        {
            let dimension = cursor.position;
            assert(!budgets.contains_key_identity(dimension));
            budgets.register_key(dimension, Budget::new(capacities[dimension]));
            cursor.advance_to(dimension + 1);
        }
        Ok(Self { entries: ResourceRegistry::new(), budgets, domain })
    }

    /// Read the member Registry's retained length.
    pub fn len(&self) -> (length: usize)
        requires self.inv(), ensures length == self.entries_spec().len(),
    { self.entries.entries.len() }
    /// Whether this allocation has no admitted members.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.inv(), ensures empty == (self.entries_spec().len() == 0),
    { self.entries.entries.is_empty() }
    /// Read the fixed schema length without a copied resource ledger.
    pub fn dimension_count(&self) -> (length: usize)
        requires self.inv(), ensures length == self.budgets_spec().len(),
    { self.budgets.entries.len() }
    /// Observe one actual Budget's fixed capacity and committed charge.
    #[expect(clippy::indexing_slicing, reason = "the runtime dimension guard checks the retained Budget Registry length")]
    pub fn budget(&self, dimension: usize) -> (observation: Option<(u64, u64)>)
        requires self.inv(),
        ensures observation == if dimension < self.budgets_spec().len() {
            Some((self.budgets_spec()[dimension as int].1.capacity, self.budgets_spec()[dimension as int].1.allocated))
        } else { None },
    {
        if dimension < self.budgets.entries.len() {
            let scoped = &self.budgets.entries[dimension].1;
            Some((scoped.capacity, scoped.allocated))
        } else { None }
    }
    /// Borrow the owned payload at its exact logical identity.
    pub fn get<'a>(&'a self, key: &K) -> (value: Option<&'a V>)
        requires self.inv(),
        ensures value is None ==> !self.contains_spec(*key),
            value matches Some(value) ==> self.maps_payload(*key, *value),
    { self.get_query(key) }

    /// Borrow an admitted payload without allocating a retained-key representation.
    pub fn get_query<'a, Q: RegistryQuery<K>>(&'a self, query: &Q) -> (value: Option<&'a V>)
        requires self.inv(),
        ensures value is None ==> !crate::primitives::resource_registry::has_key(
            crate::primitives::resource_registry::identity_entries(self.entries_spec()),
            self.entries_spec().len() as int, query.query_identity()),
            value matches Some(value) ==> typed_identity_payload_matches(
                self.entries_spec(), query.query_identity(), *value),
    {
        match self.entries.lookup_query(query) {
            Some(retained) => {
                proof {
                    let projected = crate::primitives::resource_registry::identity_entries(self.entries.entries@);
                    assert(projected.len() == self.entries.entries@.len());
                    let entry = choose|entry: int| 0 <= entry < projected.len()
                        && projected[entry].0 == query.query_identity() && projected[entry].1 == *retained;
                    crate::primitives::resource_registry::identity_entry_at(self.entries.entries@, entry);
                    assert(self.entries_spec()[entry].0.identity() == query.query_identity()
                        && self.entries_spec()[entry].1.0 == retained.0);
                    assert(typed_identity_payload_matches(self.entries_spec(), query.query_identity(), retained.0));
                }
                Some(&retained.0)
            },
            None => None,
        }
    }

    /// Consume admission authority; membership, costs and Budget owners cannot reopen.
    /// This does not deeply freeze arbitrary interior-mutable payload data.
    pub fn seal(self) -> (sealed: SealedTypedAllocation<K, V, P>)
        requires self.inv(),
        ensures sealed.inv(), sealed.entries_spec() == self.entries_spec(),
            sealed.budgets_spec() == self.budgets_spec(),
    { SealedTypedAllocation { inner: self } }

    /// Check every logical guard and reserve entry storage before publication.
    ///
    /// # Errors
    /// Returns the exact owned input and unchanged membership/Budget observations.
    /// A failed reservation may retain physical spare capacity only.
    #[expect(clippy::indexing_slicing, reason = "check_content establishes charge width equal to the Budget Registry and the dimension Cursor guards each paired access")]
    #[expect(clippy::arithmetic_side_effects, reason = "the dimension Cursor advances only while strictly below the admitted charge width")]
    pub fn prepare<'a>(&'a mut self, key: K, value: V, charges: Vec<u64>)
        -> (result: Result<PreparedTypedAdmission<'a, K, V, P>, RefusedTypedAdmission<K, V>>)
        requires old(self).inv(),
        ensures match result {
            Ok(prepared) => prepared.inv()
                && prepared.before_spec().entries_spec() == old(self).entries_spec()
                && prepared.before_spec().budgets_spec() == old(self).budgets_spec()
                && prepared.before_spec().domain_spec() == old(self).domain_spec()
                && prepared.key_spec() == key && prepared.value_spec() == value && prepared.charges_spec() == charges@
                && typed_member_charge(old(self).budgets_spec().len() as int, charges@)
                && !old(self).contains_spec(key) && old(self).domain_spec().admits(key, value, charges@)
                && (forall|dimension: int|
                    #![trigger old(self).budgets_spec()[dimension]] #![trigger charges@[dimension]]
                    0 <= dimension < charges@.len() ==> charges@[dimension] as int
                        + old(self).budgets_spec()[dimension].1.allocated as int
                            <= old(self).budgets_spec()[dimension].1.capacity as int)
                && *final(self) == prepared.after_spec(),
            Err(refused) => refused.key == key && refused.value == value && refused.charges == charges
                && final(self).inv() && final(self).entries_spec() == old(self).entries_spec()
                && final(self).budgets_spec() == old(self).budgets_spec()
                && final(self).domain_spec() == old(self).domain_spec()
                && match refused.reason {
                    Some(TypedAllocationError::WidthMismatch) => charges@.len() != old(self).budgets_spec().len()
                        && refused.dimension == None,
                    Some(TypedAllocationError::MembershipCharge) => charges@.len() == old(self).budgets_spec().len()
                        && old(self).budgets_spec().len() > 0 && charges@[0] != 1 && refused.dimension == None,
                    Some(TypedAllocationError::DuplicateKey) => typed_member_charge(old(self).budgets_spec().len() as int, charges@)
                        && old(self).contains_spec(key) && refused.dimension == None,
                    Some(TypedAllocationError::OutsideDomain) => typed_member_charge(old(self).budgets_spec().len() as int, charges@)
                        && !old(self).contains_spec(key)
                        && !old(self).domain_spec().admits(key, value, charges@) && refused.dimension == None,
                    Some(TypedAllocationError::Capacity) => refused.dimension is Some
                        && typed_member_charge(old(self).budgets_spec().len() as int, charges@)
                        && !old(self).contains_spec(key) && old(self).domain_spec().admits(key, value, charges@)
                        && refused.dimension.unwrap() < charges@.len()
                        && charges@[refused.dimension.unwrap() as int] as int
                            + old(self).budgets_spec()[refused.dimension.unwrap() as int].1.allocated as int
                            > old(self).budgets_spec()[refused.dimension.unwrap() as int].1.capacity as int
                        && forall|dimension: int|
                            #![trigger old(self).budgets_spec()[dimension]] #![trigger charges@[dimension]]
                            0 <= dimension < refused.dimension.unwrap() ==>
                            charges@[dimension] as int + old(self).budgets_spec()[dimension].1.allocated as int
                                <= old(self).budgets_spec()[dimension].1.capacity as int,
                    Some(TypedAllocationError::StorageUnavailable) => typed_member_charge(old(self).budgets_spec().len() as int, charges@)
                        && !old(self).contains_spec(key)
                        && old(self).domain_spec().admits(key, value, charges@) && refused.dimension == None
                        && forall|dimension: int|
                            #![trigger old(self).budgets_spec()[dimension]] #![trigger charges@[dimension]]
                            0 <= dimension < charges@.len() ==>
                            charges@[dimension] as int + old(self).budgets_spec()[dimension].1.allocated as int
                                <= old(self).budgets_spec()[dimension].1.capacity as int,
                    _ => false,
                },
        },
    {
        if let Err(reason) = self.check_content(&key, &value, &charges) {
            return Err(RefusedTypedAdmission { reason: Some(reason), dimension: None, key, value, charges });
        }
        let mut cursor = Cursor::new(0);
        while cursor.position < charges.len()
            invariant self.inv(), typed_member_charge(self.budgets.entries@.len() as int, charges@),
                cursor.position <= charges@.len(),
                !self.entries.contains_key_identity(key), self.domain.admits(key, value, charges@),
                forall|dimension: int| 0 <= dimension < cursor.position ==>
                    #[trigger] charges@[dimension] as int + self.budgets.entries@[dimension].1.allocated as int
                        <= self.budgets.entries@[dimension].1.capacity as int,
            decreases charges.len() - cursor.position,
        {
            let dimension = cursor.position;
            if charges[dimension] > self.budgets.entries[dimension].1.available() {
                return Err(RefusedTypedAdmission { reason: Some(TypedAllocationError::Capacity), dimension: Some(dimension), key, value, charges });
            }
            cursor.advance_to(dimension + 1);
        }
        if self.entries.try_reserve_entries(1).is_err() {
            return Err(RefusedTypedAdmission { reason: Some(TypedAllocationError::StorageUnavailable), dimension: None, key, value, charges });
        }
        Ok(PreparedTypedAdmission { allocation: self, key, value, charges })
    }
}

impl<'a,K: KeyIdentity,V,P: AllocationDomain<K,V>> PreparedTypedBatch<'a,K,V,P> {
    /// All content/identity guards and exact batch charges pass against the unchanged owner.
    pub closed spec fn inv(&self) -> bool {
        self.allocation.inv() && self.pending.well_formed()
            && typed_batch_admitted(*self.allocation, self.pending.values@, self.pending.values@.len() as int)
    }
    /// Actual accepted owners before this preparation is resolved.
    pub closed spec fn before_spec(&self) -> TypedAllocation<K,V,P> { *self.allocation }
    /// Actual accepted owners after the exclusive preparation is resolved.
    #[verifier::prophetic]
    pub closed spec fn after_spec(&self) -> TypedAllocation<K,V,P> { *final(self.allocation) }
    /// The original owned entries, in authored order.
    pub closed spec fn items_spec(&self) -> Seq<(K,(V,Vec<u64>))> { self.pending.values@ }

    /// Return the exact original vector without changing any logical owner.
    pub fn cancel(self) -> (returned: RefusedTypedBatch<K,V>)
        requires self.inv(),
        ensures self.after_spec().entries_spec() == self.before_spec().entries_spec()
            && self.after_spec().budgets_spec() == self.before_spec().budgets_spec()
            && self.after_spec().domain_spec() == self.before_spec().domain_spec()
            && returned.reason == None && returned.entry == None && returned.dimension == None
            && returned.items@ == self.items_spec(),
    { RefusedTypedBatch { reason: None, entry: None, dimension: None, items: self.pending.values } }

    /// Transfer every original entry through the existing one-entry commit action.
    /// All fallible storage/domain checks precede this call; no commit allocates,
    /// invokes the domain, clones a key or payload, or shifts a retained suffix.
    #[expect(clippy::arithmetic_side_effects, reason = "the owned-batch Cursor advances only while below the retained length certified by its iterator binding")]
    pub fn commit(self)
        requires self.inv(),
        ensures self.after_spec().inv(),
            self.after_spec().entries_spec() == self.before_spec().entries_spec() + self.items_spec(),
            self.after_spec().domain_spec() == self.before_spec().domain_spec(),
            self.after_spec().budgets_spec().len() == self.before_spec().budgets_spec().len(),
            forall|dimension: int|
                #![trigger self.after_spec().budgets_spec()[dimension]] #![trigger self.before_spec().budgets_spec()[dimension]]
                0 <= dimension < self.before_spec().budgets_spec().len() ==>
                self.after_spec().budgets_spec()[dimension].1.capacity
                    == self.before_spec().budgets_spec()[dimension].1.capacity
                && self.after_spec().budgets_spec()[dimension].0 == self.before_spec().budgets_spec()[dimension].0
                && self.after_spec().budgets_spec()[dimension].1.reserved == self.before_spec().budgets_spec()[dimension].1.reserved
                && self.after_spec().budgets_spec()[dimension].1.pending_eviction == self.before_spec().budgets_spec()[dimension].1.pending_eviction
                && self.after_spec().budgets_spec()[dimension].1.allocated as int
                    == self.before_spec().budgets_spec()[dimension].1.allocated as int
                        + typed_charge_to(self.items_spec(), self.items_spec().len() as int, dimension),
    {
        let allocation = self.allocation;
        let ghost before = *allocation;
        let pending = self.pending;
        let ghost items = pending.values@;
        let length = pending.len();
        let mut transfer = pending.into_transfer();
        let mut cursor = Cursor::new(0);
        while cursor.position < length
            invariant allocation.inv(), length == items.len(), cursor.position <= length,
                vstd::std_specs::iter::IteratorSpec::remaining(&transfer) == items.skip(cursor.position as int),
                vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(&transfer),
                before.inv(), typed_batch_admitted(before, items, items.len() as int),
                allocation.entries_spec() == before.entries_spec() + items.take(cursor.position as int),
                allocation.domain_spec() == before.domain_spec(),
                allocation.budgets_spec().len() == before.budgets_spec().len(),
                forall|d: int| 0 <= d < before.budgets_spec().len() ==>
                    #[trigger] allocation.budgets_spec()[d].1.capacity == before.budgets_spec()[d].1.capacity
                    && allocation.budgets_spec()[d].1.allocated as int == before.budgets_spec()[d].1.allocated as int
                        + typed_charge_to(items, cursor.position as int, d),
            decreases length - cursor.position,
        {
            let position = cursor.position;
            let entry = match crate::connectives::buffer::advance_owned_transfer(&mut transfer) {
                Some(entry) => entry,
                None => { proof { assert(false); } return; },
            };
            assert(entry == items[position as int]);
            let (key, (value, charges)) = entry;
            proof {
                if allocation.contains_spec(key) {
                    let projected = crate::primitives::resource_registry::identity_entries(allocation.entries_spec());
                    let index = choose|index: int| 0 <= index < projected.len() && projected[index].0 == key.identity();
                    crate::primitives::resource_registry::identity_entry_at(allocation.entries_spec(), index);
                    if index < before.entries_spec().len() {
                        crate::primitives::resource_registry::identity_entry_at(before.entries_spec(), index);
                        assert(before.contains_spec(key));
                        assert(false);
                    } else {
                        let prior = index - before.entries_spec().len();
                        assert(0 <= prior < position);
                        assert(items[prior].0.identity() == items[position as int].0.identity());
                        assert(false);
                    }
                }
                assert forall|d: int| 0 <= d < charges@.len() implies
                    #[trigger] charges@[d] as int + allocation.budgets_spec()[d].1.allocated as int
                        <= allocation.budgets_spec()[d].1.capacity as int by {
                    typed_charge_monotone(items, position as int + 1, items.len() as int, d);
                    assert(typed_charge_to(items, position as int + 1, d)
                        == typed_charge_to(items, position as int, d) + charges@[d] as int);
                }
            }
            let ghost previous = allocation.entries_spec();
            let prepared = PreparedTypedAdmission { allocation, key, value, charges };
            assert(prepared.inv());
            prepared.commit();
            proof {
                assert(allocation.entries_spec() == previous.push(entry));
                assert(previous.push(entry) =~= before.entries_spec() + items.take(position as int + 1));
            }
            cursor.advance_to(position + 1);
        }
        assert(items.take(length as int) == items);
    }
}

/// One admitted owned entry exclusively borrowing its actual Registry/Budget owners.
/// Cancellation or drop changes no logical mapping or charge. Commit consumes it.
pub struct PreparedTypedAdmission<'a, K: KeyIdentity, V, P: AllocationDomain<K, V>> {
    allocation: &'a mut TypedAllocation<K, V, P>,
    key: K,
    value: V,
    charges: Vec<u64>,
}

impl<'a, K: KeyIdentity, V, P: AllocationDomain<K, V>> PreparedTypedAdmission<'a, K, V, P> {
    /// All coupled guards hold over this exclusive unchanged owner.
    pub closed spec fn inv(&self) -> bool {
        &&& self.allocation.inv()
        &&& typed_member_charge(self.allocation.budgets.entries@.len() as int, self.charges@)
        &&& !self.allocation.entries.contains_key_identity(self.key)
        &&& self.allocation.domain.admits(self.key, self.value, self.charges@)
        &&& forall|dimension: int| 0 <= dimension < self.charges@.len() ==>
            #[trigger] self.charges@[dimension] as int + self.allocation.budgets.entries@[dimension].1.allocated as int
                <= self.allocation.budgets.entries@[dimension].1.capacity as int
    }
    /// Owner at the preparation boundary.
    pub closed spec fn before_spec(&self) -> TypedAllocation<K, V, P> { *self.allocation }
    /// Owner when this exclusive borrow is resolved.
    #[verifier::prophetic]
    pub closed spec fn after_spec(&self) -> TypedAllocation<K, V, P> { *final(self.allocation) }
    /// Exact unconsumed key.
    pub closed spec fn key_spec(&self) -> K { self.key }
    /// Exact unconsumed owned payload.
    pub closed spec fn value_spec(&self) -> V { self.value }
    /// Exact declared dimension charges.
    pub closed spec fn charges_spec(&self) -> Seq<u64> { self.charges@ }
    /// Owned charge representation, visible only to the proof contract.
    pub closed spec fn charge_data_spec(&self) -> Vec<u64> { self.charges }

    /// Return the original input without any logical owner action.
    pub fn cancel(self) -> (returned: RefusedTypedAdmission<K, V>)
        requires self.inv(),
        ensures self.after_spec().entries_spec() == self.before_spec().entries_spec()
            && self.after_spec().budgets_spec() == self.before_spec().budgets_spec()
            && self.after_spec().domain_spec() == self.before_spec().domain_spec()
            && returned.reason == None && returned.dimension == None
            && returned.key == self.key_spec() && returned.value == self.value_spec()
            && returned.charges@ == self.charges_spec(),
    { RefusedTypedAdmission { reason: None, dimension: None, key: self.key, value: self.value, charges: self.charges } }

    /// Publish the existing Budget actions and unique Register once, without allocation.
    #[expect(clippy::indexing_slicing, reason = "the prepared-entry invariant equates charge width and Budget schema, and the dimension Cursor bounds each charge read")]
    #[expect(clippy::arithmetic_side_effects, reason = "the dimension Cursor advances only while strictly below the fixed charge width")]
    pub fn commit(self)
        requires self.inv(),
        ensures self.after_spec().inv(),
            self.after_spec().entries_spec() == self.before_spec().entries_spec().push(
                (self.key_spec(), (self.value_spec(), self.charge_data_spec()))),
            self.after_spec().domain_spec() == self.before_spec().domain_spec(),
            self.after_spec().budgets_spec().len() == self.before_spec().budgets_spec().len(),
            forall|dimension: int|
                #![trigger self.after_spec().budgets_spec()[dimension]] #![trigger self.before_spec().budgets_spec()[dimension]]
                0 <= dimension < self.charges_spec().len() ==>
                self.after_spec().budgets_spec()[dimension].1.capacity
                    == self.before_spec().budgets_spec()[dimension].1.capacity
                && self.after_spec().budgets_spec()[dimension].1.allocated as int
                    == self.before_spec().budgets_spec()[dimension].1.allocated as int + self.charges_spec()[dimension] as int,
    {
        let allocation = self.allocation;
        let key = self.key;
        let value = self.value;
        let charges = self.charges;
        let ghost before_budgets = allocation.budgets.entries@;
        let ghost before_entries = allocation.entries.entries@;
        let ghost before_domain = allocation.domain;
        let mut cursor = Cursor::new(0);
        while cursor.position < charges.len()
            invariant cursor.position <= charges@.len(), typed_member_charge(before_budgets.len() as int, charges@),
                before_budgets.len() == charges@.len(), allocation.domain == before_domain,
                allocation.entries.entries@ == before_entries, allocation.entries.unique_identities(),
                !allocation.entries.contains_key_identity(key), allocation.domain.admits(key, value, charges@),
                allocation.budgets.unique_identities(), allocation.budgets.entries@.len() == charges@.len(),
                forall|dimension: int| 0 <= dimension < charges@.len() ==> {
                    let scoped = #[trigger] allocation.budgets.entries@[dimension];
                    &&& scoped.0 == dimension && scoped.1.safety_invariant()
                    &&& scoped.1.reserved == 0 && scoped.1.pending_eviction == 0
                    &&& scoped.1.capacity == before_budgets[dimension].1.capacity
                    &&& scoped.1.allocated as int == before_budgets[dimension].1.allocated as int
                        + if dimension < cursor.position { charges@[dimension] as int } else { 0int }
                    &&& before_budgets[dimension].1.allocated as int + charges@[dimension] as int
                        <= before_budgets[dimension].1.capacity as int
                    &&& before_budgets[dimension].1.allocated as int
                        == typed_charge_to(before_entries, before_entries.len() as int, dimension)
                },
                forall|entry: int| 0 <= entry < before_entries.len() ==> {
                    let retained = #[trigger] before_entries[entry];
                    &&& typed_member_charge(charges@.len() as int, retained.1.1@)
                    &&& allocation.domain.admits(retained.0, retained.1.0, retained.1.1@)
                },
            decreases charges.len() - cursor.position,
        {
            let dimension = cursor.position;
            let budget = match allocation.budgets.value_mut_at(dimension) {
                Some(budget) => budget,
                None => { proof { assert(false); } return; },
            };
            let _accepted = budget.try_allocate(charges[dimension]);
            assert(_accepted);
            cursor.advance_to(dimension + 1);
        }
        allocation.entries.register_key(key, (value, charges));
        assert forall|dimension: int| 0 <= dimension < allocation.budgets.entries@.len() implies
            #[trigger] allocation.budgets.entries@[dimension].1.allocated as int
                == typed_charge_to(allocation.entries.entries@, allocation.entries.entries@.len() as int, dimension) by {
            typed_charge_push(before_entries, (key, (value, charges)), dimension);
        }
    }
}

/// Read-only membership and charge view retaining the original canonical owners.
/// A payload may still have its own interior mutability; this API supplies no
/// mutable admission authority and makes no unrestricted deep-freeze claim.
pub struct SealedTypedAllocation<K: KeyIdentity, V, P: AllocationDomain<K, V> = UnrestrictedAllocation> {
    inner: TypedAllocation<K, V, P>,
}
impl<K: KeyIdentity, V, P: AllocationDomain<K, V>> SealedTypedAllocation<K, V, P> {
    /// The original membership/resource coupling holds after the consuming seal.
    pub closed spec fn inv(&self) -> bool { self.inner.inv() }
    /// Fixed retained membership, payload representation and charges.
    pub closed spec fn entries_spec(&self) -> Seq<(K, (V, Vec<u64>))> { self.inner.entries_spec() }
    /// Fixed scoped Budget owners.
    pub closed spec fn budgets_spec(&self) -> Seq<(usize, Budget)> { self.inner.budgets_spec() }
    /// Fixed logical key membership.
    pub open spec fn contains_spec(&self, key: K) -> bool {
        crate::primitives::resource_registry::has_key(
            crate::primitives::resource_registry::identity_entries(self.entries_spec()),
            self.entries_spec().len() as int, key.identity())
    }
    /// Retained payload correspondence at one fixed logical identity.
    pub open spec fn maps_payload(&self, key: K, value: V) -> bool {
        typed_payload_matches(self.entries_spec(), key, value)
    }
    /// Read the retained member count.
    pub fn len(&self) -> (length: usize)
        requires self.inv(), ensures length == self.entries_spec().len(),
    { self.inner.len() }
    /// Whether no members were admitted.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.inv(), ensures empty == (self.entries_spec().len() == 0),
    { self.inner.is_empty() }
    /// Observe fixed capacity and committed charge at one schema position.
    pub fn budget(&self, dimension: usize) -> (observation: Option<(u64, u64)>)
        requires self.inv(),
        ensures observation == if dimension < self.budgets_spec().len() {
            Some((self.budgets_spec()[dimension as int].1.capacity, self.budgets_spec()[dimension as int].1.allocated))
        } else { None },
    { self.inner.budget(dimension) }
    /// Borrow the retained payload without reopening the allocation.
    pub fn get<'a>(&'a self, key: &K) -> (value: Option<&'a V>)
        requires self.inv(),
        ensures value is None ==> !self.contains_spec(*key),
            value matches Some(value) ==> self.maps_payload(*key, *value),
    { self.inner.get(key) }

    /// Borrow a fixed payload through the same allocation-free identity query.
    pub fn get_query<'a, Q: RegistryQuery<K>>(&'a self, query: &Q) -> (value: Option<&'a V>)
        requires self.inv(),
        ensures value is None ==> !crate::primitives::resource_registry::has_key(
            crate::primitives::resource_registry::identity_entries(self.entries_spec()),
            self.entries_spec().len() as int, query.query_identity()),
            value matches Some(value) ==> typed_identity_payload_matches(
                self.entries_spec(), query.query_identity(), *value),
    { self.inner.get_query(query) }
}

}

impl<K, V> core::fmt::Debug for RefusedTypedAdmission<K, V> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("RefusedTypedAdmission")
            .field("reason", &self.reason)
            .field("dimension", &self.dimension)
            .finish_non_exhaustive()
    }
}

impl<K, V> core::fmt::Debug for RefusedTypedBatch<K, V> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("RefusedTypedBatch")
            .field("reason", &self.reason)
            .field("entry", &self.entry)
            .field("dimension", &self.dimension)
            .finish_non_exhaustive()
    }
}
impl<K, V> core::fmt::Display for RefusedTypedBatch<K, V> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.reason {
            Some(reason) => {
                write!(formatter, "{reason}")?;
                if let Some(entry) = self.entry {
                    write!(formatter, " at entry {entry}")?;
                }
                if let Some(dimension) = self.dimension {
                    write!(formatter, " in dimension {dimension}")?;
                }
                Ok(())
            }
            None => formatter.write_str("batch preparation cancelled"),
        }
    }
}
impl<K, V> std::error::Error for RefusedTypedBatch<K, V> {}
impl<'a, K: KeyIdentity, V, P: AllocationDomain<K, V>> core::fmt::Debug
    for PreparedTypedBatch<'a, K, V, P>
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("PreparedTypedBatch")
            .finish_non_exhaustive()
    }
}

impl core::fmt::Display for TypedAllocationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::EmptySchema => "allocation schema has no membership dimension",
            Self::WidthMismatch => "allocation charges differ from the fixed schema width",
            Self::MembershipCharge => "allocation membership charge must equal one",
            Self::DuplicateKey => "allocation identity already has a retained binding",
            Self::OutsideDomain => "allocation content lies outside the declared domain",
            Self::Capacity => "allocation charge exceeds the scoped Budget",
            Self::StorageUnavailable => "allocation storage reservation failed",
        })
    }
}
impl std::error::Error for TypedAllocationError {}
impl<K, V> core::fmt::Display for RefusedTypedAdmission<K, V> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.reason {
            Some(reason) => {
                write!(formatter, "{reason}")?;
                if let Some(dimension) = self.dimension {
                    write!(formatter, " at dimension {dimension}")?;
                }
                Ok(())
            }
            None => formatter.write_str("allocation preparation cancelled"),
        }
    }
}
impl<K, V> std::error::Error for RefusedTypedAdmission<K, V> {}
impl<K: KeyIdentity, V, P: AllocationDomain<K, V>> core::fmt::Debug for TypedAllocation<K, V, P> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("TypedAllocation")
            .field("members", &self.len())
            .field("dimensions", &self.dimension_count())
            .finish_non_exhaustive()
    }
}
impl<K: KeyIdentity, V, P: AllocationDomain<K, V>> core::fmt::Debug
    for PreparedTypedAdmission<'_, K, V, P>
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("PreparedTypedAdmission")
            .finish_non_exhaustive()
    }
}
impl<K: KeyIdentity, V, P: AllocationDomain<K, V>> core::fmt::Debug
    for SealedTypedAllocation<K, V, P>
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("SealedTypedAllocation")
            .field("members", &self.len())
            .finish_non_exhaustive()
    }
}
