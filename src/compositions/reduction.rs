// AuditSink-backed ReductionStream named composition.
//
// ReductionStreamFromAuditSink.tla has no held glue state: the source is
// immutable configuration, the AuditSink log is the consumed prefix,
// `result` is `last_hash`, and `pos` is `Len(log)`. AdditiveChain instantiates
// AuditSink's operation with the reduction operator.
//
// Overflow ceiling: values bounded to <= 1e9, inputs to <= 1e9 elements,
// so the accumulator stays under 1e18 < u64::MAX.

use vstd::prelude::*;

use crate::connectives::{buffer::Buffer, cursor::Cursor};
#[allow(unused_imports)]
use crate::primitives::audit_sink::{AdditiveChain, AuditSink, ChainOperation};
use crate::primitives::resource_registry::{RegistryStorage, ResourceRegistry};

mod row_error_data {
    // The pinned macro emits undocumented proof-only arrow accessors for data variants.
    // Scope the exception to this fully documented error enum, as for NullableSigned.
    #![allow(missing_docs)]
    use vstd::prelude::*;
    verus! {
        /// Refusal while preparing a row for a fixed set of Reduction columns.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[non_exhaustive]
        pub enum ReductionRowError {
            /// The item width differs from the retained column schema.
            WidthMismatch,
            /// Storage for columns or prepared Copy data could not be reserved.
            StorageUnavailable,
            /// An existing column refused its exact Record guard.
            Column {
                /// The unchanged column's schema position.
                column: usize,
                /// Its canonical capacity or domain refusal.
                reason: crate::primitives::audit_sink::RecordRefusal,
            },
        }
    }
}
pub use row_error_data::ReductionRowError;

verus! {

/// Refusal of an owned, immutable-version Reduction preparation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum OwnedReductionError {
    /// The canonical record ceiling is exhausted.
    Capacity,
    /// The pure domain combination is undefined.
    Domain,
    /// Registry or domain staging storage could not be reserved.
    StorageUnavailable,
    /// Another retained version cannot fit the usize-indexed representation.
    VersionExhausted,
}

/// Pure domain content for an owned-value Reduction. It owns no progress state.
/// Values with interior mutability require their own content-stability contract;
/// immutable version membership does not supply unrestricted deep freezing.
pub trait OwnedReductionOperation<V> {
    /// Mathematical content observed in an owned representation.
    type View;
    /// Pure content observation; allocation addresses are not domain semantics.
    spec fn observe(&self, value: V) -> Self::View;
    /// Whether the ordered content combination is defined.
    spec fn accepts(&self, previous: V, input: V) -> bool;
    /// Exact owned result of an admitted combination.
    spec fn combined(&self, previous: V, input: V) -> Self::View;
    /// Stage a result against immutable borrowed inputs, before owner publication.
    ///
    /// # Errors
    /// Returns Domain for an undefined combination or StorageUnavailable when
    /// staging cannot allocate. It cannot mutate either borrowed representation.
    fn try_combine(&self, previous: &V, input: &V) -> (result: Result<V, OwnedReductionError>)
        ensures match result {
            Ok(value) => self.accepts(*previous, *input)
                && self.observe(value) == self.combined(*previous, *input),
            Err(reason) => reason == OwnedReductionError::StorageUnavailable
                || (reason == OwnedReductionError::Domain && !self.accepts(*previous, *input)),
        };
}

// Copy data operation only; the existing AuditSink owns its prefix and carry.
#[derive(Clone, Copy)]
struct VersionSequence;
impl crate::primitives::audit_sink::TypedChainOperation for VersionSequence {
    type Item = usize;
    type Carry = usize;
    open spec fn initial_spec(&self) -> usize { 0 }
    open spec fn accepts(&self, previous: usize, input: usize) -> bool {
        previous < usize::MAX && input as int == previous as int + 1
    }
    open spec fn combined(&self, _previous: usize, input: usize) -> usize { input }
    fn initial(&self) -> (value: usize) { 0 }
    fn accepts_exec(&self, previous: usize, input: usize) -> (accepted: bool) {
        previous.checked_add(1) == Some(input)
    }
    fn combine_typed(&self, _previous: usize, input: usize) -> (value: usize) { input }
}

struct OwnedVersion<V> { value: V, input: Option<V> }

/// Named Reduction over owned payload versions in the canonical Registry.
/// AuditSink carries only the local version index; historical values never get
/// replaced or exposed mutably. The same owner supplies every prefix observation.
pub struct VersionedReduction<V, O: OwnedReductionOperation<V>> {
    versions: crate::primitives::resource_registry::ResourceRegistry<usize, OwnedVersion<V>>,
    reduction: IncrementalReduction<VersionSequence>,
    operator: O,
}

/// One-use, borrow-scoped owned preparation. Drop/cancel does not publish a version.
pub struct PreparedOwnedReduction<'a, V, O: OwnedReductionOperation<V>> {
    owner: &'a mut VersionedReduction<V, O>,
    input: V,
    value: V,
    version: usize,
}

impl<V, O: OwnedReductionOperation<V>> VersionedReduction<V, O> {
    /// Exact Registry/AuditSink coupling, without another prefix counter.
    pub closed spec fn inv(&self) -> bool {
        &&& self.versions.unique_identities()
        &&& self.reduction.inv()
        &&& self.reduction.operator_spec() == VersionSequence
        &&& self.reduction.result_spec() == self.reduction.processed_spec()
        &&& self.versions.entries@.len() == self.reduction.processed_spec() + 1
        &&& forall|i: int| 0 <= i < self.versions.entries@.len() ==>
            #[trigger] self.versions.entries@[i].0 == i
        &&& self.versions.entries@[0].1.input is None
        &&& forall|i: int| 1 <= i < self.versions.entries@.len() ==> {
            let record = #[trigger] self.versions.entries@[i].1;
            record.input is Some
                && self.operator.accepts(self.versions.entries@[i - 1].1.value, record.input->Some_0)
                && self.operator.observe(record.value) == self.operator.combined(self.versions.entries@[i - 1].1.value, record.input->Some_0)
        }
    }
    /// Canonical accepted-prefix observation.
    pub closed spec fn processed_spec(&self) -> nat { self.reduction.processed_spec() }
    /// Immutable result representation for a retained local version.
    pub closed spec fn value_spec(&self, version: int) -> V { self.versions.entries@[version].1.value }
    /// The input retained by a noninitial version.
    pub closed spec fn input_spec(&self, version: int) -> Option<V> { self.versions.entries@[version].1.input }
    /// Pure content operation retained by this composition.
    pub closed spec fn operator_spec(&self) -> O { self.operator }
    /// Lifetime record ceiling.
    pub closed spec fn limit_spec(&self) -> usize { self.reduction.limit_spec() }

    /// Logical state identity; successful storage reservation may grow physical capacity.
    pub closed spec fn same_state(&self, previous: Self) -> bool {
        self.versions.entries@ == previous.versions.entries@
            && self.reduction == previous.reduction && self.operator == previous.operator
    }

    /// Export all domain observations framed by a refused preparation.
    pub proof fn expose_state_frame(&self, previous: &Self)
        requires self.same_state(*previous),
        ensures self.processed_spec() == previous.processed_spec(),
            self.operator_spec() == previous.operator_spec(), self.limit_spec() == previous.limit_spec(),
            forall|i: int| #[trigger] self.value_spec(i) == previous.value_spec(i)
                && self.input_spec(i) == previous.input_spec(i),
    {}

    /// Export the exact ordered content chain over immutable Registry versions.
    pub proof fn expose_versions(&self)
        requires self.inv(),
        ensures self.input_spec(0) is None,
            forall|i: int| 1 <= i <= self.processed_spec() ==>
                #[trigger] self.input_spec(i) is Some
                && self.operator_spec().accepts(self.value_spec(i - 1), self.input_spec(i)->Some_0)
                && self.operator_spec().observe(self.value_spec(i)) == self.operator_spec().combined(self.value_spec(i - 1), self.input_spec(i)->Some_0),
    {}

    /// Admit initial owned content and one Registry slot before constructing the fold.
    ///
    /// # Errors
    /// Returns both original inputs if initial Registry storage cannot be reserved.
    pub fn try_new(initial: V, limit: usize, operator: O)
        -> (result: Result<Self, (OwnedReductionError, V, O)>)
        ensures match result {
            Ok(owner) => owner.inv() && owner.processed_spec() == 0
                && owner.value_spec(0) == initial && owner.operator_spec() == operator
                && owner.limit_spec() == limit,
            Err((reason, returned, returned_operator)) => reason == OwnedReductionError::StorageUnavailable
                && returned == initial && returned_operator == operator,
        },
    {
        let mut versions = crate::primitives::resource_registry::ResourceRegistry::new();
        if versions.try_reserve_entries(1).is_err() {
            return Err((OwnedReductionError::StorageUnavailable, initial, operator));
        }
        versions.register_key(0usize, OwnedVersion { value: initial, input: None });
        Ok(Self { versions, reduction: IncrementalReduction::new(limit, VersionSequence), operator })
    }

    /// Number of committed domain combinations, observed from the AuditSink owner.
    pub fn processed_len(&self) -> (length: usize)
        requires self.inv(), ensures length == self.processed_spec(),
    { self.reduction.processed_len() }

    /// Borrow a retained immutable version. Its local index is meaningful in this owner.
    pub fn version(&self, version: usize) -> (value: Option<&V>)
        requires self.inv(),
        ensures value is Some <==> version <= self.processed_spec(),
            value matches Some(value) ==> *value == self.value_spec(version as int),
    {
        proof { reveal(VersionedReduction::inv); }
        if version > self.reduction.processed_len() { return None; }
        proof {
            crate::primitives::resource_registry::identity_entry_at(self.versions.entries@, version as int);
        }
        match self.versions.lookup_key_ref(&version) {
            Some(record) => {
                proof { self.versions.unique_identity_value(version, *record, self.versions.entries@[version as int].1); }
                Some(&record.value)
            },
            None => { assert(false); None },
        }
    }

    /// Stage one ordered combination without changing accepted versions or prefix.
    ///
    /// # Errors
    /// Returns the unchanged input on record, representation, storage or domain refusal.
    #[expect(clippy::arithmetic_side_effects, reason = "the version exhaustion guard reserves room for both the successor and its Registry length")]
    pub fn prepare<'a>(&'a mut self, input: V)
        -> (result: Result<PreparedOwnedReduction<'a, V, O>, (OwnedReductionError, V)>)
        requires old(self).inv(),
        ensures match result {
            Ok(prepared) => prepared.inv() && prepared.before_spec().same_state(*old(self))
                && prepared.input_spec() == input && *final(self) == prepared.after_spec()
                && prepared.before_spec().processed_spec() == old(self).processed_spec()
                && prepared.before_spec().operator_spec() == old(self).operator_spec()
                && prepared.before_spec().limit_spec() == old(self).limit_spec()
                && (forall|i: int| #[trigger] prepared.before_spec().value_spec(i) == old(self).value_spec(i)
                    && prepared.before_spec().input_spec(i) == old(self).input_spec(i))
                && old(self).operator_spec().accepts(old(self).value_spec(old(self).processed_spec() as int), input)
                && old(self).processed_spec() < old(self).limit_spec(),
            Err((reason, returned)) => returned == input && final(self).inv() && final(self).same_state(*old(self))
                && match reason {
                    OwnedReductionError::Capacity => old(self).processed_spec() >= old(self).limit_spec(),
                    OwnedReductionError::VersionExhausted => old(self).processed_spec() >= usize::MAX - 1,
                    OwnedReductionError::Domain => !old(self).operator_spec().accepts(
                        old(self).value_spec(old(self).processed_spec() as int), input),
                    OwnedReductionError::StorageUnavailable => true,
                },
        },
    {
        let current = self.reduction.processed_len();
        if current >= self.reduction.limit() { return Err((OwnedReductionError::Capacity, input)); }
        if current >= usize::MAX - 1 { return Err((OwnedReductionError::VersionExhausted, input)); }
        if self.versions.try_reserve_entries(1).is_err() { return Err((OwnedReductionError::StorageUnavailable, input)); }
        let value = match self.version(current) {
            Some(previous) => match self.operator.try_combine(previous, &input) {
                Ok(value) => value,
                Err(reason) => return Err((reason, input)),
            },
            None => { assert(false); return Err((OwnedReductionError::Domain, input)); },
        };
        Ok(PreparedOwnedReduction { owner: self, input, value, version: current + 1 })
    }
}

impl<'a, V, O: OwnedReductionOperation<V>> PreparedOwnedReduction<'a, V, O> {
    /// Both owner actions are admitted and the exact domain result is already staged.
    pub closed spec fn inv(&self) -> bool {
        &&& self.owner.inv()
        &&& self.owner.processed_spec() < self.owner.limit_spec()
        &&& self.owner.processed_spec() < usize::MAX - 1
        &&& self.version as int == self.owner.processed_spec() + 1
        &&& self.owner.operator_spec().accepts(self.owner.value_spec(self.owner.processed_spec() as int), self.input)
        &&& self.owner.operator_spec().observe(self.value) == self.owner.operator_spec().combined(self.owner.value_spec(self.owner.processed_spec() as int), self.input)
    }
    /// Unchanged owner at preparation.
    pub closed spec fn before_spec(&self) -> VersionedReduction<V, O> { *self.owner }
    /// Owner at exclusive-borrow resolution.
    #[verifier::prophetic]
    pub closed spec fn after_spec(&self) -> VersionedReduction<V, O> { *final(self.owner) }
    /// Unconsumed domain input.
    pub closed spec fn input_spec(&self) -> V { self.input }
    /// Already-computed next representation.
    pub closed spec fn value_spec(&self) -> V { self.value }

    /// Publish the Registry version and its admitted Record, without allocation or callback.
    pub fn commit(self) -> (version: usize)
        requires self.inv(),
        ensures self.after_spec().inv(), version == self.after_spec().processed_spec(),
            self.after_spec().processed_spec() == self.before_spec().processed_spec() + 1,
            self.after_spec().operator_spec() == self.before_spec().operator_spec(),
            self.after_spec().limit_spec() == self.before_spec().limit_spec(),
            self.after_spec().value_spec(version as int) == self.value_spec(),
            self.after_spec().input_spec(version as int) == Some(self.input_spec()),
            self.after_spec().operator_spec().observe(self.after_spec().value_spec(version as int))
                == self.before_spec().operator_spec().combined(
                    self.before_spec().value_spec(self.before_spec().processed_spec() as int), self.input_spec()),
            forall|i: int| 0 <= i <= self.before_spec().processed_spec() ==>
                #[trigger] self.after_spec().value_spec(i) == self.before_spec().value_spec(i)
                && self.after_spec().input_spec(i) == self.before_spec().input_spec(i),
    {
        let owner = self.owner;
        let version = self.version;
        let ghost before = owner.versions.entries@;
        proof {
            use crate::primitives::resource_registry::KeyIdentity;
            assert(!owner.versions.contains_key_identity(version)) by {
                if owner.versions.contains_key_identity(version) {
                    owner.versions.identity_has_value(version);
                    let value = choose|value: OwnedVersion<V>| owner.versions.maps_key(version, value);
                    let i = choose|i: int| 0 <= i < before.len()
                        && before[i].0.identity() == version.identity() && before[i].1 == value;
                    assert(before[i].0 == i);
                }
            }
        }
        owner.versions.register_key(version, OwnedVersion { value: self.value, input: Some(self.input) });
        owner.reduction.audit.commit_record(version, version);
        proof {
            assert forall|i: int| 0 <= i < owner.versions.entries@.len()
                implies #[trigger] owner.versions.entries@[i].0 == i by {
                if i < before.len() { assert(owner.versions.entries@[i] == before[i]); }
            }
            assert forall|i: int| 1 <= i < owner.versions.entries@.len() implies {
                let record = #[trigger] owner.versions.entries@[i].1;
                record.input is Some
                    && owner.operator.accepts(owner.versions.entries@[i - 1].1.value, record.input->Some_0)
                    && owner.operator.observe(record.value) == owner.operator.combined(owner.versions.entries@[i - 1].1.value, record.input->Some_0)
            } by {
                if i < before.len() {
                    assert(owner.versions.entries@[i] == before[i]);
                    assert(owner.versions.entries@[i - 1] == before[i - 1]);
                } else { assert(i == before.len()); }
            }
        }
        version
    }

    /// Return the original input without either owner action.
    pub fn cancel(self) -> (input: V)
        requires self.inv(), ensures self.after_spec() == self.before_spec(), input == self.input_spec(),
    { self.input }
}

/// Fold of `s[0..n]`.
pub open spec fn sum_to(s: Seq<u64>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else if n > s.len() as int {
        0
    } else {
        s[n - 1] as int + sum_to(s, n - 1)
    }
}

/// Fold of the entire sequence.
pub open spec fn sum_spec(s: Seq<u64>) -> int {
    sum_to(s, s.len() as int)
}

/// Partial fold bounded by (max element) * n.
pub proof fn lemma_sum_to_bounded(s: Seq<u64>, n: int)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] <= 1_000_000_000u64,
        0 <= n <= s.len() as int,
    ensures
        sum_to(s, n) <= 1_000_000_000 * n,
    decreases n,
{
    if n > 0 {
        lemma_sum_to_bounded(s, n - 1);
    }
}

/// sum_to(s.push(x), n) == sum_to(s, n) for 0 <= n <= |s|.
proof fn lemma_sum_to_push_prefix(s: Seq<u64>, x: u64, n: int)
    requires
        0 <= n <= s.len() as int,
    ensures
        sum_to(s.push(x), n) == sum_to(s, n),
    decreases n,
{
    if n > 0 {
        lemma_sum_to_push_prefix(s, x, n - 1);
        assert(s.push(x)[n - 1] == s[n - 1]);
    }
}

/// sum_spec(s.push(x)) == sum_spec(s) + x.
/// Re-association: the fold of a prefix plus one element equals the fold of the whole.
pub proof fn lemma_sum_push(s: Seq<u64>, x: u64)
    ensures
        sum_spec(s.push(x)) == sum_spec(s) + x as int,
{
    let t = s.push(x);
    let n = s.len() as int;
    assert(t.len() == n + 1);
    lemma_sum_to_push_prefix(s, x, n);
    assert(t[n] == x);
    assert(sum_to(t, n + 1) == t[n] as int + sum_to(t, n));
}

/// Pure indexed domain content for a named incremental Reduction.
pub trait ReductionProjection<O: crate::primitives::audit_sink::TypedChainOperation> {
    /// Number of immutable projected inputs.
    spec fn domain_len(&self) -> nat;
    /// Mathematical item at one admitted position.
    spec fn item_spec(&self, position: int) -> O::Item;
    /// Read the immutable input length without retaining traversal state.
    fn len(&self) -> (length: usize) ensures length == self.domain_len();
    /// Whether the immutable input is empty.
    fn is_empty(&self) -> (empty: bool) ensures empty == (self.domain_len() == 0),
    { self.len() == 0 }
    /// Project one item; the Reduction owner supplies its current position.
    fn item(&self, position: usize) -> (item: O::Item)
        requires position < self.domain_len(),
        ensures item == self.item_spec(position as int);
}

/// Ordered mathematical fold of a projected prefix.
pub open spec fn projected_fold_to<
    O: crate::primitives::audit_sink::TypedChainOperation, P: ReductionProjection<O>,
>(source: P, operator: O, end: int) -> O::Carry
    decreases end,
{
    if end <= 0 || end > source.domain_len() { operator.initial_spec() }
    else { operator.combined(projected_fold_to(source, operator, end - 1), source.item_spec(end - 1)) }
}

/// Every ordered combination in this projected prefix lies within its domain.
pub open spec fn projected_prefix_admitted<
    O: crate::primitives::audit_sink::TypedChainOperation, P: ReductionProjection<O>,
>(source: P, operator: O, end: int) -> bool
    decreases end,
{
    if end == 0 { true }
    else if end < 0 || end > source.domain_len() { false }
    else { projected_prefix_admitted(source, operator, end - 1)
        && operator.accepts(projected_fold_to(source, operator, end - 1), source.item_spec(end - 1)) }
}

/// Typed incremental Reduction using the existing AuditSink summary profile.
/// The AuditSink owns the accepted-prefix count and carried result. Capacity or
/// undefined domain arithmetic refuses without changing either observation.
///
/// ```rust
/// use automation_structures::{CheckedSignedAdd, IncrementalReduction};
/// let mut reduction = IncrementalReduction::new(3, CheckedSignedAdd);
/// assert!(reduction.try_record(7));
/// assert!(reduction.try_record(-4));
/// assert_eq!(reduction.result(), 3);
/// assert_eq!(reduction.processed_len(), 2);
/// ```
pub struct IncrementalReduction<O: crate::primitives::audit_sink::TypedChainOperation> {
    audit: AuditSink<O, crate::primitives::audit_sink::SummaryHistory<O::Item, O::Carry>>,
}

/// One admitted summary Record, exclusively borrowing its canonical owner.
/// Dropping or cancelling it leaves the owner unchanged. Commit consumes it and
/// performs no allocation or domain callback.
///
/// The owner cannot change while its preparation is live:
/// ```compile_fail
/// use automation_structures::{CheckedSignedAdd, IncrementalReduction};
/// let mut reduction = IncrementalReduction::new(2, CheckedSignedAdd);
/// let prepared = reduction.prepare(7).map_err(|(reason, _input)| reason)?;
/// reduction.try_record(3);
/// prepared.commit();
/// # Ok::<(), automation_structures::RecordRefusal>(())
/// ```
/// A committed preparation cannot be spent again:
/// ```compile_fail
/// use automation_structures::{CheckedSignedAdd, IncrementalReduction};
/// let mut reduction = IncrementalReduction::new(2, CheckedSignedAdd);
/// let prepared = reduction.prepare(7).map_err(|(reason, _input)| reason)?;
/// prepared.commit();
/// prepared.commit();
/// # Ok::<(), automation_structures::RecordRefusal>(())
/// ```
pub struct PreparedReductionRecord<'a, O: crate::primitives::audit_sink::TypedChainOperation> {
    reduction: &'a mut IncrementalReduction<O>,
    item: O::Item,
    carry: O::Carry,
}

impl<'a, O: crate::primitives::audit_sink::TypedChainOperation> PreparedReductionRecord<'a, O> {
    /// The preparation retains the same unchanged owner and its one Record guard.
    pub closed spec fn inv(&self) -> bool {
        &&& self.reduction.inv()
        &&& self.reduction.processed_spec() < self.reduction.limit_spec()
        &&& self.reduction.operator_spec().accepts(self.reduction.result_spec(), self.item)
        &&& self.carry == self.reduction.operator_spec().combined(self.reduction.result_spec(), self.item)
    }
    /// Owner observation at preparation, before any publication.
    pub closed spec fn before_spec(&self) -> IncrementalReduction<O> { *self.reduction }
    /// Owner observation when the exclusive borrow is resolved.
    #[verifier::prophetic]
    pub closed spec fn after_spec(&self) -> IncrementalReduction<O> { *final(self.reduction) }
    /// Admitted input data.
    pub closed spec fn item_spec(&self) -> O::Item { self.item }
    /// Already computed ordered result.
    pub closed spec fn carry_spec(&self) -> O::Carry { self.carry }

    /// Consume this preparation and publish its exact Record once.
    /// Returns the owner's committed count and carry as observations.
    pub fn commit(self) -> (observation: (usize, O::Carry))
        requires self.inv(),
        ensures self.after_spec().inv(),
            self.after_spec().operator_spec() == self.before_spec().operator_spec(),
            self.after_spec().limit_spec() == self.before_spec().limit_spec(),
            self.after_spec().processed_spec() == self.before_spec().processed_spec() + 1,
            self.after_spec().result_spec() == self.carry_spec(),
            self.after_spec().result_spec() == self.before_spec().operator_spec().combined(
                self.before_spec().result_spec(), self.item_spec()),
            observation.0 == self.after_spec().processed_spec(),
            observation.1 == self.after_spec().result_spec(),
    {
        let reduction = self.reduction;
        let item = self.item;
        let carry = self.carry;
        reduction.audit.commit_record(item, carry);
        (reduction.processed_len(), reduction.result())
    }

    /// Release the preparation without an owner action and return the input.
    pub fn cancel(self) -> (item: O::Item)
        requires self.inv(),
        ensures self.after_spec() == self.before_spec(), item == self.item_spec(),
    { self.item }
}

impl<O: crate::primitives::audit_sink::TypedChainOperation> IncrementalReduction<O> {
    /// The one AuditSink owns the typed prefix, count and carried result.
    pub closed spec fn inv(&self) -> bool { self.audit.chain_valid() }
    /// Domain operation bound to this reduction.
    pub closed spec fn operator_spec(&self) -> O { self.audit.operator }
    /// Admitted prefix length, without a caller-owned cursor.
    pub closed spec fn processed_spec(&self) -> nat { self.audit.history_spec().len() }
    /// Current result, without a second accumulator.
    pub closed spec fn result_spec(&self) -> O::Carry { self.audit.last_hash }
    /// Fixed lifetime admission ceiling.
    pub closed spec fn limit_spec(&self) -> usize { self.audit.max_log_len }

    /// Construct the typed summary profile without allocating retained history.
    pub fn new(limit: usize, operator: O) -> (reduction: Self)
        ensures reduction.inv(), reduction.processed_spec() == 0,
            reduction.operator_spec() == operator, reduction.limit_spec() == limit,
            reduction.result_spec() == operator.initial_spec(),
    {
        Self { audit: AuditSink::with_summary(limit, operator) }
    }

    /// Construct and fold one immutable projection with its exact input ceiling.
    /// The named owner admits inputs in order, retaining only summary storage.
    ///
    /// # Errors
    /// Returns the first Domain refusal together with the exact accepted-prefix owner.
    pub fn try_from_projection<P: ReductionProjection<O>>(source: &P, operator: O)
        -> (result: Result<Self, (crate::primitives::audit_sink::RecordRefusal, Self)>)
        ensures match result {
            Ok(fold) => fold.inv() && fold.operator_spec() == operator
                && fold.limit_spec() == source.domain_len()
                && fold.processed_spec() == source.domain_len()
                && fold.result_spec() == projected_fold_to(*source, operator, source.domain_len() as int)
                && projected_prefix_admitted(*source, operator, source.domain_len() as int),
            Err((reason, fold)) => reason == crate::primitives::audit_sink::RecordRefusal::Domain
                && fold.inv() && fold.operator_spec() == operator
                && fold.limit_spec() == source.domain_len()
                && fold.processed_spec() < source.domain_len()
                && fold.result_spec() == projected_fold_to(*source, operator, fold.processed_spec() as int)
                && projected_prefix_admitted(*source, operator, fold.processed_spec() as int)
                && !operator.accepts(fold.result_spec(), source.item_spec(fold.processed_spec() as int)),
        },
    {
        let mut fold = Self::new(source.len(), operator);
        match fold.try_fold_projection(source) {
            Ok(()) => Ok(fold),
            Err(reason) => Err((reason, fold)),
        }
    }
    /// Observe the canonical record ceiling.
    pub fn limit(&self) -> (limit: usize)
        requires self.inv(), ensures limit == self.limit_spec(),
    { self.audit.max_log_len }

    /// Read the canonical accepted-prefix count.
    pub fn processed_len(&self) -> (count: usize)
        requires self.inv(), ensures count == self.processed_spec(),
    { self.audit.committed_count() }
    /// Read the canonical carried result.
    pub fn result(&self) -> (result: O::Carry)
        requires self.inv(), ensures result == self.result_spec(),
    { self.audit.carry() }

    /// Admit and compute one summary Record without publishing it.
    ///
    /// # Errors
    /// Returns the exact capacity/domain refusal and unconsumed item. The owner
    /// remains unchanged until the successful preparation is committed.
    pub fn prepare<'a>(&'a mut self, item: O::Item)
        -> (result: Result<PreparedReductionRecord<'a, O>, (crate::primitives::audit_sink::RecordRefusal, O::Item)>)
        requires old(self).inv(),
        ensures match result {
            Ok(prepared) => prepared.inv() && prepared.before_spec() == *old(self)
                && old(self).processed_spec() < old(self).limit_spec()
                && old(self).operator_spec().accepts(old(self).result_spec(), item)
                && prepared.item_spec() == item && *final(self) == prepared.after_spec()
                && prepared.carry_spec() == old(self).operator_spec().combined(old(self).result_spec(), item),
            Err((reason, returned)) => returned == item && *final(self) == *old(self)
                && match reason {
                    crate::primitives::audit_sink::RecordRefusal::Capacity =>
                        old(self).processed_spec() >= old(self).limit_spec(),
                    crate::primitives::audit_sink::RecordRefusal::Domain =>
                        old(self).processed_spec() < old(self).limit_spec()
                        && !old(self).operator_spec().accepts(old(self).result_spec(), item),
                },
        },
    {
        match self.audit.prepare_record(item) {
            Ok(carry) => Ok(PreparedReductionRecord { reduction: self, item, carry }),
            Err(reason) => Err((reason, item)),
        }
    }
    /// Apply the existing typed Record action once; refusal preserves all state.
    pub fn try_record(&mut self, item: O::Item) -> (accepted: bool)
        requires old(self).inv(),
        ensures final(self).inv(),
            final(self).operator_spec() == old(self).operator_spec(),
            final(self).limit_spec() == old(self).limit_spec(),
            accepted == (old(self).processed_spec() < old(self).limit_spec()
                && old(self).operator_spec().accepts(old(self).result_spec(), item)),
            !accepted ==> *final(self) == *old(self),
            accepted ==> final(self).processed_spec() == old(self).processed_spec() + 1,
            accepted ==> final(self).result_spec()
                == old(self).operator_spec().combined(old(self).result_spec(), item),
    { self.audit.record_typed(item) }

    /// Fold immutable projected inputs through this owner's single Record action.
    /// Starts at genesis with a ceiling equal to the input length. A domain refusal
    /// retains the exact admitted prefix in this Reduction; source state is borrowed.
    ///
    /// # Errors
    /// Returns Domain at the first undefined combination, before recording that item.
    pub(crate) fn try_fold_projection<P: ReductionProjection<O>>(&mut self, source: &P)
        -> (result: Result<(), crate::primitives::audit_sink::RecordRefusal>)
        requires old(self).inv(), old(self).processed_spec() == 0,
            old(self).result_spec() == old(self).operator_spec().initial_spec(),
            old(self).limit_spec() == source.domain_len(),
        ensures final(self).inv(),
            final(self).operator_spec() == old(self).operator_spec(),
            final(self).limit_spec() == old(self).limit_spec(),
            final(self).processed_spec() <= source.domain_len(),
            final(self).result_spec() == projected_fold_to(*source,
                old(self).operator_spec(), final(self).processed_spec() as int),
            projected_prefix_admitted(*source, old(self).operator_spec(), final(self).processed_spec() as int),
            (result is Ok) == (final(self).processed_spec() == source.domain_len()),
            result is Err ==> result == Err(crate::primitives::audit_sink::RecordRefusal::Domain)
                && final(self).processed_spec() < source.domain_len()
                && !old(self).operator_spec().accepts(final(self).result_spec(),
                    source.item_spec(final(self).processed_spec() as int)),
    {
        let length = source.len();
        while self.processed_len() < length
            invariant self.inv(), self.operator_spec() == old(self).operator_spec(),
                self.limit_spec() == length, length == old(self).limit_spec(),
                length == source.domain_len(),
                self.processed_spec() <= length,
                self.result_spec() == projected_fold_to(*source, self.operator_spec(), self.processed_spec() as int),
                projected_prefix_admitted(*source, self.operator_spec(), self.processed_spec() as int),
            decreases length - self.processed_spec(),
        {
            let item = source.item(self.processed_len());
            if !self.try_record(item) {
                return Err(crate::primitives::audit_sink::RecordRefusal::Domain);
            }
        }
        Ok(())
    }
}

/// Fixed-column profile of the named Reduction, with one owner per column.
/// Registry owns column identity; each retained AuditSink owns its count and carry.
/// No separate row count, transaction phase or result cache is retained.
pub struct ReductionColumns<O: crate::primitives::audit_sink::TypedChainOperation> {
    columns: ResourceRegistry<usize, IncrementalReduction<O>>,
}

/// An exclusively borrowed, fully prepared row of Copy item/carry data.
/// Commit performs only the existing Record actions, without allocation or callbacks.
/// Cancelling or dropping this preparation leaves every column unchanged.
///
/// Column mutation cannot intervene before the row commits:
/// ```compile_fail
/// use automation_structures::{CheckedSignedAdd, ReductionColumns};
/// let mut columns = ReductionColumns::try_new(&vec![CheckedSignedAdd; 2], 2)?;
/// let row = columns.prepare_row(&vec![7, -4])?;
/// let _intervening = columns.prepare_row(&vec![1, 1]);
/// row.commit();
/// # Ok::<(), automation_structures::ReductionRowError>(())
/// ```
/// A consumed row cannot commit twice:
/// ```compile_fail
/// use automation_structures::{CheckedSignedAdd, ReductionColumns};
/// let mut columns = ReductionColumns::try_new(&vec![CheckedSignedAdd; 2], 2)?;
/// let row = columns.prepare_row(&vec![7, -4])?;
/// row.commit();
/// row.commit();
/// # Ok::<(), automation_structures::ReductionRowError>(())
/// ```
pub struct PreparedReductionRow<'a, O: crate::primitives::audit_sink::TypedChainOperation> {
    reduction: &'a mut ReductionColumns<O>,
    pending: Buffer<(O::Item, O::Carry)>,
}

/// Prepared data satisfies every retained column's existing capacity and domain guard.
pub open spec fn prepared_columns<O: crate::primitives::audit_sink::TypedChainOperation>(
    columns: Seq<(usize, IncrementalReduction<O>)>, data: Seq<(O::Item, O::Carry)>,
) -> bool {
    &&& data.len() == columns.len()
    &&& forall|i: int| 0 <= i < columns.len() ==>
        (#[trigger] columns[i]).1.processed_spec() < columns[i].1.limit_spec()
        && columns[i].1.operator_spec().accepts(columns[i].1.result_spec(), data[i].0)
        && data[i].1 == columns[i].1.operator_spec().combined(columns[i].1.result_spec(), data[i].0)
}

impl<O: crate::primitives::audit_sink::TypedChainOperation> ReductionColumns<O> {
    /// The same retained column bindings, in fixed schema order.
    pub closed spec fn columns_spec(&self) -> Seq<(usize, IncrementalReduction<O>)> { self.columns.entries@ }
    /// Fixed ordinal identity and one valid accepted prefix per column.
    pub closed spec fn inv(&self) -> bool {
        &&& self.columns.unique_identities()
        &&& forall|i: int| 0 <= i < self.columns_spec().len() ==>
            (#[trigger] self.columns_spec()[i]).0 == i && self.columns_spec()[i].1.inv()
        &&& forall|i: int| 0 <= i < self.columns_spec().len() ==>
            #[trigger] self.columns_spec()[i].1.processed_spec() == self.columns_spec()[0].1.processed_spec()
    }
    /// Bind an immutable operator schema to summary owners with one lifetime ceiling.
    ///
    /// # Errors
    /// Returns StorageUnavailable if the column Registry cannot reserve the schema.
    #[expect(clippy::indexing_slicing, reason = "the schema Cursor is guarded by the immutable operator length before reading each column operator")]
    #[expect(clippy::arithmetic_side_effects, reason = "the schema Cursor advances only while strictly below the operator length")]
    pub fn try_new(operators: &Vec<O>, limit: usize) -> (result: Result<Self, ReductionRowError>)
        ensures result is Err ==> result == Err(ReductionRowError::StorageUnavailable),
            result matches Ok(reduction) ==> reduction.inv()
            && reduction.columns_spec().len() == operators@.len()
            && forall|i: int| 0 <= i < operators@.len() ==>
                (#[trigger] reduction.columns_spec()[i]).1.processed_spec() == 0
                && reduction.columns_spec()[i].1.limit_spec() == limit
                && reduction.columns_spec()[i].1.operator_spec() == operators@[i]
                && reduction.columns_spec()[i].1.result_spec() == operators@[i].initial_spec(),
    {
        let mut columns = ResourceRegistry::<usize, IncrementalReduction<O>>::new();
        if columns.try_reserve_entries(operators.len()).is_err() { return Err(ReductionRowError::StorageUnavailable); }
        let mut cursor = Cursor::new(0);
        while cursor.position < operators.len()
            invariant cursor.position <= operators.len(), columns.unique_identities(),
                columns.entries@.len() == cursor.position,
                forall|i: int| 0 <= i < cursor.position ==>
                    (#[trigger] columns.entries@[i]).0 == i && columns.entries@[i].1.inv()
                    && columns.entries@[i].1.processed_spec() == 0
                    && columns.entries@[i].1.limit_spec() == limit
                    && columns.entries@[i].1.operator_spec() == operators@[i]
                    && columns.entries@[i].1.result_spec() == operators@[i].initial_spec(),
            decreases operators.len() - cursor.position,
        {
            let ghost prior = columns.entries@;
            let position = cursor.position;
            let record = IncrementalReduction::new(limit, operators[position]);
            proof {
                crate::primitives::resource_registry::identity_entries_are_exact(columns.entries@);
                assert(!columns.contains_key(position)) by {
                    if columns.contains_key(position) {
                        let i = choose|i: int| 0 <= i < prior.len() && prior[i].0 == position;
                        assert(prior[i].0 == i);
                    }
                }
            }
            columns.register(position, record);
            proof {
                crate::primitives::resource_registry::identity_entries_are_exact(columns.entries@);
                assert forall|i: int| 0 <= i < position + 1 implies
                    (#[trigger] columns.entries@[i]).0 == i && columns.entries@[i].1.inv()
                    && columns.entries@[i].1.processed_spec() == 0
                    && columns.entries@[i].1.limit_spec() == limit
                    && columns.entries@[i].1.operator_spec() == operators@[i]
                    && columns.entries@[i].1.result_spec() == operators@[i].initial_spec() by {
                    if i < position { assert(columns.entries@[i] == prior[i]); }
                    else { assert(i == position); assert(columns.entries@[i] == (position, record)); }
                }
            }
            cursor.advance_to(cursor.position + 1);
        }
        let reduction = Self { columns };
        proof {
            reveal(ReductionColumns::inv);
            assert forall|i: int| 0 <= i < reduction.columns_spec().len() implies
                #[trigger] reduction.columns_spec()[i].1.processed_spec() == reduction.columns_spec()[0].1.processed_spec() by {
                assert(reduction.columns_spec()[i].1.processed_spec() == 0);
                assert(reduction.columns_spec()[0].1.processed_spec() == 0);
            }
        }
        Ok(reduction)
    }
    /// Number of schema columns, observed from the same Registry.
    pub fn column_count(&self) -> (count: usize) ensures count == self.columns_spec().len(),
    { self.columns.entries.len() }
    /// Observe the common accepted prefix from the retained column owner.
    /// An empty schema has no recorded row and reports zero.
    #[expect(clippy::indexing_slicing, reason = "the empty-schema branch returns before reading the first retained column")]
    pub fn processed_len(&self) -> (count: usize)
        requires self.inv(),
        ensures count == if self.columns_spec().len() > 0
            { self.columns_spec()[0].1.processed_spec() } else { 0nat },
    {
        if self.columns.entries.is_empty() { 0 }
        else { self.columns.entries[0].1.processed_len() }
    }
    /// Observe a column carry without exposing its mutable owner.
    #[expect(clippy::manual_map, reason = "the explicit typed storage match preserves the Verus observation contract")]
    pub fn column_result(&self, column: usize) -> (result: Option<O::Carry>)
        requires self.inv(),
        ensures column < self.columns_spec().len() ==> result == Some(self.columns_spec()[column as int].1.result_spec()),
            column >= self.columns_spec().len() ==> result is None,
    {
        match self.columns.entries.value_at(column) {
            Some(column) => Some(column.result()), None => None,
        }
    }
    /// Observe a column's accepted prefix without a shadow row counter.
    #[expect(clippy::manual_map, reason = "the explicit typed storage match preserves the Verus observation contract")]
    pub fn column_processed(&self, column: usize) -> (result: Option<usize>)
        requires self.inv(),
        ensures column < self.columns_spec().len() ==> result == Some(self.columns_spec()[column as int].1.processed_spec() as usize),
            column >= self.columns_spec().len() ==> result is None,
    {
        match self.columns.entries.value_at(column) {
            Some(column) => Some(column.processed_len()), None => None,
        }
    }
    /// Prepare every column before any Record. Items are borrowed and remain unconsumed.
    ///
    /// # Errors
    /// Returns the exact width, storage or first column refusal; all owners remain unchanged.
    #[expect(clippy::indexing_slicing, reason = "the width guard and schema Cursor prove every item position is in bounds")]
    #[expect(clippy::arithmetic_side_effects, reason = "the schema Cursor advances only while strictly below the admitted row width")]
    pub fn prepare_row<'a>(&'a mut self, items: &Vec<O::Item>)
        -> (result: Result<PreparedReductionRow<'a, O>, ReductionRowError>)
        requires old(self).inv(),
        ensures match result {
            Ok(prepared) => prepared.inv() && prepared.before_spec() == *old(self)
                && prepared.items_spec() == items@ && *final(self) == prepared.after_spec()
                && (forall|i: int| 0 <= i < old(self).columns_spec().len() ==>
                    (#[trigger] old(self).columns_spec()[i]).1.processed_spec() < old(self).columns_spec()[i].1.limit_spec()
                    && old(self).columns_spec()[i].1.operator_spec().accepts(
                        old(self).columns_spec()[i].1.result_spec(), items@[i])),
            Err(error) => *final(self) == *old(self) && match error {
                ReductionRowError::WidthMismatch => items@.len() != old(self).columns_spec().len(),
                ReductionRowError::StorageUnavailable => items@.len() == old(self).columns_spec().len(),
                ReductionRowError::Column { column, reason } =>
                    items@.len() == old(self).columns_spec().len() && column < items@.len()
                    && (forall|i: int| 0 <= i < column ==>
                        (#[trigger] old(self).columns_spec()[i]).1.processed_spec() < old(self).columns_spec()[i].1.limit_spec()
                        && old(self).columns_spec()[i].1.operator_spec().accepts(
                            old(self).columns_spec()[i].1.result_spec(), items@[i]))
                    && match reason {
                        crate::primitives::audit_sink::RecordRefusal::Capacity =>
                            old(self).columns_spec()[column as int].1.processed_spec() >= old(self).columns_spec()[column as int].1.limit_spec(),
                        crate::primitives::audit_sink::RecordRefusal::Domain =>
                            old(self).columns_spec()[column as int].1.processed_spec() < old(self).columns_spec()[column as int].1.limit_spec()
                            && !old(self).columns_spec()[column as int].1.operator_spec().accepts(
                                old(self).columns_spec()[column as int].1.result_spec(), items@[column as int]),
                    },
            },
        },
    {
        if items.len() != self.columns.entries.len() { return Err(ReductionRowError::WidthMismatch); }
        let ghost columns = self.columns_spec();
        let mut pending: Buffer<(O::Item, O::Carry)> = match Buffer::try_new(items.len()) {
            Ok(buffer) => buffer,
            Err(_) => return Err(ReductionRowError::StorageUnavailable),
        };
        let mut cursor = Cursor::new(0);
        while cursor.position < items.len()
            invariant self.inv(), *self == *old(self), self.columns_spec() == columns,
                items.len() == columns.len(), cursor.position <= items.len(),
                pending.well_formed(), pending.capacity == items.len(), pending.values@.len() == cursor.position,
                forall|i: int| #![trigger pending.values@[i]] #![trigger columns[i]]
                    0 <= i < cursor.position ==> pending.values@[i].0 == items@[i]
                    && columns[i].1.processed_spec() < columns[i].1.limit_spec()
                    && columns[i].1.operator_spec().accepts(columns[i].1.result_spec(), items@[i])
                    && pending.values@[i].1 == columns[i].1.operator_spec().combined(columns[i].1.result_spec(), items@[i]),
            decreases items.len() - cursor.position,
        {
            let position = cursor.position;
            let item = items[position];
            let column = match self.columns.entries.value_at(position) {
                Some(column) => column,
                None => { proof { assert(false); } return Err(ReductionRowError::StorageUnavailable); },
            };
            let carry = match column.audit.prepare_record(item) {
                Ok(carry) => carry,
                Err(reason) => {
                    proof {
                        assert forall|i: int| 0 <= i < position implies
                            (#[trigger] old(self).columns_spec()[i]).1.processed_spec() < old(self).columns_spec()[i].1.limit_spec()
                            && old(self).columns_spec()[i].1.operator_spec().accepts(
                                old(self).columns_spec()[i].1.result_spec(), items@[i]) by {
                            assert(pending.values@[i].0 == items@[i]);
                        }
                        match reason {
                            crate::primitives::audit_sink::RecordRefusal::Capacity => {
                                assert(column.processed_spec() >= column.limit_spec());
                            },
                            crate::primitives::audit_sink::RecordRefusal::Domain => {
                                assert(column.processed_spec() < column.limit_spec());
                                assert(!column.operator_spec().accepts(column.result_spec(), item));
                            },
                        }
                    }
                    return Err(ReductionRowError::Column { column: position, reason });
                },
            };
            let ghost prior_data = pending.values@;
            let accepted = pending.push((item, carry));
            assert(accepted is Ok); let _ = accepted;
            proof {
                assert forall|i: int| #![trigger pending.values@[i]] #![trigger columns[i]]
                    0 <= i < position + 1 implies pending.values@[i].0 == items@[i]
                    && columns[i].1.processed_spec() < columns[i].1.limit_spec()
                    && columns[i].1.operator_spec().accepts(columns[i].1.result_spec(), items@[i])
                    && pending.values@[i].1 == columns[i].1.operator_spec().combined(columns[i].1.result_spec(), items@[i]) by {
                    if i < position { assert(pending.values@[i] == prior_data[i]); }
                    else { assert(i == position); assert(pending.values@[i] == (item, carry)); }
                }
            }
            cursor.advance_to(position + 1);
        }
        proof {
            assert forall|i: int| 0 <= i < pending.values@.len() implies
                self.columns_spec()[i].1.processed_spec() < self.columns_spec()[i].1.limit_spec()
                && self.columns_spec()[i].1.operator_spec().accepts(self.columns_spec()[i].1.result_spec(), pending.values@[i].0)
                && pending.values@[i].1 == self.columns_spec()[i].1.operator_spec().combined(
                    self.columns_spec()[i].1.result_spec(), pending.values@[i].0) by {
                assert(pending.values@[i].0 == items@[i]);
            }
            assert(pending.values@.map(|_i: int, pair: (O::Item, O::Carry)| pair.0) == items@) by {
                assert forall|i: int| 0 <= i < items@.len() implies
                    pending.values@.map(|_i: int, pair: (O::Item, O::Carry)| pair.0)[i] == items@[i] by {}
            }
            assert(prepared_columns(self.columns_spec(), pending.values@)) by {
                assert forall|i: int| 0 <= i < self.columns_spec().len() implies
                    (#[trigger] self.columns_spec()[i]).1.processed_spec() < self.columns_spec()[i].1.limit_spec()
                    && self.columns_spec()[i].1.operator_spec().accepts(self.columns_spec()[i].1.result_spec(), pending.values@[i].0)
                    && pending.values@[i].1 == self.columns_spec()[i].1.operator_spec().combined(
                        self.columns_spec()[i].1.result_spec(), pending.values@[i].0) by {
                    assert(pending.values@[i].0 == items@[i]);
                }
            }
        }
        let prepared = PreparedReductionRow { reduction: self, pending };
        proof {
            reveal(PreparedReductionRow::inv);
            assert(prepared.reduction.inv());
            assert(prepared.pending.well_formed());
            assert(prepared.pending.values@.len() == prepared.reduction.columns_spec().len());
            assert(prepared_columns(prepared.reduction.columns_spec(), prepared.pending.values@));
            assert(prepared.inv());
        }
        Ok(prepared)
    }
}

impl<'a, O: crate::primitives::audit_sink::TypedChainOperation> PreparedReductionRow<'a, O> {
    /// Every retained column's exact Record guard and result was admitted without mutation.
    pub closed spec fn inv(&self) -> bool {
        &&& self.reduction.inv() && self.pending.well_formed()
        &&& prepared_columns(self.reduction.columns_spec(), self.pending.values@)
    }
    /// The unchanged owner at row preparation.
    pub closed spec fn before_spec(&self) -> ReductionColumns<O> { *self.reduction }
    /// The owner after resolving this exclusive row borrow.
    #[verifier::prophetic]
    pub closed spec fn after_spec(&self) -> ReductionColumns<O> { *final(self.reduction) }
    /// The admitted Copy inputs, in schema order.
    pub closed spec fn items_spec(&self) -> Seq<O::Item> {
        self.pending.values@.map(|_i: int, pair: (O::Item, O::Carry)| pair.0)
    }
    /// Release this exclusive borrow without a Record action.
    pub fn cancel(self)
        requires self.inv(), ensures self.after_spec() == self.before_spec(),
    {}
    /// Publish the complete prepared row once. No allocation or domain callback runs here.
    #[expect(clippy::indexing_slicing, reason = "the prepared-row invariant equates pending length and column count; the schema Cursor bounds each paired read")]
    #[expect(clippy::arithmetic_side_effects, reason = "the schema Cursor advances only while strictly below the retained column count")]
    pub fn commit(self)
        requires self.inv(),
        ensures self.after_spec().inv(),
            self.after_spec().columns_spec().len() == self.before_spec().columns_spec().len(),
            forall|i: int| #![trigger self.after_spec().columns_spec()[i]] #![trigger self.before_spec().columns_spec()[i]]
                0 <= i < self.before_spec().columns_spec().len() ==>
                self.after_spec().columns_spec()[i].0 == self.before_spec().columns_spec()[i].0
                && self.after_spec().columns_spec()[i].1.operator_spec() == self.before_spec().columns_spec()[i].1.operator_spec()
                && self.after_spec().columns_spec()[i].1.limit_spec() == self.before_spec().columns_spec()[i].1.limit_spec()
                && self.after_spec().columns_spec()[i].1.processed_spec() == self.before_spec().columns_spec()[i].1.processed_spec() + 1
                && self.after_spec().columns_spec()[i].1.result_spec() == self.before_spec().columns_spec()[i].1.operator_spec().combined(
                    self.before_spec().columns_spec()[i].1.result_spec(), self.items_spec()[i]),
    {
        reveal(PreparedReductionRow::inv);
        reveal(ReductionColumns::inv);
        assert(self.reduction.inv());
        assert(self.pending.well_formed());
        let ghost before = self.reduction.columns_spec();
        let ghost data = self.pending.values@;
        assert(self.pending.values@.len() == before.len());
        assert forall|i: int| 0 <= i < before.len() implies before[i].1.inv()
            && before[i].1.processed_spec() < before[i].1.limit_spec()
            && before[i].1.operator_spec().accepts(before[i].1.result_spec(), data[i].0)
            && data[i].1 == before[i].1.operator_spec().combined(before[i].1.result_spec(), data[i].0) by {
            assert(self.reduction.columns_spec()[i].1.inv());
            assert(self.reduction.columns_spec()[i].1.processed_spec() < self.reduction.columns_spec()[i].1.limit_spec());
            assert(self.reduction.columns_spec()[i].1.operator_spec().accepts(
                self.reduction.columns_spec()[i].1.result_spec(), self.pending.values@[i].0));
            assert(self.pending.values@[i].1 == self.reduction.columns_spec()[i].1.operator_spec().combined(
                self.reduction.columns_spec()[i].1.result_spec(), self.pending.values@[i].0));
        }
        let reduction = self.reduction;
        let pending = self.pending;
        let mut cursor = Cursor::new(0);
        while cursor.position < reduction.columns.entries.len()
            invariant cursor.position <= before.len(), reduction.columns.unique_identities(),
                reduction.columns_spec().len() == before.len(),
                pending.well_formed(), pending.values@ == data,
                data.len() == before.len(),
                forall|i: int| 0 <= i < before.len() ==> before[i].0 == i,
                forall|i: int| 0 <= i < before.len() ==> reduction.columns_spec()[i].0 == before[i].0,
                forall|i: int| 0 <= i < cursor.position ==>
                    (#[trigger] reduction.columns_spec()[i]).1.inv()
                    && reduction.columns_spec()[i].1.operator_spec() == before[i].1.operator_spec()
                    && reduction.columns_spec()[i].1.limit_spec() == before[i].1.limit_spec()
                    && reduction.columns_spec()[i].1.processed_spec() == before[i].1.processed_spec() + 1
                    && reduction.columns_spec()[i].1.result_spec() == data[i].1,
                forall|i: int| cursor.position <= i < before.len() ==> reduction.columns_spec()[i] == before[i],
                forall|i: int| 0 <= i < before.len() ==> (#[trigger] before[i]).1.inv()
                    && before[i].1.processed_spec() < before[i].1.limit_spec()
                    && before[i].1.operator_spec().accepts(before[i].1.result_spec(), data[i].0)
                    && data[i].1 == before[i].1.operator_spec().combined(before[i].1.result_spec(), data[i].0),
                forall|i: int| 0 <= i < before.len() ==> #[trigger] before[i].1.processed_spec() == before[0].1.processed_spec(),
            decreases before.len() - cursor.position,
        {
            let position = cursor.position;
            let ghost prior = reduction.columns_spec();
            let (item, carry) = pending.values[position];
            assert(item == data[position as int].0 && carry == data[position as int].1);
            {
                let column = match reduction.columns.value_mut_at(position) {
                    Some(column) => column,
                    None => { proof { assert(false); } return; },
                };
                assert(*column == before[position as int].1);
                let prepared = PreparedReductionRecord { reduction: column, item, carry };
                proof {
                    reveal(PreparedReductionRecord::inv);
                    assert(prepared.reduction.inv());
                    assert(prepared.reduction.processed_spec() < prepared.reduction.limit_spec());
                    assert(prepared.reduction.operator_spec().accepts(prepared.reduction.result_spec(), prepared.item));
                    assert(prepared.carry == prepared.reduction.operator_spec().combined(prepared.reduction.result_spec(), prepared.item));
                    assert(prepared.inv());
                }
                let _observation = prepared.commit();
            }
            proof {
                assert(reduction.columns_spec()[position as int].1.inv());
                assert(reduction.columns_spec()[position as int].1.result_spec() == data[position as int].1);
                assert forall|i: int| 0 <= i < position + 1 implies
                    reduction.columns_spec()[i].1.inv()
                    && reduction.columns_spec()[i].1.operator_spec() == before[i].1.operator_spec()
                    && reduction.columns_spec()[i].1.limit_spec() == before[i].1.limit_spec()
                    && reduction.columns_spec()[i].1.processed_spec() == before[i].1.processed_spec() + 1
                    && reduction.columns_spec()[i].1.result_spec() == data[i].1 by {
                    if i < position { assert(reduction.columns_spec()[i] == prior[i]); }
                    else { assert(i == position); }
                }
            }
            cursor.advance_to(cursor.position + 1);
        }
    }
}

/// Additive ReductionStream assembled from the AuditSink owner.
pub struct Reducer {
    /// Immutable reduction source.
    pub source: Vec<u64>,
    /// Owner of the consumed prefix, position, and result.
    pub audit: AuditSink<AdditiveChain>,
}

impl Reducer {
    /// AuditSink's log is exactly the consumed source prefix.
    pub open spec fn prefix_binding(&self) -> bool {
        &&& self.audit.log.len() <= self.source.len()
        &&& forall|index: int|
            #![trigger self.audit.log@[index]]
            0 <= index < self.audit.log.len() ==>
                self.audit.log@[index].operation == self.source@[index]
    }

    /// AuditSink's carry is the fold of the consumed source prefix.
    pub open spec fn aggregate(&self) -> bool {
        self.audit.last_hash as int == sum_to(self.source@, self.audit.log.len() as int)
    }

    /// Overflow ceiling for the additive AuditSink operation.
    pub open spec fn bounded(&self) -> bool {
        &&& forall|k: int| 0 <= k < self.source@.len() ==> self.source@[k] <= 1_000_000_000u64
        &&& self.source@.len() <= 1_000_000_000
    }

    /// Complete representation invariant of the named composition.
    pub open spec fn inv(&self) -> bool {
        &&& self.audit.inv()
        &&& self.audit.max_log_len == self.source.len()
        &&& self.prefix_binding()
        &&& self.aggregate()
        &&& self.bounded()
    }

    /// Empty AuditSink over the immutable source.
    pub fn new(items: Vec<u64>) -> (r: Reducer)
        requires
            forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
            items@.len() <= 1_000_000_000,
        ensures
            r.inv(),
            r.source@ == items@,
            r.audit.log@.len() == 0,
            r.audit.last_hash == 0,
    {
        let audit = AuditSink::with_operator(items.len(), AdditiveChain);
        let r = Reducer { source: items, audit };
        proof {
            assert(r.audit.log@.len() == 0);
            assert(sum_to(r.source@, 0) == 0);
        }
        r
    }

    /// Number of source elements already consumed.
    pub fn position(&self) -> (position: usize)
        ensures position == self.audit.log@.len(),
    {
        self.audit.log.len()
    }

    /// Current additive result, projected from AuditSink's carry.
    pub fn result(&self) -> (result: u64)
        ensures result == self.audit.last_hash,
    {
        self.audit.last_hash
    }

    /// Number of source elements not yet consumed.
    #[expect(clippy::arithmetic_side_effects, reason = "the required prefix binding proves the AuditSink log length is at most source length")]
    pub fn remaining_len(&self) -> (remaining: usize)
        requires self.prefix_binding(),
        ensures remaining == self.source@.len() - self.audit.log@.len(),
    {
        self.source.len() - self.audit.log.len()
    }

    /// Whether the complete source prefix has been reduced.
    pub fn done(&self) -> (d: bool)
        requires self.prefix_binding(),
        ensures
            d == (self.audit.log@.len() == self.source@.len()),
    {
        self.audit.log.len() == self.source.len()
    }

    /// Consume the next source value through AuditSink's `Record` action.
    #[expect(clippy::indexing_slicing, reason = "the enabled-action precondition proves AuditSink's consumed prefix is strictly below source length")]
    pub fn process(&mut self)
        requires
            old(self).inv(),
            old(self).audit.log@.len() < old(self).source@.len(),
        ensures
            final(self).inv(),
            final(self).source@ == old(self).source@,
            final(self).audit.log@.len() == old(self).audit.log@.len() + 1,
            final(self).audit.last_hash
                == old(self).audit.last_hash
                    + old(self).source@[old(self).audit.log@.len() as int],
    {
        let old_position = self.audit.log.len();
        let x = self.source[old_position];
        let ghost old_log = self.audit.log@;
        let ghost source = self.source@;
        proof {
            lemma_sum_to_bounded(self.source@, old_position as int);
            assert(self.audit.last_hash as int
                == sum_to(self.source@, old_position as int));
            assert(self.audit.last_hash as int <= 1_000_000_000 * old_position as int);
            assert(x <= 1_000_000_000u64);
            assert(old_position < 1_000_000_000usize);
            assert(self.audit.last_hash as int + x as int <= 1_000_000_000_000_000_000int);
            assert(1_000_000_000_000_000_000int < u64::MAX as int);
            assert(self.audit.operator.enabled(self.audit.last_hash, x));
        }
        let accepted = self.audit.record(x);
        assert(accepted);
        let _ = accepted;

        proof {
            assert(self.audit.log@[old_position as int].operation == x);
            assert(self.prefix_binding()) by {
                assert forall|index: int|
                    #![trigger self.audit.log@[index]]
                    0 <= index < self.audit.log.len() implies
                        self.audit.log@[index].operation == self.source@[index] by {
                    if index < old_position {
                        assert(self.audit.log@[index] == old_log[index]);
                    } else {
                        assert(index == old_position);
                    }
                }
            }
            assert(sum_to(source, old_position as int + 1)
                == source[old_position as int] as int
                    + sum_to(source, old_position as int));
            assert(self.aggregate());
        }
    }
}

// ---------------------------------------------------------------------------
// Borrowed batch bindings reuse the named projected Reduction above. The
// retained fold_to specifications describe domain results, not another owner.
/// Fold the first `n` values of `s` from `identity` with `op`.
pub open spec fn fold_to(s: Seq<u64>, n: int, identity: u64, op: spec_fn(u64, u64) -> u64) -> u64
    decreases n,
{
    if n <= 0 {
        identity
    } else if n > s.len() as int {
        identity
    } else {
        op(fold_to(s, n - 1, identity, op), s[n - 1])
    }
}

/// Sum-specific boundedness for the retained mathematical fold: mirrors
/// lemma_sum_to_bounded above. Boundedness is operator-specific (sum needs a
/// multiplicative bound; max needs only the input ceiling), so it sits outside
/// the generic lemmas.
proof fn lemma_fold_to_bounded_sum(s: Seq<u64>, n: int)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] <= 1_000_000_000u64,
        0 <= n <= s.len() as int,
    ensures
        fold_to(s, n, 0, |a: u64, b: u64| (a + b) as u64) <= 1_000_000_000 * n,
    decreases n,
{
    if n > 0 {
        lemma_fold_to_bounded_sum(s, n - 1);
    }
}

/// Unsigned maximum domain operation for the existing Reduction owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaximumU64;

impl ChainOperation for MaximumU64 {
    open spec fn enabled(&self, _previous: u64, _operation: u64) -> bool { true }
    open spec fn combine_spec(&self, previous: u64, operation: u64) -> u64 {
        if previous > operation { previous } else { operation }
    }
    fn enabled_exec(&self, _previous: u64, _operation: u64) -> (enabled: bool) { true }
    fn combine(&self, previous: u64, operation: u64) -> (result: u64) {
        if previous > operation { previous } else { operation }
    }
}

struct BorrowedU64Input<'a> { items: &'a [u64] }

impl<'a, O: ChainOperation> ReductionProjection<O> for BorrowedU64Input<'a> {
    closed spec fn domain_len(&self) -> nat { self.items@.len() }
    closed spec fn item_spec(&self, position: int) -> u64 { self.items@[position] }
    fn len(&self) -> (length: usize) { self.items.len() }
    #[expect(clippy::indexing_slicing, reason = "ReductionProjection requires position below the immutable source domain length")]
    fn item(&self, position: usize) -> (item: u64) { self.items[position] }
}

proof fn lemma_borrowed_sum(source: BorrowedU64Input, end: int)
    requires
        forall|k: int| 0 <= k < source.items@.len() ==> source.items@[k] <= 1_000_000_000u64,
        source.items@.len() <= 1_000_000_000,
        0 <= end <= source.items@.len(),
    ensures
        projected_fold_to(source, AdditiveChain, end)
            == fold_to(source.items@, end, 0, |a: u64, b: u64| (a + b) as u64),
        projected_prefix_admitted(source, AdditiveChain, end),
    decreases end,
{
    if end > 0 {
        lemma_borrowed_sum(source, end - 1);
        lemma_fold_to_bounded_sum(source.items@, end - 1);
    }
}

proof fn lemma_borrowed_max(source: BorrowedU64Input, end: int)
    requires 0 <= end <= source.items@.len(),
    ensures
        projected_fold_to(source, MaximumU64, end)
            == fold_to(source.items@, end, 0, |a: u64, b: u64| if a > b { a } else { b }),
        projected_prefix_admitted(source, MaximumU64, end),
    decreases end,
{
    if end > 0 { lemma_borrowed_max(source, end - 1); }
}

/// Additive fold, stated against the generic fold_to spec. The value is
/// identical to sum_spec; this entry point instantiates the generic spec rather
/// than the sum-specific one above.
pub fn reduce_sum(items: &[u64]) -> (result: u64)
    requires
        forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
        items@.len() <= 1_000_000_000,
    ensures
        result as int == fold_to(items@, items@.len() as int, 0, |a: u64, b: u64| (a + b) as u64) as int,
{
    let source = BorrowedU64Input { items };
    match IncrementalReduction::try_from_projection(&source, AdditiveChain) {
        Ok(fold) => {
            proof { lemma_borrowed_sum(source, items@.len() as int); }
            fold.result()
        },
        Err((_reason, fold)) => {
            proof { lemma_borrowed_sum(source, fold.processed_spec() as int + 1); }
            // Unreachable under the retained bounds: the next ordered sum is defined.
            fold.result()
        },
    }
}

/// Max fold: a second, idempotent instance of the same ordered-prefix spec.
pub fn reduce_max(items: &[u64]) -> (result: u64)
    requires
        forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
        items@.len() <= 1_000_000_000,
    ensures
        result as int == fold_to(items@, items@.len() as int, 0, |a: u64, b: u64| if a > b { a } else { b }) as int,
{
    let source = BorrowedU64Input { items };
    match IncrementalReduction::try_from_projection(&source, MaximumU64) {
        Ok(fold) => {
            proof { lemma_borrowed_max(source, items@.len() as int); }
            fold.result()
        },
        Err((_reason, fold)) => {
            proof { lemma_borrowed_max(source, fold.processed_spec() as int + 1); }
            // Maximum is a total domain operation; this branch is unreachable.
            fold.result()
        },
    }
}

}

impl<O: crate::primitives::audit_sink::TypedChainOperation> core::fmt::Debug
    for IncrementalReduction<O>
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("IncrementalReduction")
            .field("processed", &self.processed_len())
            .field("limit", &self.audit.max_log_len)
            .finish_non_exhaustive()
    }
}

impl<O: crate::primitives::audit_sink::TypedChainOperation> core::fmt::Debug
    for ReductionColumns<O>
{
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("ReductionColumns")
            .field("columns", &self.column_count())
            .finish_non_exhaustive()
    }
}
impl core::fmt::Display for ReductionRowError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WidthMismatch => {
                formatter.write_str("row width differs from the Reduction columns")
            }
            Self::StorageUnavailable => {
                formatter.write_str("Reduction row storage reservation failed")
            }
            Self::Column { column, reason } => {
                write!(formatter, "Reduction column {column}: {reason}")
            }
        }
    }
}
impl std::error::Error for ReductionRowError {}
