// Shared append-only chain owner for AuditSink and its named compositions.
//
// The chain operation is a verified parameter. BoundedHash is the public bounded model instance;
// AdditiveChain is the ReductionStream instance proved by ReductionStreamFromAuditSink.tla.

use crate::connectives::counter::Counter;
use vstd::prelude::*;

mod storage_seal {
    use vstd::prelude::*;
    verus! { pub trait Sealed {} }
}

mod nullable_data {
    // The pinned macro emits undocumented proof-only arrow_0/arrow_Value_0.
    // Keep the exception inside this one documented data enum's module.
    #![allow(missing_docs)]
    use vstd::prelude::*;
    verus! {
        /// Nullable signed input, kept as typed data rather than an encoded integer.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum NullableSigned {
            /// An input with no contribution.
            Missing,
            /// One nonnull signed contribution.
            Value(i64),
        }
    }
}
pub use nullable_data::NullableSigned;

verus! {

/// Operation used to extend an AuditSink chain.
pub trait ChainOperation: Copy {
    /// Whether the executable operation is defined for this input pair.
    spec fn enabled(&self, previous: u64, operation: u64) -> bool;

    /// Mathematical result of extending the chain.
    spec fn combine_spec(&self, previous: u64, operation: u64) -> u64;

    /// Executable form of `enabled`.
    fn enabled_exec(&self, previous: u64, operation: u64) -> (enabled: bool)
        ensures enabled == self.enabled(previous, operation);

    /// Extend the chain.
    fn combine(&self, previous: u64, operation: u64) -> (result: u64)
        requires self.enabled(previous, operation),
        ensures result == self.combine_spec(previous, operation);
}

/// The bounded recomputation operation used by the public audit sink.
///
/// Its modulo-100 output intentionally permits collisions. It supplies neither cryptographic
/// collision resistance nor evidence of durable custody or external tamper detection.
#[derive(Clone, Copy)]
pub struct BoundedHash;

impl ChainOperation for BoundedHash {
    open spec fn enabled(&self, _previous: u64, _operation: u64) -> bool {
        true
    }

    open spec fn combine_spec(&self, previous: u64, operation: u64) -> u64 {
        AuditSink::<BoundedHash>::hash_spec(previous, operation) as u64
    }

    fn enabled_exec(&self, _previous: u64, _operation: u64) -> (enabled: bool) {
        true
    }

    fn combine(&self, previous: u64, operation: u64) -> (result: u64) {
        AuditSink::<BoundedHash>::hash_exec(previous, operation)
    }
}

/// Exact additive chain operation used by ReductionStream.
#[derive(Clone, Copy)]
pub struct AdditiveChain;

impl ChainOperation for AdditiveChain {
    open spec fn enabled(&self, previous: u64, operation: u64) -> bool {
        previous as int + operation as int <= u64::MAX as int
    }

    open spec fn combine_spec(&self, previous: u64, operation: u64) -> u64 {
        (previous + operation) as u64
    }

    fn enabled_exec(&self, previous: u64, operation: u64) -> (enabled: bool) {
        operation <= u64::MAX - previous
    }

    fn combine(&self, previous: u64, operation: u64) -> (result: u64) {
        previous + operation
    }
}

/// One audit record: the operation, predecessor chain value, and resulting chain value.
pub struct AuditEntry<I: Copy = u64, C: Copy = u64> {
    /// Operation committed by this entry.
    pub operation: I,
    /// Chain value immediately before the operation.
    pub prev_hash: C,
    /// Chain value produced by the operation.
    pub hash: C,
}

/// An append-only chained log. The operation parameter defaults to the public bounded hash.
pub struct AuditSink<
    O: TypedChainOperation = BoundedHash,
    S: AuditStorage<O::Item, O::Carry> = Vec<AuditEntry<<O as TypedChainOperation>::Item, <O as TypedChainOperation>::Carry>>,
> {
    /// Chain operation instance.
    pub operator: O,
    /// Maximum retained entry count.
    pub max_log_len: usize,
    /// Append-only audit entries.
    pub log: S,
    /// Chain value after the latest entry, or zero for an empty log.
    pub last_hash: O::Carry,
}


/// Typed data operation supplied to the existing AuditSink owner.
pub trait TypedChainOperation: Copy {
    /// Admitted operation data.
    type Item: Copy;
    /// Carried domain result.
    type Carry: Copy;
    /// Initial domain result.
    spec fn initial_spec(&self) -> Self::Carry;
    /// Whether this ordered combination is defined.
    spec fn accepts(&self, previous: Self::Carry, operation: Self::Item) -> bool;
    /// Result of one admitted ordered combination.
    spec fn combined(&self, previous: Self::Carry, operation: Self::Item) -> Self::Carry;
    /// Construct the initial domain result.
    fn initial(&self) -> (result: Self::Carry)
        ensures result == self.initial_spec();
    /// Check the operation's domain.
    fn accepts_exec(&self, previous: Self::Carry, operation: Self::Item) -> (yes: bool)
        ensures yes == self.accepts(previous, operation);
    /// Compute one domain result, without retaining automation state.
    fn combine_typed(&self, previous: Self::Carry, operation: Self::Item) -> (result: Self::Carry)
        requires self.accepts(previous, operation),
        ensures result == self.combined(previous, operation);
}

impl<O: ChainOperation> TypedChainOperation for O {
    type Item = u64;
    type Carry = u64;
    open spec fn initial_spec(&self) -> u64 { 0 }
    open spec fn accepts(&self, previous: u64, operation: u64) -> bool {
        self.enabled(previous, operation)
    }
    open spec fn combined(&self, previous: u64, operation: u64) -> u64 {
        self.combine_spec(previous, operation)
    }
    fn initial(&self) -> (result: u64) { 0 }
    fn accepts_exec(&self, previous: u64, operation: u64) -> (yes: bool) {
        self.enabled_exec(previous, operation)
    }
    fn combine_typed(&self, previous: u64, operation: u64) -> (result: u64) {
        self.combine(previous, operation)
    }
}

/// Checked signed arithmetic, used to exercise typed domain/refusal binding.
#[derive(Clone, Copy)]
pub struct CheckedSignedAdd;

impl TypedChainOperation for CheckedSignedAdd {
    type Item = i64;
    type Carry = i64;
    open spec fn initial_spec(&self) -> i64 { 0 }
    open spec fn accepts(&self, previous: i64, operation: i64) -> bool {
        i64::MIN as int <= previous as int + operation as int <= i64::MAX as int
    }
    open spec fn combined(&self, previous: i64, operation: i64) -> i64 {
        (previous as int + operation as int) as i64
    }
    fn initial(&self) -> (result: i64) { 0 }
    fn accepts_exec(&self, previous: i64, operation: i64) -> (yes: bool) {
        if operation >= 0 { previous <= i64::MAX - operation }
        else { previous >= i64::MIN - operation }
    }
    fn combine_typed(&self, previous: i64, operation: i64) -> (result: i64) {
        previous + operation
    }
}

/// Nullable checked sum/count data operation; null consumes input without contributing.
#[derive(Clone, Copy)]
pub struct CheckedSignedSumCount;
/// Typed sum/count domain result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedSumCount {
    /// Checked sum of nonnull inputs.
    pub sum: i64,
    /// Number of nonnull contributions.
    pub count: u64,
}
impl TypedChainOperation for CheckedSignedSumCount {
    type Item = NullableSigned;
    type Carry = SignedSumCount;
    open spec fn initial_spec(&self) -> SignedSumCount { SignedSumCount { sum: 0, count: 0 } }
    open spec fn accepts(&self, previous: SignedSumCount, operation: NullableSigned) -> bool {
        match operation {
            NullableSigned::Missing => true,
            NullableSigned::Value(value) => previous.count < u64::MAX
                && CheckedSignedAdd.accepts(previous.sum, value),
        }
    }
    open spec fn combined(&self, previous: SignedSumCount, operation: NullableSigned) -> SignedSumCount {
        match operation {
            NullableSigned::Missing => previous,
            NullableSigned::Value(value) => SignedSumCount {
                sum: CheckedSignedAdd.combined(previous.sum, value), count: (previous.count + 1) as u64 },
        }
    }
    fn initial(&self) -> (result: SignedSumCount) { SignedSumCount { sum: 0, count: 0 } }
    fn accepts_exec(&self, previous: SignedSumCount, operation: NullableSigned) -> (yes: bool) {
        match operation {
            NullableSigned::Missing => true,
            NullableSigned::Value(value) => previous.count < u64::MAX && CheckedSignedAdd.accepts_exec(previous.sum, value),
        }
    }
    fn combine_typed(&self, previous: SignedSumCount, operation: NullableSigned) -> (result: SignedSumCount) {
        match operation {
            NullableSigned::Missing => previous,
            NullableSigned::Value(value) => SignedSumCount {
                sum: CheckedSignedAdd.combine_typed(previous.sum, value), count: previous.count + 1 },
        }
    }
}

/// Sealed physical record representation used only by the AuditSink owner.
pub trait AuditStorage<I: Copy, C: Copy>: storage_seal::Sealed {
    /// Logical retained/proof history.
    spec fn records(&self) -> Seq<AuditEntry<I, C>>;
    /// Physical representation agrees with the logical observations.
    spec fn storage_valid(&self) -> bool;
    /// Number of accepted records.
    fn record_count(&self) -> (count: usize)
        requires self.storage_valid(),
        ensures count == self.records().len();
    /// Store one already-computed record; no chain operation or admission policy lives here.
    fn append_record(&mut self, entry: AuditEntry<I, C>)
        requires old(self).storage_valid(), old(self).records().len() < usize::MAX,
        ensures final(self).storage_valid(), final(self).records() == old(self).records().push(entry);
    /// Latest operation, without exposing a summary's ghost history as runtime evidence.
    fn latest_operation(&self) -> (latest: Option<I>)
        requires self.storage_valid(),
        ensures latest == if self.records().len() == 0 { None }
            else { Some(self.records()[self.records().len() - 1].operation) };
}

impl<I: Copy, C: Copy> storage_seal::Sealed for Vec<AuditEntry<I, C>> {}
impl<I: Copy, C: Copy> AuditStorage<I, C> for Vec<AuditEntry<I, C>> {
    open spec fn records(&self) -> Seq<AuditEntry<I, C>> { self@ }
    open spec fn storage_valid(&self) -> bool { true }
    fn record_count(&self) -> (count: usize) { self.len() }
    fn append_record(&mut self, entry: AuditEntry<I, C>) { self.push(entry); }
    fn latest_operation(&self) -> (latest: Option<I>) {
        if self.len() == 0 { None } else { Some(self[self.len() - 1].operation) }
    }
}

/// Summary data representation: canonical Counter, one latest item and proof-only history.
/// It has no chain carry, chain operator, reset or record-admission authority.
pub struct SummaryHistory<I: Copy, C: Copy> {
    count: Counter,
    latest: Option<I>,
    history: Ghost<Seq<AuditEntry<I, C>>>,
}
impl<I: Copy, C: Copy> storage_seal::Sealed for SummaryHistory<I, C> {}
impl<I: Copy, C: Copy> SummaryHistory<I, C> {
    fn empty() -> (storage: Self)
        ensures storage.storage_valid(), storage.records().len() == 0,
    {
        Self { count: Counter::new(0), latest: None, history: Ghost(Seq::empty()) }
    }
}
impl<I: Copy, C: Copy> AuditStorage<I, C> for SummaryHistory<I, C> {
    closed spec fn records(&self) -> Seq<AuditEntry<I, C>> { self.history@ }
    closed spec fn storage_valid(&self) -> bool {
        &&& self.count.value as nat == self.history@.len()
        &&& self.history@.len() <= usize::MAX
        &&& self.latest == if self.history@.len() == 0 { None }
            else { Some(self.history@[self.history@.len() - 1].operation) }
    }
    fn record_count(&self) -> (count: usize) { self.count.value() as usize }
    fn append_record(&mut self, entry: AuditEntry<I, C>) {
        let accepted = self.count.try_increment();
        assert(accepted);
        let _ = accepted;
        self.latest = Some(entry.operation);
        proof { self.history = Ghost(self.history@.push(entry)); }
    }
    fn latest_operation(&self) -> (latest: Option<I>) { self.latest }
}

impl<O: TypedChainOperation, S: AuditStorage<O::Item, O::Carry>> AuditSink<O, S> {
    /// Logical chain observations for either sealed retention profile.
    pub open spec fn history_spec(&self) -> Seq<AuditEntry<O::Item, O::Carry>> {
        self.log.records()
    }
    /// Typed chain, admission and representation invariant.
    pub open spec fn chain_valid(&self) -> bool {
        let h = self.history_spec();
        &&& self.log.storage_valid()
        &&& h.len() <= self.max_log_len
        &&& (if h.len() == 0 { self.last_hash == self.operator.initial_spec() }
             else { self.last_hash == h[h.len() - 1].hash })
        &&& (h.len() > 0 ==> h[0].prev_hash == self.operator.initial_spec())
        &&& forall|i: int| 1 <= i < h.len() ==> #[trigger] h[i].prev_hash == h[i - 1].hash
        &&& forall|i: int| 0 <= i < h.len() ==> #[trigger] h[i].hash
            == self.operator.combined(h[i].prev_hash, h[i].operation)
        &&& forall|i: int| 0 <= i < h.len() ==> self.operator.accepts(
            #[trigger] h[i].prev_hash, h[i].operation)
    }
    /// Observe committed count from its physical representation owner.
    pub fn committed_count(&self) -> (count: usize)
        requires self.chain_valid(),
        ensures count == self.history_spec().len(),
    { self.log.record_count() }
    /// Observe the current typed carry.
    pub fn carry(&self) -> (carry: O::Carry)
        ensures carry == self.last_hash,
    { self.last_hash }
    /// Observe the latest accepted operation.
    pub fn latest(&self) -> (latest: Option<O::Item>)
        requires self.chain_valid(),
        ensures latest == if self.history_spec().len() == 0 { None }
            else { Some(self.history_spec()[self.history_spec().len() - 1].operation) },
    { self.log.latest_operation() }
    /// One shared Record commit. Capacity or undefined domain arithmetic refuses unchanged.
    pub fn record_typed(&mut self, operation: O::Item) -> (accepted: bool)
        requires old(self).chain_valid(),
        ensures
            final(self).chain_valid(),
            final(self).operator == old(self).operator,
            final(self).max_log_len == old(self).max_log_len,
            accepted == (old(self).history_spec().len() < old(self).max_log_len
                && old(self).operator.accepts(old(self).last_hash, operation)),
            !accepted ==> *final(self) == *old(self),
            accepted ==> final(self).history_spec() == old(self).history_spec().push(AuditEntry {
                operation, prev_hash: old(self).last_hash,
                hash: old(self).operator.combined(old(self).last_hash, operation),
            }),
            accepted ==> final(self).last_hash
                == old(self).operator.combined(old(self).last_hash, operation),
    {
        if self.log.record_count() >= self.max_log_len { return false; }
        if !self.operator.accepts_exec(self.last_hash, operation) { return false; }
        let ghost previous = self.history_spec();
        let new_hash = self.operator.combine_typed(self.last_hash, operation);
        let entry = AuditEntry { operation, prev_hash: self.last_hash, hash: new_hash };
        self.log.append_record(entry);
        self.last_hash = new_hash;
        proof {
            let h = self.history_spec();
            assert(h == previous.push(entry));
            assert forall|i: int| 1 <= i < h.len() implies
                #[trigger] h[i].prev_hash == h[i - 1].hash by {
                if i < previous.len() {} else { assert(i == previous.len()); }
            }
            assert forall|i: int| 0 <= i < h.len() implies
                #[trigger] h[i].hash == self.operator.combined(h[i].prev_hash, h[i].operation) by {
                if i < previous.len() {} else { assert(i == previous.len()); }
            }
            assert forall|i: int| 0 <= i < h.len() implies
                self.operator.accepts(#[trigger] h[i].prev_hash, h[i].operation) by {
                if i < previous.len() {} else { assert(i == previous.len()); }
            }
        }
        true
    }
}

impl<O: TypedChainOperation> AuditSink<O> {
    /// Reserve retained records without changing the chain or its lifetime ceiling.
    ///
    /// # Errors
    /// Returns the standard allocation error; every logical field remains unchanged.
    pub fn try_reserve_records(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
        requires old(self).chain_valid(),
        ensures final(self).history_spec() == old(self).history_spec(),
            final(self).last_hash == old(self).last_hash,
            final(self).operator == old(self).operator,
            final(self).max_log_len == old(self).max_log_len,
            final(self).chain_valid(),
    {
        self.log.try_reserve(additional)
    }

    /// Construct the full-history profile for a typed domain operation.
    pub fn with_typed_operator(max_log_len: usize, operator: O) -> (sink: Self)
        ensures sink.chain_valid(), sink.operator == operator,
            sink.max_log_len == max_log_len, sink.history_spec().len() == 0,
            sink.last_hash == operator.initial_spec(),
    {
        let last_hash = operator.initial();
        Self { operator, max_log_len, log: Vec::new(), last_hash }
    }
}
impl<O: TypedChainOperation> AuditSink<O, SummaryHistory<O::Item, O::Carry>> {
    /// Construct summary retention. The lifetime bound allocates no record storage.
    pub fn with_summary(max_log_len: usize, operator: O) -> (sink: Self)
        ensures sink.chain_valid(), sink.operator == operator,
            sink.max_log_len == max_log_len, sink.history_spec().len() == 0,
            sink.last_hash == operator.initial_spec(),
    {
        let last_hash = operator.initial();
        Self { operator, max_log_len, log: SummaryHistory::empty(), last_hash }
    }
}

impl AuditSink<BoundedHash> {
    /// Chain hash in the original AuditSink model's integer form.
    pub open spec fn hash_spec(previous: u64, operation: u64) -> int {
        ((previous as int) * 3 + ((operation as int) % 100) + 1) % 100
    }

    /// Execute the public bounded hash instance.
    pub fn hash_exec(previous: u64, operation: u64) -> (result: u64)
        ensures
            result as int == Self::hash_spec(previous, operation),
            result < 100,
    {
        ((previous % 100) * 3 + (operation % 100) + 1) % 100
    }

    /// Construct the public bounded-hash AuditSink.
    pub fn new(max_log_len: usize) -> (sink: AuditSink<BoundedHash>)
        ensures
            sink.max_log_len == max_log_len,
            sink.log@.len() == 0,
            sink.last_hash == 0,
            sink.inv(),
    {
        AuditSink::with_operator(max_log_len, BoundedHash)
    }
}

impl<O: ChainOperation> AuditSink<O> {
    /// Construct an empty chain for a verified operation instance.
    pub fn with_operator(max_log_len: usize, operator: O) -> (sink: AuditSink<O>)
        ensures
            sink.operator == operator,
            sink.max_log_len == max_log_len,
            sink.log@.len() == 0,
            sink.last_hash == 0,
            sink.inv(),
    {
        AuditSink { operator, max_log_len, log: Vec::new(), last_hash: 0 }
    }

    /// Whether the retained log fits within its configured capacity.
    pub open spec fn type_invariant(&self) -> bool {
        self.log.len() <= self.max_log_len
    }

    /// Whether every non-genesis record links to its immediate predecessor.
    pub open spec fn chain_integrity(&self) -> bool {
        forall|index: int|
            #![trigger self.log@[index]]
            1 <= index < self.log.len() ==>
                self.log@[index].prev_hash == self.log@[index - 1].hash
    }

    /// Whether the retained head agrees with the last record or the empty-chain value.
    pub open spec fn hash_consistency(&self) -> bool {
        if self.log.len() > 0 {
            self.last_hash == self.log@[self.log.len() - 1].hash
        } else {
            self.last_hash == 0
        }
    }

    /// Every entry is the configured chain operation recomputed from its stored content.
    ///
    /// For `BoundedHash`, this is an arithmetic consistency check, not a cryptographic binding.
    pub open spec fn hash_binds_content(&self) -> bool {
        forall|index: int|
            #![trigger self.log@[index]]
            0 <= index < self.log.len() ==>
                self.log@[index].hash
                    == self.operator.combine_spec(
                        self.log@[index].prev_hash,
                        self.log@[index].operation,
                    )
    }

    /// Every stored operation was in the configured operation's executable domain.
    pub open spec fn operations_enabled(&self) -> bool {
        forall|index: int|
            #![trigger self.log@[index]]
            0 <= index < self.log.len() ==>
                self.operator.enabled(
                    self.log@[index].prev_hash,
                    self.log@[index].operation,
                )
    }

    /// Whether the first retained record links to the genesis hash.
    pub open spec fn genesis_consistency(&self) -> bool {
        self.log.len() > 0 ==> self.log@[0].prev_hash == 0
    }

    /// Whether all append-only chain contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.chain_integrity()
        &&& self.hash_consistency()
        &&& self.hash_binds_content()
        &&& self.operations_enabled()
        &&& self.genesis_consistency()
    }

    /// Append one operation through the chain owner.
    pub fn record(&mut self, operation: u64) -> (accepted: bool)
        requires
            old(self).inv(),
            old(self).operator.enabled(old(self).last_hash, operation),
        ensures
            final(self).inv(),
            final(self).operator == old(self).operator,
            final(self).max_log_len == old(self).max_log_len,
            accepted == (old(self).log.len() < old(self).max_log_len),
            accepted ==> {
                &&& final(self).log@.len() == old(self).log@.len() + 1
                &&& final(self).last_hash
                    == old(self).operator.combine_spec(old(self).last_hash, operation)
                &&& final(self).log@[old(self).log@.len() as int].operation == operation
                &&& final(self).log@[old(self).log@.len() as int].prev_hash
                    == old(self).last_hash
                &&& forall|index: int|
                    #![trigger final(self).log@[index]]
                    0 <= index < old(self).log@.len() ==>
                        final(self).log@[index] == old(self).log@[index]
            },
            !accepted ==>
                final(self).log@ == old(self).log@
                    && final(self).last_hash == old(self).last_hash,
    {
        assert(self.chain_valid());
        let accepted = self.record_typed(operation);
        assert(self.inv());
        accepted
    }

    /// Recompute the entire configured chain from the zero genesis.
    pub fn validate(&self) -> (valid: bool)
        ensures valid == self.inv(),
    {
        if self.log.len() > self.max_log_len {
            return false;
        }

        let length = self.log.len();
        let mut index: usize = 0;
        let mut expected_previous: u64 = 0;
        while index < length
            invariant
                index <= length,
                length == self.log.len(),
                self.log.len() <= self.max_log_len,
                index == 0 ==> expected_previous == 0,
                index > 0 ==> expected_previous == self.log@[index as int - 1].hash,
                forall|entry: int| 0 <= entry < index ==>
                    #[trigger] self.log@[entry].hash == self.operator.combine_spec(
                        self.log@[entry].prev_hash,
                        self.log@[entry].operation,
                    ),
                forall|entry: int| 0 <= entry < index ==>
                    #[trigger] self.operator.enabled(
                        self.log@[entry].prev_hash,
                        self.log@[entry].operation,
                    ),
                forall|entry: int| 1 <= entry < index ==>
                    #[trigger] self.log@[entry].prev_hash == self.log@[entry - 1].hash,
                index > 0 ==> self.log@[0].prev_hash == 0,
            decreases length - index,
        {
            if self.log[index].prev_hash != expected_previous {
                return false;
            }
            if !self.operator.enabled_exec(self.log[index].prev_hash, self.log[index].operation) {
                return false;
            }
            let expected_hash = self.operator.combine(
                self.log[index].prev_hash,
                self.log[index].operation,
            );
            if self.log[index].hash != expected_hash {
                return false;
            }
            expected_previous = self.log[index].hash;
            index = index + 1;
        }

        if self.last_hash != expected_previous {
            return false;
        }
        true
    }
}

}
