// Executable carrier for the bounded one-source/two-sink StreamGraph fan-out
// profile. A source commit broadcasts one value to both queues. Rejected calls
// stutter, and conservation is stated independently for each branch.

use vstd::prelude::*;

use crate::connectives::buffer::{Buffer, BufferLayout, ContiguousStorage, FifoStorage};
use crate::connectives::counter::Counter;
use crate::connectives::marker::Marker;
use crate::modalities::stream_graph::{ReceivedStreamValue, TypedPublishRefusal, TypedStreamError};
use crate::primitives::budget::Budget;
use crate::primitives::resource_registry::{RegistryStorage, ResourceRegistry};

mod branch_error_data {
    // The pinned macro emits undocumented proof-only arrow accessors for data variants.
    // As for ReductionRowError, scope the exception to this fully documented error enum.
    #![allow(missing_docs)]
    use vstd::prelude::*;
    verus! {
        /// Exact source bound or branch owner that refused paired publication.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[non_exhaustive]
        pub enum TypedBranchFanoutError {
            /// The finite source has accepted its declared maximum input count.
            InputLimitReached,
            /// The left branch refused before any owner changed.
            Left(crate::modalities::stream_graph::TypedStreamError),
            /// The right branch refused before any owner changed.
            Right(crate::modalities::stream_graph::TypedStreamError),
        }
    }
}
pub use branch_error_data::TypedBranchFanoutError;

verus! {

/// One of the existing two governed FIFO branches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FanoutBranch {
    /// Left branch of the retained fanout composition.
    Left,
    /// Right branch of the retained fanout composition.
    Right,
}

/// Checked shared-fanout construction, publication or consumption refusal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypedFanoutError {
    /// This existing two-branch profile requires positive branch capacity.
    ZeroCapacity,
    /// Storage reservation failed before any publication.
    StorageUnavailable,
    /// One actual branch Buffer is full.
    BranchCapacity,
    /// The declared retained encoded-byte Budget refused publication.
    ByteCapacity,
    /// The shared publication Counter cannot issue another identity.
    SequenceExhausted,
    /// Producer closure prevents publication, or this closed branch has drained.
    Closed,
    /// This open branch has no observation available.
    Empty,
    /// The observation belongs to another caller-owned scope.
    ForeignScope,
    /// The observation no longer identifies this branch's current head.
    StaleObservation,
}

/// Scoped branch/head identity returned by a borrowed observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FanoutObservationToken {
    scope: u64,
    branch: FanoutBranch,
    sequence: u64,
}
impl FanoutObservationToken {
    /// Read-only owner scope for external proof consumers.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Read-only branch selected by the borrowed observation.
    pub closed spec fn branch_spec(&self) -> FanoutBranch { self.branch }
    /// Read-only publication identity for external proof consumers.
    pub closed spec fn sequence_spec(&self) -> u64 { self.sequence }
    /// Publication identity read without exposing token construction.
    pub fn sequence(&self) -> (sequence: u64) ensures sequence == self.sequence_spec(),
    { self.sequence }
}

/// Borrowed original payload and the exact branch head that supplied it.
pub struct FanoutObservation<'a, T> {
    /// Original payload retained by the same Registry for both branches.
    pub value: &'a T,
    /// Checked observation identity for subsequent branch consumption.
    pub token: FanoutObservationToken,
}

/// Typed shared-payload binding around the existing two-branch fanout owner.
/// Each instance requires a distinct caller-owned scope. The declared encoded-byte
/// Budget covers Registry custody while at least one governed branch reference
/// remains. Domain aliases and physical-memory accounting require their own binding.
pub struct TypedFanout<T> {
    scope: u64,
    flow: StreamGraphFanout<FifoStorage>,
    payloads: ResourceRegistry<u64, ((T, Counter), u64), FifoStorage>,
    bytes: Budget,
    closed: Marker,
}

pub(crate) open spec fn fanout_queue<S: BufferLayout<u64>>(flow: StreamGraphFanout<S>, branch: FanoutBranch) -> Seq<u64> {
    match branch { FanoutBranch::Left => flow.left_queue.values@,
        FanoutBranch::Right => flow.right_queue.values@ }
}
pub(crate) open spec fn fanout_consumed<S: BufferLayout<u64>>(flow: StreamGraphFanout<S>, branch: FanoutBranch) -> nat {
    match branch { FanoutBranch::Left => flow.left_emitted.value_spec(),
        FanoutBranch::Right => flow.right_emitted.value_spec() }
}
pub(crate) open spec fn fanout_head<S: BufferLayout<u64>>(flow: StreamGraphFanout<S>) -> nat {
    if flow.left_emitted.value_spec() < flow.right_emitted.value_spec() {
        flow.left_emitted.value_spec() } else { flow.right_emitted.value_spec() }
}
pub(crate) open spec fn fanout_references<S: BufferLayout<u64>>(flow: StreamGraphFanout<S>, sequence: u64) -> nat {
    (if flow.left_emitted.value_spec() <= sequence as nat { 1nat } else { 0nat })
        + (if flow.right_emitted.value_spec() <= sequence as nat { 1nat } else { 0nat })
}

impl<T> TypedFanout<T> {
    /// Retained original payloads, reference Counters and declared byte charges.
    pub closed spec fn entries_spec(&self) -> Seq<(u64, ((T, Counter), u64))> { self.payloads.entries@ }
    /// Immutable caller-owned scope identity.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Exact retained charge owned by Budget.
    pub closed spec fn encoded_bytes_spec(&self) -> nat { self.bytes.allocated as nat }
    /// Producer closure owned by Marker.
    pub closed spec fn closed_spec(&self) -> bool { self.closed.marked }
    /// Shared publication head owned by the existing fanout Counter.
    pub closed spec fn published_spec(&self) -> nat { self.flow.ingested.value_spec() }
    /// Exact consumed prefix of one existing branch owner.
    pub closed spec fn consumed_spec(&self, branch: FanoutBranch) -> nat {
        fanout_consumed(self.flow, branch)
    }
    /// Actual retained identity sequence of one existing branch Buffer.
    pub closed spec fn queue_spec(&self, branch: FanoutBranch) -> Seq<u64> {
        fanout_queue(self.flow, branch)
    }
    /// Oldest identity whose original payload still has a governed branch reference.
    pub closed spec fn retained_head_spec(&self) -> nat {
        fanout_head(self.flow)
    }
    /// Exact number of governed branch references still naming one publication.
    pub closed spec fn references_spec(&self, sequence: u64) -> nat {
        fanout_references(self.flow, sequence)
    }
    /// Coupling of existing branch execution, original custody, reference and charge owners.
    pub closed spec fn inv(&self) -> bool {
        &&& self.flow.inv()
        &&& self.flow.max_inputs == usize::MAX
        &&& self.flow.record_domain_size == u64::MAX
        &&& self.payloads.unique_identities()
        &&& self.bytes.safety_invariant()
        &&& self.bytes.reserved == 0 && self.bytes.pending_eviction == 0
        &&& self.bytes.allocated as int == crate::modalities::stream_graph::stream_bytes_to(
            self.payloads.entries@, self.payloads.entries@.len() as int)
        &&& fanout_head(self.flow) + self.payloads.entries@.len() == self.flow.ingested.value_spec()
        &&& forall|index: int| 0 <= index < self.payloads.entries@.len() ==>
            #[trigger] self.payloads.entries@[index].0 as int == fanout_head(self.flow) as int + index
                && self.payloads.entries@[index].1.0.1.value_spec()
                    == fanout_references(self.flow, self.payloads.entries@[index].0)
                && 0 < self.payloads.entries@[index].1.0.1.value_spec() <= 2
        &&& forall|branch: FanoutBranch, index: int| 0 <= index < fanout_queue(self.flow, branch).len() ==>
            #[trigger] fanout_queue(self.flow, branch)[index] as int == fanout_consumed(self.flow, branch) as int + index
    }

    proof fn expose_branch(&self, branch: FanoutBranch)
        requires self.inv(),
        ensures fanout_consumed(self.flow, branch) <= self.flow.ingested.value_spec() <= usize::MAX as nat,
            fanout_head(self.flow) <= fanout_consumed(self.flow, branch),
            fanout_consumed(self.flow, branch) + fanout_queue(self.flow, branch).len() == self.flow.ingested.value_spec(),
            forall|index: int| 0 <= index < fanout_queue(self.flow, branch).len() ==>
                #[trigger] fanout_queue(self.flow, branch)[index] as int == fanout_consumed(self.flow, branch) as int + index,
    {
        match branch { FanoutBranch::Left => {}, FanoutBranch::Right => {} }
    }

    /// Expose branch conservation and shared retained-custody projections to proof consumers.
    pub proof fn expose_custody(&self)
        requires self.inv(),
        ensures self.consumed_spec(FanoutBranch::Left) + self.queue_spec(FanoutBranch::Left).len() == self.published_spec(),
            self.consumed_spec(FanoutBranch::Right) + self.queue_spec(FanoutBranch::Right).len() == self.published_spec(),
            self.retained_head_spec() == if self.consumed_spec(FanoutBranch::Left) < self.consumed_spec(FanoutBranch::Right) {
                self.consumed_spec(FanoutBranch::Left) } else { self.consumed_spec(FanoutBranch::Right) },
            self.retained_head_spec() + self.entries_spec().len() == self.published_spec(),
            forall|index: int| 0 <= index < self.entries_spec().len() ==>
                #[trigger] self.entries_spec()[index].0 as int == self.retained_head_spec() as int + index
                    && self.entries_spec()[index].1.0.1.value_spec() == self.references_spec(self.entries_spec()[index].0),
    {}

    /// Reserve both existing branch Buffer backings before accepting original content.
    ///
    /// # Errors
    /// Returns ZeroCapacity or StorageUnavailable before any payload is consumed.
    pub fn try_new(scope: u64, capacity: usize, encoded_bytes: u64)
        -> (result: Result<Self, TypedFanoutError>)
        ensures result matches Ok(owner) ==> owner.inv() && owner.scope_spec() == scope
            && owner.entries_spec().len() == 0 && owner.published_spec() == 0
            && owner.encoded_bytes_spec() == 0 && !owner.closed_spec()
            && owner.consumed_spec(FanoutBranch::Left) == 0 && owner.consumed_spec(FanoutBranch::Right) == 0
            && owner.queue_spec(FanoutBranch::Left).len() == 0 && owner.queue_spec(FanoutBranch::Right).len() == 0,
    {
        if capacity == 0 { return Err(TypedFanoutError::ZeroCapacity); }
        let left = match Buffer::<u64, FifoStorage>::try_with_storage(capacity) {
            Ok(queue) => queue, Err(_) => return Err(TypedFanoutError::StorageUnavailable),
        };
        let right = match Buffer::<u64, FifoStorage>::try_with_storage(capacity) {
            Ok(queue) => queue, Err(_) => return Err(TypedFanoutError::StorageUnavailable),
        };
        let flow = StreamGraphFanout::with_buffers(left, right, usize::MAX, u64::MAX);
        Ok(Self { scope, flow, payloads: ResourceRegistry::new_fifo(), bytes: Budget::new(encoded_bytes),
            closed: Marker::new(false) })
    }

    /// Number of originals retained by Registry, including a slow branch's references.
    pub fn retained_len(&self) -> (length: usize) requires self.inv(),
        ensures length as nat == self.entries_spec().len(),
    { self.payloads.entries.len() }
    /// Current encoded-byte charge read from its Budget owner.
    pub fn retained_bytes(&self) -> (bytes: u64) requires self.inv(),
        ensures bytes as nat == self.encoded_bytes_spec(),
    { self.bytes.allocated }
    /// Actual pending count read from the selected existing branch Buffer.
    pub fn pending_len(&self, branch: FanoutBranch) -> (length: usize) requires self.inv(),
        ensures length as nat == self.queue_spec(branch).len(),
    { match branch { FanoutBranch::Left => self.flow.left_queue.len(), FanoutBranch::Right => self.flow.right_queue.len() } }
    /// Whether the producer is closed and both actual branches are drained.
    pub fn is_drained(&self) -> (drained: bool) requires self.inv(),
        ensures drained == (self.closed_spec() && self.entries_spec().len() == 0),
    { self.closed.is_marked() && self.flow.left_queue.is_empty() && self.flow.right_queue.is_empty() }

    /// Publish one original to both existing branch owners, or return it unchanged.
    ///
    /// # Errors
    /// Returns original content on closure, branch/byte pressure, storage failure or identity exhaustion.
    pub fn publish(&mut self, value: T, encoded_bytes: u64)
        -> (result: Result<u64, crate::modalities::stream_graph::TypedPublishRefusal<T, TypedFanoutError>>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).scope_spec() == old(self).scope_spec(),
            final(self).closed_spec() == old(self).closed_spec(),
            final(self).consumed_spec(FanoutBranch::Left) == old(self).consumed_spec(FanoutBranch::Left),
            final(self).consumed_spec(FanoutBranch::Right) == old(self).consumed_spec(FanoutBranch::Right),
            result matches Err(refusal) ==> refusal.value == value
                && final(self).entries_spec() == old(self).entries_spec()
                && final(self).published_spec() == old(self).published_spec()
                && final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec()
                && final(self).queue_spec(FanoutBranch::Left) == old(self).queue_spec(FanoutBranch::Left)
                && final(self).queue_spec(FanoutBranch::Right) == old(self).queue_spec(FanoutBranch::Right),
            result matches Ok(sequence) ==> sequence as nat == old(self).published_spec()
                && final(self).published_spec() == old(self).published_spec() + 1
                && final(self).entries_spec() == old(self).entries_spec().push((sequence,((value,Counter { value: 2 }),encoded_bytes)))
                && final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec() + encoded_bytes as nat
                && final(self).queue_spec(FanoutBranch::Left) == old(self).queue_spec(FanoutBranch::Left).push(sequence)
                && final(self).queue_spec(FanoutBranch::Right) == old(self).queue_spec(FanoutBranch::Right).push(sequence),
    {
        if self.closed.is_marked() { return Err(TypedPublishRefusal { error: TypedFanoutError::Closed, value }); }
        if self.flow.left_queue.is_full() || self.flow.right_queue.is_full() {
            return Err(TypedPublishRefusal { error: TypedFanoutError::BranchCapacity, value });
        }
        if !self.bytes.admits_additional(encoded_bytes, 0) {
            return Err(TypedPublishRefusal { error: TypedFanoutError::ByteCapacity, value });
        }
        if !self.flow.ingested.can_increment() || self.flow.ingested.value() >= usize::MAX as u64 {
            return Err(TypedPublishRefusal { error: TypedFanoutError::SequenceExhausted, value });
        }
        if self.payloads.try_reserve_entries(1).is_err() {
            return Err(TypedPublishRefusal { error: TypedFanoutError::StorageUnavailable, value });
        }
        let ghost before = *self;
        let sequence = self.flow.ingested.value();
        proof {
            crate::primitives::resource_registry::identity_entries_are_exact(self.payloads.entries@);
            assert(!self.payloads.contains_key_identity(sequence)) by {
                if self.payloads.contains_key_identity(sequence) {
                    let index = choose|index: int| 0 <= index < self.payloads.entries@.len()
                        && #[trigger] self.payloads.entries@[index].0 == sequence;
                    assert(false);
                }
            }
        }
        let references = Counter::new(2);
        self.payloads.register_absent_key(sequence, ((value, references), encoded_bytes));
        let _charged = self.bytes.try_allocate(encoded_bytes);
        assert(_charged);
        proof {
            self.flow.left_queue.expose_capacity_bound();
            self.flow.right_queue.expose_capacity_bound();
        }
        assert(self.flow.left_queue.values@.len() < self.flow.left_queue.capacity);
        assert(self.flow.right_queue.values@.len() < self.flow.right_queue.capacity);
        assert(sequence < self.flow.record_domain_size);
        assert(self.flow.ingested.value_spec() < self.flow.max_inputs as nat);
        let _broadcast = self.flow.source_ingest(sequence);
        assert(_broadcast);
        proof {
            crate::modalities::stream_graph::stream_bytes_append_prefix(before.payloads.entries@,
                (sequence,((value,references),encoded_bytes)), before.payloads.entries@.len() as int);
        }
        assert forall|branch: FanoutBranch, index: int| 0 <= index < self.queue_spec(branch).len() implies
            #[trigger] self.queue_spec(branch)[index] as int == self.consumed_spec(branch) as int + index by {
            if index < before.queue_spec(branch).len() {
                assert(self.queue_spec(branch)[index] == before.queue_spec(branch)[index]);
            }
        }
        assert forall|index: int| 0 <= index < self.payloads.entries@.len() implies
            #[trigger] self.payloads.entries@[index].0 as int == self.retained_head_spec() as int + index
                && self.payloads.entries@[index].1.0.1.value_spec()
                    == self.references_spec(self.payloads.entries@[index].0)
                && 0 < self.payloads.entries@[index].1.0.1.value_spec() <= 2 by {
            if index < before.payloads.entries@.len() {
                assert(self.payloads.entries@[index] == before.payloads.entries@[index]);
            }
        }
        assert(self.flow.inv());
        assert(self.bytes.allocated as int == crate::modalities::stream_graph::stream_bytes_to(
            self.payloads.entries@, self.payloads.entries@.len() as int));
        assert(fanout_head(self.flow) + self.payloads.entries@.len() == self.flow.ingested.value_spec());
        assert(self.payloads.unique_identities());
        assert(self.bytes.safety_invariant());
        assert(self.bytes.reserved == 0 && self.bytes.pending_eviction == 0);
        assert forall|branch: FanoutBranch, index: int| 0 <= index < fanout_queue(self.flow, branch).len() implies
            #[trigger] fanout_queue(self.flow, branch)[index] as int == fanout_consumed(self.flow, branch) as int + index by {
            assert(self.queue_spec(branch)[index] as int == self.consumed_spec(branch) as int + index);
        }
        assert forall|index: int| 0 <= index < self.payloads.entries@.len() implies
            #[trigger] self.payloads.entries@[index].0 as int == fanout_head(self.flow) as int + index
                && self.payloads.entries@[index].1.0.1.value_spec()
                    == fanout_references(self.flow, self.payloads.entries@[index].0)
                && 0 < self.payloads.entries@[index].1.0.1.value_spec() <= 2 by {
            assert(self.payloads.entries@[index].0 as int == self.retained_head_spec() as int + index);
        }
        assert(self.inv());
        Ok(sequence)
    }

    /// Borrow the original at the exact rank established by this profile's coupling.
    /// The flow supplies the retained interval; Registry storage supplies the borrow.
    #[expect(clippy::arithmetic_side_effects, reason = "the explicit sequence >= retained head guard bounds identity subtraction")]
    #[expect(clippy::cast_possible_truncation, reason = "the retained interval lies below the fanout's usize::MAX publication ceiling")]
    fn retained_entry(&self, sequence: u64) -> (entry: Option<&((T, Counter), u64)>)
        requires self.inv(),
        ensures entry is Some <==> self.retained_head_spec() <= sequence as nat
            && (sequence as nat) < self.published_spec(),
            entry matches Some(entry) ==> exists|index: int| 0 <= index < self.entries_spec().len()
                && self.entries_spec()[index].0 == sequence && self.entries_spec()[index].1 == *entry,
    {
        proof { self.expose_branch(FanoutBranch::Left); }
        let head = self.flow.retained_head();
        if sequence < head || sequence >= self.flow.ingested.value() { return None; }
        let index = (sequence - head) as usize;
        assert(index < self.payloads.entries@.len());
        assert(self.payloads.entries@[index as int].0 == sequence);
        let entry = self.payloads.entries.value_at(index);
        assert(entry is Some);
        proof {
            if let Some(retained) = entry {
                assert(self.entries_spec()[index as int].1 == *retained);
                assert(exists|rank: int| 0 <= rank < self.entries_spec().len()
                    && self.entries_spec()[rank].0 == sequence
                    && self.entries_spec()[rank].1 == *retained);
            }
        }
        entry
    }

    /// Borrow the original payload at one actual branch head without releasing its charge.
    ///
    /// # Errors
    /// Returns Empty while that branch is open, or Closed after its producer closes and it drains.
    #[expect(clippy::indexing_slicing, reason = "the selected branch Buffer is checked nonempty before its retained head is read")]
    pub fn observe<'a>(&'a self, branch: FanoutBranch) -> (result: Result<FanoutObservation<'a,T>, TypedFanoutError>)
        requires self.inv(),
        ensures result matches Ok(observation) ==> observation.token.scope_spec() == self.scope_spec()
            && observation.token.branch_spec() == branch
            && self.queue_spec(branch).len() > 0
            && observation.token.sequence_spec() == self.queue_spec(branch)[0]
            && exists|index: int| 0 <= index < self.entries_spec().len()
                && #[trigger] self.entries_spec()[index].0 == observation.token.sequence_spec()
                && self.entries_spec()[index].1.0.0 == *observation.value,
            result is Err <==> self.queue_spec(branch).len() == 0,
            result matches Err(error) ==> error == if self.closed_spec() { TypedFanoutError::Closed } else { TypedFanoutError::Empty },
    {
        proof { self.expose_branch(FanoutBranch::Left); self.expose_branch(FanoutBranch::Right); }
        let empty = match branch { FanoutBranch::Left => self.flow.left_queue.is_empty(), FanoutBranch::Right => self.flow.right_queue.is_empty() };
        if empty { return Err(if self.closed.is_marked() { TypedFanoutError::Closed } else { TypedFanoutError::Empty }); }
        proof {
            self.flow.left_queue.values.expose_view();
            self.flow.right_queue.values.expose_view();
        }
        let sequence = match branch { FanoutBranch::Left => self.flow.left_queue.values.values[0], FanoutBranch::Right => self.flow.right_queue.values.values[0] };
        proof {
            let index = sequence as int - self.retained_head_spec() as int;
            assert(0 <= index < self.payloads.entries@.len());
            assert(self.payloads.entries@[index].0 == sequence);
            crate::primitives::resource_registry::identity_entry_at(self.payloads.entries@, index);
            assert(self.payloads.contains_key_identity(sequence));
        }
        match self.retained_entry(sequence) {
            Some(entry) => {
                proof {
                    let index = choose|index: int| 0 <= index < self.payloads.entries@.len()
                        && #[trigger] self.payloads.entries@[index].0 == sequence
                        && self.payloads.entries@[index].1 == *entry;
                    assert(self.entries_spec()[index].1.0.0 == entry.0.0);
                }
                Ok(FanoutObservation { value: &entry.0.0,
                    token: FanoutObservationToken { scope: self.scope, branch, sequence } })
            },
            None => { assert(false); Err(TypedFanoutError::Empty) },
        }
    }

    /// Close publication while retaining every outstanding governed branch reference.
    pub fn close_input(&mut self) -> (changed: bool) requires old(self).inv(),
        ensures final(self).inv(), final(self).closed_spec(), changed == !old(self).closed_spec(),
            final(self).entries_spec() == old(self).entries_spec(),
            final(self).scope_spec() == old(self).scope_spec(),
            final(self).published_spec() == old(self).published_spec(),
            final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec(),
            final(self).queue_spec(FanoutBranch::Left) == old(self).queue_spec(FanoutBranch::Left),
            final(self).queue_spec(FanoutBranch::Right) == old(self).queue_spec(FanoutBranch::Right),
    { self.closed.set() }

    /// Observe the original's actual reference Counter without recomputing branch totals.
    pub fn remaining_references(&self, sequence: u64) -> (references: Option<u64>)
        requires self.inv(),
        ensures references matches Some(count) ==> count as nat == self.references_spec(sequence),
            references is None ==> (sequence as nat) < self.retained_head_spec() || self.published_spec() <= sequence as nat,
    {
        match self.retained_entry(sequence) {
            Some(entry) => {
                proof {
                    let index = choose|index: int| 0 <= index < self.payloads.entries@.len()
                        && #[trigger] self.payloads.entries@[index].0 == sequence
                        && self.payloads.entries@[index].1 == *entry;
                }
                Some(entry.0.1.value())
            },
            None => {
                proof {
                    if self.retained_head_spec() <= sequence as nat && (sequence as nat) < self.published_spec() {
                        let index = sequence as int - self.retained_head_spec() as int;
                        crate::primitives::resource_registry::identity_entry_at(self.payloads.entries@, index);
                        assert(false);
                    }
                }
                None
            },
        }
    }

    /// Consume the exact observed branch head, retaining original custody until its last reference.
    ///
    /// # Errors
    /// Refuses a foreign scope or a stale/repeated observation without consuming any reference.
    #[expect(clippy::indexing_slicing, reason = "the selected branch Buffer is checked nonempty before comparing its current head")]
    #[expect(clippy::arithmetic_side_effects, reason = "the explicit sequence >= retained head guard bounds identity subtraction")]
    #[expect(clippy::cast_possible_truncation, reason = "an admitted branch head lies below the fanout's usize::MAX publication ceiling")]
    pub fn consume(&mut self, token: FanoutObservationToken) -> (result: Result<(),TypedFanoutError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).scope_spec() == old(self).scope_spec(),
            final(self).published_spec() == old(self).published_spec(),
            final(self).closed_spec() == old(self).closed_spec(),
            result is Ok <==> token.scope_spec() == old(self).scope_spec()
                && old(self).queue_spec(token.branch_spec()).len() > 0
                && token.sequence_spec() == old(self).queue_spec(token.branch_spec())[0],
            result is Err ==> *final(self) == *old(self),
            result matches Err(error) ==> error == if token.scope_spec() != old(self).scope_spec() {
                TypedFanoutError::ForeignScope } else { TypedFanoutError::StaleObservation },
            result is Ok ==> final(self).consumed_spec(token.branch_spec()) == old(self).consumed_spec(token.branch_spec()) + 1
                && old(self).references_spec(token.sequence_spec()) == final(self).references_spec(token.sequence_spec()) + 1,
            result is Ok ==> final(self).entries_spec().len() == old(self).entries_spec().len()
                - if old(self).references_spec(token.sequence_spec()) == 1 { 1nat } else { 0nat },
            result is Ok ==> final(self).encoded_bytes_spec() == if old(self).references_spec(token.sequence_spec()) == 1 {
                old(self).encoded_bytes_spec() - old(self).entries_spec()[0].1.1 as nat
            } else { old(self).encoded_bytes_spec() as int },
            result is Ok ==> forall|branch: FanoutBranch| branch != token.branch_spec() ==>
                final(self).consumed_spec(branch) == old(self).consumed_spec(branch)
                    && final(self).queue_spec(branch) == old(self).queue_spec(branch),
            result is Ok ==> forall|position: int| #![trigger final(self).entries_spec()[position]]
                0 <= position < final(self).entries_spec().len() ==>
                exists|previous: int| 0 <= previous < old(self).entries_spec().len()
                    && #[trigger] old(self).entries_spec()[previous].0 == final(self).entries_spec()[position].0
                    && old(self).entries_spec()[previous].1.0.0 == final(self).entries_spec()[position].1.0.0
                    && old(self).entries_spec()[previous].1.1 == final(self).entries_spec()[position].1.1,
    {
        proof { self.expose_branch(token.branch); }
        if token.scope != self.scope { return Err(TypedFanoutError::ForeignScope); }
        let empty = match token.branch { FanoutBranch::Left => self.flow.left_queue.is_empty(), FanoutBranch::Right => self.flow.right_queue.is_empty() };
        if empty { return Err(TypedFanoutError::StaleObservation); }
        proof {
            self.flow.left_queue.values.expose_view();
            self.flow.right_queue.values.expose_view();
        }
        let sequence = match token.branch { FanoutBranch::Left => self.flow.left_queue.values.values[0], FanoutBranch::Right => self.flow.right_queue.values.values[0] };
        if sequence != token.sequence { return Err(TypedFanoutError::StaleObservation); }
        let head = self.flow.retained_head();
        if sequence < head { assert(false); return Err(TypedFanoutError::StaleObservation); }
        let index = (sequence - head) as usize;
        let ghost before = *self;
        assert(index < self.payloads.entries@.len());
        let (remaining, charge) = match self.payloads.value_mut_at(index) {
            Some(entry) => {
                let _released = entry.0.1.try_decrement();
                assert(_released);
                (entry.0.1.value(), entry.1)
            },
            None => { assert(false); return Err(TypedFanoutError::StaleObservation); },
        };
        let _consumed = match token.branch { FanoutBranch::Left => self.flow.consume_left(), FanoutBranch::Right => self.flow.consume_right() };
        assert(_consumed);
        assert forall|position: int| 0 <= position < self.payloads.entries@.len() implies
            #[trigger] self.payloads.entries@[position].1.0.1.value_spec()
                == self.references_spec(self.payloads.entries@[position].0) by {
            if position == index as int {
                assert(self.payloads.entries@[position].0 == sequence);
            } else {
                assert(self.payloads.entries@[position] == before.payloads.entries@[position]);
                assert(self.payloads.entries@[position].0 != sequence);
            }
        }
        proof {
            crate::modalities::stream_graph::stream_bytes_same_charges(before.payloads.entries@,
                self.payloads.entries@, self.payloads.entries@.len() as int);
        }
        if remaining == 0 {
            assert(index == 0);
            let ghost before_remove = self.payloads.entries@;
            let _removed = self.payloads.deregister_identity_at(0);
            proof {
                assert(self.payloads.entries@ =~= before_remove.skip(1));
                crate::modalities::stream_graph::stream_bytes_drop_first(before_remove, before_remove.len() as int);
                crate::modalities::stream_graph::stream_bytes_nonnegative(self.payloads.entries@, self.payloads.entries@.len() as int);
                assert(charge <= self.bytes.allocated);
            }
            self.bytes.release(charge);
            assert(self.retained_head_spec() == before.retained_head_spec() + 1);
        } else {
            assert(remaining == 1);
            assert(self.retained_head_spec() == before.retained_head_spec());
        }
        assert forall|branch: FanoutBranch, position: int| 0 <= position < self.queue_spec(branch).len() implies
            #[trigger] self.queue_spec(branch)[position] as int == self.consumed_spec(branch) as int + position by {
            if branch == token.branch { assert(self.queue_spec(branch)[position] == before.queue_spec(branch)[position + 1]); }
            else { assert(self.queue_spec(branch) == before.queue_spec(branch)); }
        }
        assert forall|position: int| 0 <= position < self.payloads.entries@.len() implies
            #[trigger] self.payloads.entries@[position].0 as int == self.retained_head_spec() as int + position
                && self.payloads.entries@[position].1.0.1.value_spec()
                    == self.references_spec(self.payloads.entries@[position].0)
                && 0 < self.payloads.entries@[position].1.0.1.value_spec() <= 2 by {
            if remaining == 0 {
                assert(self.payloads.entries@[position] == before.payloads.entries@[position + 1]);
                assert(self.payloads.entries@[position].0 != sequence);
            } else if position == index as int {
                assert(self.payloads.entries@[position].1.0.1.value == remaining);
            }
        }
        assert(self.flow.inv());
        assert(self.bytes.allocated as int == crate::modalities::stream_graph::stream_bytes_to(
            self.payloads.entries@, self.payloads.entries@.len() as int));
        assert(fanout_head(self.flow) + self.payloads.entries@.len() == self.flow.ingested.value_spec());
        assert(self.payloads.unique_identities());
        assert(self.bytes.safety_invariant());
        assert(self.bytes.reserved == 0 && self.bytes.pending_eviction == 0);
        assert forall|branch: FanoutBranch, position: int| 0 <= position < fanout_queue(self.flow, branch).len() implies
            #[trigger] fanout_queue(self.flow, branch)[position] as int == fanout_consumed(self.flow, branch) as int + position by {
            assert(self.queue_spec(branch)[position] as int == self.consumed_spec(branch) as int + position);
        }
        assert forall|position: int| 0 <= position < self.payloads.entries@.len() implies
            #[trigger] self.payloads.entries@[position].0 as int == fanout_head(self.flow) as int + position
                && self.payloads.entries@[position].1.0.1.value_spec()
                    == fanout_references(self.flow, self.payloads.entries@[position].0)
                && 0 < self.payloads.entries@[position].1.0.1.value_spec() <= 2 by {
            assert(self.payloads.entries@[position].0 as int == self.retained_head_spec() as int + position);
        }
        assert(self.inv());
        assert forall|position: int| #![trigger self.entries_spec()[position]]
            0 <= position < self.entries_spec().len() implies
                exists|previous: int| 0 <= previous < before.entries_spec().len()
                    && #[trigger] before.entries_spec()[previous].0 == self.entries_spec()[position].0
                    && before.entries_spec()[previous].1.0.0 == self.entries_spec()[position].1.0.0
                    && before.entries_spec()[previous].1.1 == self.entries_spec()[position].1.1 by {
            let previous = if remaining == 0 { position + 1 } else { position };
            assert(0 <= previous < before.entries_spec().len());
            assert(before.entries_spec()[previous].0 == self.entries_spec()[position].0);
            assert(before.entries_spec()[previous].1.0.0 == self.entries_spec()[position].1.0.0);
            assert(before.entries_spec()[previous].1.1 == self.entries_spec()[position].1.1);
        }
        Ok(())
    }
}

/// Why independently bounded fanout storage could not be admitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypedBranchFanoutBuildError {
    /// Branch custody requires two distinct caller-owned scopes.
    DuplicateScope,
    /// The left FIFO requires positive capacity in this profile.
    LeftZeroCapacity,
    /// The right FIFO requires positive capacity in this profile.
    RightZeroCapacity,
    /// Left FIFO or Registry storage could not be reserved.
    LeftStorageUnavailable,
    /// Right FIFO or Registry storage could not be reserved.
    RightStorageUnavailable,
}

/// Both original inputs returned by an unchanged paired-publication refusal.
#[derive(Debug)]
pub struct TypedBranchPublishRefusal<T> {
    /// Source or branch refusal observed before commit.
    pub error: TypedBranchFanoutError,
    /// Exact original left-branch content.
    pub left: T,
    /// Exact original right-branch content.
    pub right: T,
}

/// Per-branch custody profile of the same canonical two-branch fanout owner.
/// Each branch has independent slots, encoded-byte charges and original payload
/// custody. Both branch publications share the retained fanout Counter and commit
/// together. This profile does not change TypedFanout's shared-original policy.
pub struct TypedBranchFanout<T> {
    scopes: [u64; 2],
    flow: StreamGraphFanout<FifoStorage>,
    left: ResourceRegistry<u64, (T, u64), FifoStorage>,
    right: ResourceRegistry<u64, (T, u64), FifoStorage>,
    left_bytes: Budget,
    right_bytes: Budget,
    closed: Marker,
}

impl<T> TypedBranchFanout<T> {
    /// Original content retained by the selected branch Registry.
    pub closed spec fn entries_spec(&self, branch: FanoutBranch) -> Seq<(u64, (T, u64))> {
        match branch { FanoutBranch::Left => self.left.entries@, FanoutBranch::Right => self.right.entries@ }
    }
    /// Immutable caller-owned branch scope.
    pub closed spec fn scope_spec(&self, branch: FanoutBranch) -> u64 {
        match branch { FanoutBranch::Left => self.scopes[0], FanoutBranch::Right => self.scopes[1] }
    }
    /// Shared source-admission Counter, with no per-branch publication shadow.
    pub closed spec fn published_spec(&self) -> nat { self.flow.ingested.value_spec() }
    /// Immutable finite source bound.
    pub closed spec fn input_limit_spec(&self) -> nat { self.flow.max_inputs as nat }
    /// Consumed prefix owned by the selected fanout branch Counter.
    pub closed spec fn consumed_spec(&self, branch: FanoutBranch) -> nat { fanout_consumed(self.flow, branch) }
    /// Actual identity sequence in the selected fanout Buffer.
    pub closed spec fn queue_spec(&self, branch: FanoutBranch) -> Seq<u64> { fanout_queue(self.flow, branch) }
    /// Immutable retained-slot ceiling of the actual selected Buffer.
    pub closed spec fn slot_limit_spec(&self, branch: FanoutBranch) -> nat {
        match branch { FanoutBranch::Left => self.flow.left_queue.capacity as nat,
            FanoutBranch::Right => self.flow.right_queue.capacity as nat }
    }
    /// Immutable retained encoded-byte ceiling of the selected Budget.
    pub closed spec fn byte_limit_spec(&self, branch: FanoutBranch) -> nat {
        match branch { FanoutBranch::Left => self.left_bytes.capacity as nat,
            FanoutBranch::Right => self.right_bytes.capacity as nat }
    }
    /// Exact retained encoded-byte charge of the selected Budget.
    pub closed spec fn encoded_bytes_spec(&self, branch: FanoutBranch) -> nat {
        match branch { FanoutBranch::Left => self.left_bytes.allocated as nat,
            FanoutBranch::Right => self.right_bytes.allocated as nat }
    }
    /// Single producer closure Marker shared by both branches.
    pub closed spec fn closed_spec(&self) -> bool { self.closed.marked }
    /// Exact admission observed before paired publication.
    pub open spec fn publish_admitted_spec(&self, encoded_bytes: u64) -> bool {
        &&& self.published_spec() < self.input_limit_spec()
        &&& !self.closed_spec()
        &&& self.entries_spec(FanoutBranch::Left).len() < self.slot_limit_spec(FanoutBranch::Left)
        &&& self.entries_spec(FanoutBranch::Right).len() < self.slot_limit_spec(FanoutBranch::Right)
        &&& self.encoded_bytes_spec(FanoutBranch::Left) + encoded_bytes as nat <= self.byte_limit_spec(FanoutBranch::Left)
        &&& self.encoded_bytes_spec(FanoutBranch::Right) + encoded_bytes as nat <= self.byte_limit_spec(FanoutBranch::Right)
        &&& self.published_spec() < u64::MAX as nat
    }
    /// Coupling of actual fanout publication, FIFO custody and branch charge owners.
    pub closed spec fn inv(&self) -> bool {
        &&& self.scopes[0] != self.scopes[1]
        &&& self.flow.inv()
        &&& self.flow.record_domain_size == u64::MAX
        &&& self.left.unique_identities() && self.right.unique_identities()
        &&& self.left_bytes.safety_invariant() && self.right_bytes.safety_invariant()
        &&& self.left_bytes.reserved == 0 && self.left_bytes.pending_eviction == 0
        &&& self.right_bytes.reserved == 0 && self.right_bytes.pending_eviction == 0
        &&& self.left_bytes.allocated as int == crate::modalities::stream_graph::stream_bytes_to(self.left.entries@, self.left.entries@.len() as int)
        &&& self.right_bytes.allocated as int == crate::modalities::stream_graph::stream_bytes_to(self.right.entries@, self.right.entries@.len() as int)
        &&& self.left.entries@.len() == self.flow.left_queue.values@.len()
        &&& self.right.entries@.len() == self.flow.right_queue.values@.len()
        &&& forall|branch: FanoutBranch, index: int| 0 <= index < self.queue_spec(branch).len() ==>
            #[trigger] self.queue_spec(branch)[index] as int == self.consumed_spec(branch) as int + index
                && self.entries_spec(branch)[index].0 == self.queue_spec(branch)[index]
    }
    /// Logical stutter including all original payloads and governed limits.
    pub open spec fn same_state(&self, other: Self) -> bool {
        self.same_configuration(other) && self.published_spec() == other.published_spec()
            && self.closed_spec() == other.closed_spec()
            && forall|branch: FanoutBranch| self.entries_spec(branch) == other.entries_spec(branch)
                && self.queue_spec(branch) == other.queue_spec(branch)
                && self.consumed_spec(branch) == other.consumed_spec(branch)
                && self.encoded_bytes_spec(branch) == other.encoded_bytes_spec(branch)
    }
    /// Fixed branch scopes and source/branch limits preserved by every action.
    pub open spec fn same_configuration(&self, other: Self) -> bool {
        self.input_limit_spec() == other.input_limit_spec()
            && forall|branch: FanoutBranch| self.scope_spec(branch) == other.scope_spec(branch)
                && self.slot_limit_spec(branch) == other.slot_limit_spec(branch)
                && self.byte_limit_spec(branch) == other.byte_limit_spec(branch)
    }
    /// The existing bounded-transfer model projected from actual branch custody.
    pub open spec fn bounded_transfer_model(&self, branch: FanoutBranch) -> crate::modalities::stream_graph::BoundedTransferModel<T> {
        crate::modalities::stream_graph::BoundedTransferModel { slot_capacity: self.slot_limit_spec(branch), retained_byte_capacity: self.byte_limit_spec(branch),
            values: Seq::new(self.entries_spec(branch).len(), |i: int| self.entries_spec(branch)[i].1.0),
            registry: Seq::new(self.entries_spec(branch).len(), |i: int| (self.entries_spec(branch)[i].0, self.entries_spec(branch)[i].1.1)),
            retained_bytes: self.encoded_bytes_spec(branch), head: self.consumed_spec(branch),
            tail: self.published_spec(), closed: self.closed_spec() }
    }
    /// Export existing branch conservation, FIFO identity and charge correspondence.
    pub proof fn expose_bounded_transfer(&self, branch: FanoutBranch)
        requires self.inv(),
        ensures self.bounded_transfer_model(branch).inv(),
            self.consumed_spec(branch) + self.entries_spec(branch).len() == self.published_spec(),
            self.published_spec() <= self.input_limit_spec() <= usize::MAX as nat,
            self.published_spec() <= u64::MAX as nat,
            forall|i: int| 0 <= i < self.entries_spec(branch).len() ==>
                #[trigger] self.entries_spec(branch)[i].0 as nat == self.consumed_spec(branch) + i as nat,
    {
        self.flow.left_queue.expose_capacity_bound();
        self.flow.right_queue.expose_capacity_bound();
        match branch { FanoutBranch::Left => {}, FanoutBranch::Right => {} }
        let model = self.bounded_transfer_model(branch);
        assert forall|i: int| 0 <= i < self.entries_spec(branch).len() implies
            #[trigger] self.entries_spec(branch)[i].0 as nat == self.consumed_spec(branch) + i as nat by {
            assert(self.entries_spec(branch)[i].0 == self.queue_spec(branch)[i]);
        }
        assert forall|i: int| 0 <= i < model.registry.len() implies
            #[trigger] model.registry[i].0 as nat == model.head + i as nat by {
            assert(self.entries_spec(branch)[i].0 as nat == self.consumed_spec(branch) + i as nat);
        }
        assert forall|left: int, right: int| 0 <= left < model.registry.len()
            && 0 <= right < model.registry.len() && left != right implies
            #[trigger] model.registry[left].0 != #[trigger] model.registry[right].0 by {
            assert(model.registry[left].0 as nat == model.head + left as nat);
            assert(model.registry[right].0 as nat == model.head + right as nat);
        }
        assert(crate::primitives::resource_registry::unique_mapping_entries(model.registry));
        assert(crate::connectives::ordering_pass::fifo_sequence_order(model.registry, model.head, model.tail));
    }
    /// Reserve both actual FIFO and Registry backings before accepting any content.
    /// Byte ceilings may be zero; zero-charge content remains admissible.
    ///
    /// # Errors
    /// Returns duplicate-scope, zero-slot or branch-specific storage refusal.
    pub fn try_new(scopes: [u64; 2], slots: [usize; 2], encoded_bytes: [u64; 2], max_inputs: usize)
        -> (result: Result<Self, TypedBranchFanoutBuildError>)
        ensures result matches Ok(owner) ==> owner.inv() && owner.scope_spec(FanoutBranch::Left) == scopes[0]
            && owner.scope_spec(FanoutBranch::Right) == scopes[1]
            && owner.input_limit_spec() == max_inputs as nat && owner.published_spec() == 0 && !owner.closed_spec()
            && owner.slot_limit_spec(FanoutBranch::Left) == slots[0] as nat
            && owner.slot_limit_spec(FanoutBranch::Right) == slots[1] as nat
            && owner.byte_limit_spec(FanoutBranch::Left) == encoded_bytes[0] as nat
            && owner.byte_limit_spec(FanoutBranch::Right) == encoded_bytes[1] as nat
            && owner.entries_spec(FanoutBranch::Left).len() == 0 && owner.entries_spec(FanoutBranch::Right).len() == 0
            && owner.encoded_bytes_spec(FanoutBranch::Left) == 0 && owner.encoded_bytes_spec(FanoutBranch::Right) == 0
            && owner.consumed_spec(FanoutBranch::Left) == 0 && owner.consumed_spec(FanoutBranch::Right) == 0,
    {
        if scopes[0] == scopes[1] { return Err(TypedBranchFanoutBuildError::DuplicateScope); }
        if slots[0] == 0 { return Err(TypedBranchFanoutBuildError::LeftZeroCapacity); }
        if slots[1] == 0 { return Err(TypedBranchFanoutBuildError::RightZeroCapacity); }
        let left_queue = match Buffer::<u64, FifoStorage>::try_with_storage(slots[0]) {
            Ok(queue) => queue, Err(_) => return Err(TypedBranchFanoutBuildError::LeftStorageUnavailable),
        };
        let mut left = ResourceRegistry::new_fifo();
        if left.try_reserve_entries(slots[0]).is_err() { return Err(TypedBranchFanoutBuildError::LeftStorageUnavailable); }
        let right_queue = match Buffer::<u64, FifoStorage>::try_with_storage(slots[1]) {
            Ok(queue) => queue, Err(_) => return Err(TypedBranchFanoutBuildError::RightStorageUnavailable),
        };
        let mut right = ResourceRegistry::new_fifo();
        if right.try_reserve_entries(slots[1]).is_err() { return Err(TypedBranchFanoutBuildError::RightStorageUnavailable); }
        Ok(Self { scopes, flow: StreamGraphFanout::with_buffers(left_queue, right_queue, max_inputs, u64::MAX),
            left, right, left_bytes: Budget::new(encoded_bytes[0]), right_bytes: Budget::new(encoded_bytes[1]), closed: Marker::new(false) })
    }
    /// Shared source count read from its sole Counter.
    pub fn published_count(&self) -> (count: u64) requires self.inv(), ensures count as nat == self.published_spec(),
    { self.flow.ingested.value() }
    /// Finite source limit supplied at construction.
    pub fn input_limit(&self) -> (limit: usize) requires self.inv(), ensures limit as nat == self.input_limit_spec(),
    { self.flow.max_inputs }
    /// Selected branch receipt count read from its canonical Counter.
    pub fn received_count(&self, branch: FanoutBranch) -> (count: u64) requires self.inv(), ensures count as nat == self.consumed_spec(branch),
    { match branch { FanoutBranch::Left => self.flow.left_emitted.value(), FanoutBranch::Right => self.flow.right_emitted.value() } }
    /// Current selected branch occupancy read from its Buffer.
    pub fn len(&self, branch: FanoutBranch) -> (length: usize) requires self.inv(), ensures length as nat == self.entries_spec(branch).len(),
    { match branch { FanoutBranch::Left => self.flow.left_queue.len(), FanoutBranch::Right => self.flow.right_queue.len() } }
    /// Whether the selected actual branch FIFO has drained.
    pub fn is_empty(&self, branch: FanoutBranch) -> (empty: bool) requires self.inv(),
        ensures empty == (self.entries_spec(branch).len() == 0),
    { match branch { FanoutBranch::Left => self.flow.left_queue.is_empty(), FanoutBranch::Right => self.flow.right_queue.is_empty() } }
    /// Whether finite source completion or closure and both branch drainages hold.
    pub fn is_terminal(&self) -> (terminal: bool) requires self.inv(),
        ensures terminal == ((self.published_spec() == self.input_limit_spec() || self.closed_spec())
            && self.entries_spec(FanoutBranch::Left).len() == 0 && self.entries_spec(FanoutBranch::Right).len() == 0),
    { self.flow.terminal() || (self.closed.is_marked() && self.flow.left_queue.is_empty() && self.flow.right_queue.is_empty()) }
    /// Selected branch encoded-byte charge read from its Budget.
    pub fn retained_bytes(&self, branch: FanoutBranch) -> (bytes: u64) requires self.inv(), ensures bytes as nat == self.encoded_bytes_spec(branch),
    { match branch { FanoutBranch::Left => self.left_bytes.allocated, FanoutBranch::Right => self.right_bytes.allocated } }
    /// Selected branch retained-slot ceiling read from its Buffer.
    pub fn slot_capacity(&self, branch: FanoutBranch) -> (slots: usize) requires self.inv(), ensures slots as nat == self.slot_limit_spec(branch),
    { match branch { FanoutBranch::Left => self.flow.left_queue.capacity, FanoutBranch::Right => self.flow.right_queue.capacity } }
    /// Selected branch encoded-byte ceiling read from its Budget.
    pub fn byte_capacity(&self, branch: FanoutBranch) -> (bytes: u64) requires self.inv(), ensures bytes as nat == self.byte_limit_spec(branch),
    { match branch { FanoutBranch::Left => self.left_bytes.capacity, FanoutBranch::Right => self.right_bytes.capacity } }
    /// Single producer closure read from its Marker.
    pub fn is_closed(&self) -> (closed: bool) requires self.inv(), ensures closed == self.closed_spec(),
    { self.closed.is_marked() }
    /// Observe one branch's unchanged publication guards in item-size-first order.
    fn check_branch(&self, branch: FanoutBranch, encoded_bytes: u64) -> (result: Result<(), TypedStreamError>)
        requires self.inv(),
        ensures (result is Ok) == (!self.closed_spec()
            && self.entries_spec(branch).len() < self.slot_limit_spec(branch)
            && self.encoded_bytes_spec(branch) + encoded_bytes as nat <= self.byte_limit_spec(branch)
            && self.published_spec() < u64::MAX as nat),
    {
        if self.closed.is_marked() { return Err(TypedStreamError::Closed); }
        let (slots, length, bytes) = match branch {
            FanoutBranch::Left => (self.flow.left_queue.capacity, self.flow.left_queue.len(), &self.left_bytes),
            FanoutBranch::Right => (self.flow.right_queue.capacity, self.flow.right_queue.len(), &self.right_bytes),
        };
        if encoded_bytes > bytes.capacity { return Err(TypedStreamError::ItemTooLarge); }
        if length >= slots { return Err(TypedStreamError::SlotCapacity); }
        if !bytes.admits_additional(encoded_bytes, 0) { return Err(TypedStreamError::ByteCapacity); }
        if !self.flow.ingested.can_increment() { return Err(TypedStreamError::SequenceExhausted); }
        Ok(())
    }
    /// Observe source-limit, then left and right branch admission without mutation.
    ///
    /// # Errors
    /// Source-limit refusal precedes left-first item-size/slot/byte/identity checks.
    pub fn check_publish(&self, encoded_bytes: u64) -> (result: Result<(), TypedBranchFanoutError>)
        requires self.inv(), ensures (result is Ok) == self.publish_admitted_spec(encoded_bytes),
    {
        if self.flow.ingested.value() >= self.flow.max_inputs as u64 { return Err(TypedBranchFanoutError::InputLimitReached); }
        if let Err(error) = self.check_branch(FanoutBranch::Left, encoded_bytes) { return Err(TypedBranchFanoutError::Left(error)); }
        if let Err(error) = self.check_branch(FanoutBranch::Right, encoded_bytes) { return Err(TypedBranchFanoutError::Right(error)); }
        Ok(())
    }
    /// Publish both originals atomically through the actual fanout owner actions.
    /// All storage was reserved at construction; refusal returns both inputs.
    ///
    /// # Errors
    /// Returns the unchanged pair on the exact source or first branch refusal.
    pub fn publish_pair(&mut self, left: T, right: T, encoded_bytes: u64)
        -> (result: Result<u64, TypedBranchPublishRefusal<T>>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).same_configuration(*old(self)),
            final(self).closed_spec() == old(self).closed_spec(),
            final(self).consumed_spec(FanoutBranch::Left) == old(self).consumed_spec(FanoutBranch::Left),
            final(self).consumed_spec(FanoutBranch::Right) == old(self).consumed_spec(FanoutBranch::Right),
            (result is Ok) == old(self).publish_admitted_spec(encoded_bytes),
            result matches Err(refusal) ==> refusal.left == left && refusal.right == right && final(self).same_state(*old(self)),
            result matches Ok(sequence) ==> sequence as nat == old(self).published_spec()
                && final(self).published_spec() == old(self).published_spec() + 1
                && final(self).entries_spec(FanoutBranch::Left) == old(self).entries_spec(FanoutBranch::Left).push((sequence, (left, encoded_bytes)))
                && final(self).entries_spec(FanoutBranch::Right) == old(self).entries_spec(FanoutBranch::Right).push((sequence, (right, encoded_bytes)))
                && final(self).encoded_bytes_spec(FanoutBranch::Left) == old(self).encoded_bytes_spec(FanoutBranch::Left) + encoded_bytes as nat
                && final(self).encoded_bytes_spec(FanoutBranch::Right) == old(self).encoded_bytes_spec(FanoutBranch::Right) + encoded_bytes as nat,
    {
        if let Err(error) = self.check_publish(encoded_bytes) { return Err(TypedBranchPublishRefusal { error, left, right }); }
        let sequence = self.flow.ingested.value();
        let ghost before = *self;
        proof {
            crate::primitives::resource_registry::identity_entries_are_exact(self.left.entries@);
            crate::primitives::resource_registry::identity_entries_are_exact(self.right.entries@);
            assert(!self.left.contains_key_identity(sequence)) by {
                if self.left.contains_key_identity(sequence) {
                    let i = choose|i: int| 0 <= i < self.left.entries@.len() && #[trigger] self.left.entries@[i].0 == sequence;
                    assert(self.queue_spec(FanoutBranch::Left)[i] as int == self.consumed_spec(FanoutBranch::Left) as int + i);
                    assert(false);
                }
            }
            assert(!self.right.contains_key_identity(sequence)) by {
                if self.right.contains_key_identity(sequence) {
                    let i = choose|i: int| 0 <= i < self.right.entries@.len() && #[trigger] self.right.entries@[i].0 == sequence;
                    assert(self.queue_spec(FanoutBranch::Right)[i] as int == self.consumed_spec(FanoutBranch::Right) as int + i);
                    assert(false);
                }
            }
        }
        let _left_charged = self.left_bytes.try_allocate(encoded_bytes);
        let _right_charged = self.right_bytes.try_allocate(encoded_bytes);
        self.left.register_absent_key(sequence, (left, encoded_bytes));
        self.right.register_absent_key(sequence, (right, encoded_bytes));
        let _published = self.flow.source_ingest(sequence);
        assert(_left_charged && _right_charged && _published);
        proof {
            crate::modalities::stream_graph::stream_bytes_append_prefix(before.left.entries@, (sequence, (left, encoded_bytes)), before.left.entries@.len() as int);
            crate::modalities::stream_graph::stream_bytes_append_prefix(before.right.entries@, (sequence, (right, encoded_bytes)), before.right.entries@.len() as int);
        }
        assert forall|branch: FanoutBranch, i: int| 0 <= i < self.queue_spec(branch).len() implies
            #[trigger] self.queue_spec(branch)[i] as int == self.consumed_spec(branch) as int + i
                && self.entries_spec(branch)[i].0 == self.queue_spec(branch)[i] by {
            match branch { FanoutBranch::Left => {}, FanoutBranch::Right => {} }
            if i < before.queue_spec(branch).len() { assert(self.queue_spec(branch)[i] == before.queue_spec(branch)[i]); }
        }
        assert(self.inv());
        Ok(sequence)
    }
    /// Transfer the selected branch's oldest original and release only its charge.
    ///
    /// # Errors
    /// Returns Empty while open, or Closed after the selected closed FIFO drains.
    pub fn receive(&mut self, branch: FanoutBranch) -> (result: Result<ReceivedStreamValue<T>, TypedStreamError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).same_configuration(*old(self)),
            final(self).published_spec() == old(self).published_spec(), final(self).closed_spec() == old(self).closed_spec(),
            (result is Ok) == (old(self).entries_spec(branch).len() > 0),
            (result == Err(TypedStreamError::Empty)) == (old(self).entries_spec(branch).len() == 0 && !old(self).closed_spec()),
            (result == Err(TypedStreamError::Closed)) == (old(self).entries_spec(branch).len() == 0 && old(self).closed_spec()),
            result is Err ==> final(self).same_state(*old(self)),
            result matches Ok(item) ==> item.scope == old(self).scope_spec(branch)
                && item.sequence == old(self).entries_spec(branch)[0].0 && item.value == old(self).entries_spec(branch)[0].1.0
                && item.encoded_bytes == old(self).entries_spec(branch)[0].1.1
                && final(self).entries_spec(branch) == old(self).entries_spec(branch).skip(1)
                && final(self).encoded_bytes_spec(branch) + item.encoded_bytes as nat == old(self).encoded_bytes_spec(branch)
                && final(self).consumed_spec(branch) == old(self).consumed_spec(branch) + 1,
            forall|other: FanoutBranch| other != branch ==> final(self).entries_spec(other) == old(self).entries_spec(other)
                && final(self).encoded_bytes_spec(other) == old(self).encoded_bytes_spec(other)
                && final(self).consumed_spec(other) == old(self).consumed_spec(other),
    {
        if self.len(branch) == 0 { return Err(if self.closed.is_marked() { TypedStreamError::Closed } else { TypedStreamError::Empty }); }
        let ghost before = *self;
        let entry = match branch {
            FanoutBranch::Left => {
                let _consumed = self.flow.consume_left();
                assert(_consumed);
                let entry = match self.left.deregister_identity_at(0) { Some(entry) => entry, None => { assert(false); return Err(TypedStreamError::Empty); } };
                proof {
                    assert(self.left.entries@ =~= before.left.entries@.skip(1));
                    crate::modalities::stream_graph::stream_bytes_drop_first(before.left.entries@, before.left.entries@.len() as int);
                    crate::modalities::stream_graph::stream_bytes_nonnegative(self.left.entries@, self.left.entries@.len() as int);
                    assert(entry.1.1 <= self.left_bytes.allocated);
                }
                self.left_bytes.release(entry.1.1);
                entry
            }
            FanoutBranch::Right => {
                let _consumed = self.flow.consume_right();
                assert(_consumed);
                let entry = match self.right.deregister_identity_at(0) { Some(entry) => entry, None => { assert(false); return Err(TypedStreamError::Empty); } };
                proof {
                    assert(self.right.entries@ =~= before.right.entries@.skip(1));
                    crate::modalities::stream_graph::stream_bytes_drop_first(before.right.entries@, before.right.entries@.len() as int);
                    crate::modalities::stream_graph::stream_bytes_nonnegative(self.right.entries@, self.right.entries@.len() as int);
                    assert(entry.1.1 <= self.right_bytes.allocated);
                }
                self.right_bytes.release(entry.1.1);
                entry
            }
        };
        assert forall|selected: FanoutBranch, i: int| 0 <= i < self.queue_spec(selected).len() implies
            #[trigger] self.queue_spec(selected)[i] as int == self.consumed_spec(selected) as int + i
                && self.entries_spec(selected)[i].0 == self.queue_spec(selected)[i] by {
            match selected { FanoutBranch::Left => {}, FanoutBranch::Right => {} }
            if selected == branch {
                assert(self.consumed_spec(selected) == before.consumed_spec(selected) + 1);
                assert(self.entries_spec(selected) == before.entries_spec(selected).skip(1));
                assert(self.queue_spec(selected)[i] == before.queue_spec(selected)[i + 1]);
                assert(self.entries_spec(selected)[i] == before.entries_spec(selected)[i + 1]);
                assert(0 <= i + 1 < before.queue_spec(selected).len());
                assert(before.queue_spec(selected)[i + 1] as int == before.consumed_spec(selected) as int + i + 1);
                assert(before.entries_spec(selected)[i + 1].0 == before.queue_spec(selected)[i + 1]);
            } else {
                assert(self.entries_spec(selected) == before.entries_spec(selected));
                assert(self.queue_spec(selected) == before.queue_spec(selected));
                assert(self.consumed_spec(selected) == before.consumed_spec(selected));
                assert(before.queue_spec(selected)[i] as int == before.consumed_spec(selected) as int + i);
                assert(before.entries_spec(selected)[i].0 == before.queue_spec(selected)[i]);
            }
        }
        assert(self.inv());
        Ok(ReceivedStreamValue { scope: self.branch_scope(branch), sequence: entry.0, value: entry.1.0, encoded_bytes: entry.1.1 })
    }
    fn branch_scope(&self, branch: FanoutBranch) -> (scope: u64) ensures scope == self.scope_spec(branch),
    { match branch { FanoutBranch::Left => self.scopes[0], FanoutBranch::Right => self.scopes[1] } }
    /// Close the producer once while preserving independently drainable custody.
    pub fn close_input(&mut self) -> (changed: bool)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).same_configuration(*old(self)), final(self).closed_spec(), changed == !old(self).closed_spec(),
            final(self).published_spec() == old(self).published_spec(),
            forall|branch: FanoutBranch| final(self).entries_spec(branch) == old(self).entries_spec(branch)
                && final(self).encoded_bytes_spec(branch) == old(self).encoded_bytes_spec(branch)
                && final(self).consumed_spec(branch) == old(self).consumed_spec(branch),
    {
        let ghost before = *self;
        let changed = self.closed.set();
        assert forall|branch: FanoutBranch, i: int| 0 <= i < self.queue_spec(branch).len() implies
            #[trigger] self.queue_spec(branch)[i] as int == self.consumed_spec(branch) as int + i
                && self.entries_spec(branch)[i].0 == self.queue_spec(branch)[i] by {
            match branch { FanoutBranch::Left => {}, FanoutBranch::Right => {} }
            assert(self.queue_spec(branch) == before.queue_spec(branch));
            assert(self.entries_spec(branch) == before.entries_spec(branch));
            assert(self.consumed_spec(branch) == before.consumed_spec(branch));
            assert(before.queue_spec(branch)[i] as int == before.consumed_spec(branch) as int + i);
            assert(before.entries_spec(branch)[i].0 == before.queue_spec(branch)[i]);
        }
        assert(self.inv());
        changed
    }
}

/// Retained verification profile for a source fanning out to two FIFO sinks.
pub struct StreamGraphFanout<S: BufferLayout<u64> = ContiguousStorage> {
    /// Maximum records admitted by the source.
    pub max_inputs: usize,
    /// Exclusive upper bound of record values.
    pub record_domain_size: u64,
    /// Left-branch FIFO owner.
    pub left_queue: Buffer<u64, S>,
    /// Right-branch FIFO owner.
    pub right_queue: Buffer<u64, S>,
    /// Source-admission counter.
    pub ingested: Counter,
    /// Left-sink emission counter.
    pub left_emitted: Counter,
    /// Right-sink emission counter.
    pub right_emitted: Counter,
}

impl<S: BufferLayout<u64>> StreamGraphFanout<S> {
    /// Oldest original still named by at least one actual branch Buffer.
    pub fn retained_head(&self) -> (head: u64) requires self.inv(),
        ensures head as nat == if self.left_emitted.value_spec() < self.right_emitted.value_spec() {
            self.left_emitted.value_spec() } else { self.right_emitted.value_spec() },
    {
        let left = self.left_emitted.value();
        let right = self.right_emitted.value();
        if left < right { left } else { right }
    }
    /// Whether every queued value lies within `domain`.
    pub open spec fn values_valid(q: Seq<u64>, domain: u64) -> bool {
        forall|i: int| 0 <= i < q.len() ==> #[trigger] q[i] < domain
    }

    /// Whether counters, queues, and configuration values have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.left_queue.capacity > 0
        &&& self.right_queue.capacity > 0
        &&& self.record_domain_size > 0
        &&& Self::values_valid(self.left_queue.values@, self.record_domain_size)
        &&& Self::values_valid(self.right_queue.values@, self.record_domain_size)
        &&& self.ingested.value_spec() <= self.max_inputs as nat
        &&& self.left_emitted.value_spec() <= self.max_inputs as nat
        &&& self.right_emitted.value_spec() <= self.max_inputs as nat
    }

    /// Whether either full branch prevents another broadcast.
    pub open spec fn backpressure_correct(&self) -> bool {
        self.left_queue.well_formed() && self.right_queue.well_formed()
    }

    /// Whether each branch independently conserves admitted records.
    pub open spec fn per_branch_conservation(&self) -> bool {
        &&& self.ingested.value_spec()
            == self.left_queue.values@.len() + self.left_emitted.value_spec()
        &&& self.ingested.value_spec()
            == self.right_queue.values@.len() + self.right_emitted.value_spec()
    }

    /// Whether all fan-out stream contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.backpressure_correct()
            && self.per_branch_conservation()
    }

}
impl StreamGraphFanout {
    /// Test whether the shared queue capacity and value domain are valid.
    pub fn valid_config(capacity: usize, record_domain_size: u64) -> (valid: bool)
        ensures valid == (capacity > 0 && record_domain_size > 0),
    {
        capacity > 0 && record_domain_size > 0
    }

    /// Construct an empty valid fan-out execution.
    pub fn new(
        capacity: usize,
        max_inputs: usize,
        record_domain_size: u64,
    ) -> (s: StreamGraphFanout)
        requires capacity > 0, record_domain_size > 0,
        ensures
            s.left_queue.capacity == capacity,
            s.right_queue.capacity == capacity,
            s.max_inputs == max_inputs,
            s.record_domain_size == record_domain_size,
            s.left_queue.values@.len() == 0,
            s.right_queue.values@.len() == 0,
            s.ingested.value_spec() == 0,
            s.left_emitted.value_spec() == 0,
            s.right_emitted.value_spec() == 0,
            s.inv(),
    {
        Self::with_buffers(Buffer::new(capacity), Buffer::new(capacity), max_inputs, record_domain_size)
    }
}

impl<S: BufferLayout<u64>> StreamGraphFanout<S> {
    /// Bind empty canonical Buffers to the same fanout transition owner.
    pub fn with_buffers(left_queue: Buffer<u64, S>, right_queue: Buffer<u64, S>,
        max_inputs: usize, record_domain_size: u64) -> (flow: Self)
        requires left_queue.well_formed(), right_queue.well_formed(),
            left_queue.capacity > 0, right_queue.capacity > 0,
            left_queue.values@.len() == 0, right_queue.values@.len() == 0,
            record_domain_size > 0,
        ensures flow.inv(), flow.left_queue == left_queue, flow.right_queue == right_queue,
            flow.max_inputs == max_inputs, flow.record_domain_size == record_domain_size,
            flow.ingested.value_spec() == 0, flow.left_emitted.value_spec() == 0,
            flow.right_emitted.value_spec() == 0,
    {
        Self {
            max_inputs, record_domain_size, left_queue, right_queue,
            ingested: Counter::new(0),
            left_emitted: Counter::new(0),
            right_emitted: Counter::new(0),
        }
    }

    /// Replicate one source record into both branch queues.
    pub fn source_ingest(&mut self, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (value < old(self).record_domain_size
                && old(self).ingested.value_spec() < old(self).max_inputs as nat
                && old(self).left_queue.values@.len() < old(self).left_queue.capacity
                && old(self).right_queue.values@.len() < old(self).right_queue.capacity),
            final(self).left_queue.capacity == old(self).left_queue.capacity,
            final(self).right_queue.capacity == old(self).right_queue.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue.values@ == if accepted {
                old(self).left_queue.values@.push(value)
            } else { old(self).left_queue.values@ },
            final(self).right_queue.values@ == if accepted {
                old(self).right_queue.values@.push(value)
            } else { old(self).right_queue.values@ },
            accepted ==> final(self).ingested.value_spec()
                == old(self).ingested.value_spec() + 1,
            !accepted ==> final(self).ingested.value_spec()
                == old(self).ingested.value_spec(),
            final(self).left_emitted.value_spec() == old(self).left_emitted.value_spec(),
            final(self).right_emitted.value_spec() == old(self).right_emitted.value_spec(),
            final(self).inv(),
    {
        if value < self.record_domain_size
            && self.ingested.value() < self.max_inputs as u64
            && self.left_queue.len() < self.left_queue.capacity
            && self.right_queue.len() < self.right_queue.capacity
        {
            let ghost old_left = self.left_queue.values@;
            let ghost old_right = self.right_queue.values@;
            let _left_pushed = self.left_queue.push(value);
            let _right_pushed = self.right_queue.push(value);
            let _counted = self.ingested.try_increment();
            assert(_counted);
            assert forall|i: int| 0 <= i < self.left_queue.values@.len()
                implies #[trigger] self.left_queue.values@[i] < self.record_domain_size by {
                if i < old_left.len() {
                    assert(self.left_queue.values@[i] == old_left[i]);
                }
            }
            assert forall|i: int| 0 <= i < self.right_queue.values@.len()
                implies #[trigger] self.right_queue.values@[i] < self.record_domain_size by {
                if i < old_right.len() {
                    assert(self.right_queue.values@[i] == old_right[i]);
                }
            }
            true
        } else {
            false
        }
    }

    /// Consume one record from the left FIFO branch.
    pub fn consume_left(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).left_queue.values@.len() > 0),
            final(self).left_queue.capacity == old(self).left_queue.capacity,
            final(self).right_queue.capacity == old(self).right_queue.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue.values@ == if accepted {
                old(self).left_queue.values@.subrange(1, old(self).left_queue.values@.len() as int)
            } else { old(self).left_queue.values@ },
            final(self).right_queue.values@ == old(self).right_queue.values@,
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            accepted ==> final(self).left_emitted.value_spec()
                == old(self).left_emitted.value_spec() + 1,
            !accepted ==> final(self).left_emitted.value_spec()
                == old(self).left_emitted.value_spec(),
            final(self).right_emitted.value_spec() == old(self).right_emitted.value_spec(),
            final(self).inv(),
    {
        if self.left_queue.len() > 0 {
            let ghost old_left = self.left_queue.values@;
            let _popped = self.left_queue.pop();
            let _counted = self.left_emitted.try_increment();
            assert(_counted);
            assert(self.left_queue.values@ =~=
                old_left.subrange(1, old_left.len() as int));
            true
        } else {
            false
        }
    }

    /// Consume one record from the right FIFO branch.
    pub fn consume_right(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).right_queue.values@.len() > 0),
            final(self).left_queue.capacity == old(self).left_queue.capacity,
            final(self).right_queue.capacity == old(self).right_queue.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).left_queue.values@ == old(self).left_queue.values@,
            final(self).right_queue.values@ == if accepted {
                old(self).right_queue.values@.subrange(1, old(self).right_queue.values@.len() as int)
            } else { old(self).right_queue.values@ },
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            final(self).left_emitted.value_spec() == old(self).left_emitted.value_spec(),
            accepted ==> final(self).right_emitted.value_spec()
                == old(self).right_emitted.value_spec() + 1,
            !accepted ==> final(self).right_emitted.value_spec()
                == old(self).right_emitted.value_spec(),
            final(self).inv(),
    {
        if self.right_queue.len() > 0 {
            let ghost old_right = self.right_queue.values@;
            let _popped = self.right_queue.pop();
            let _counted = self.right_emitted.try_increment();
            assert(_counted);
            assert(self.right_queue.values@ =~=
                old_right.subrange(1, old_right.len() as int));
            true
        } else {
            false
        }
    }

    /// Whether bounded input was admitted and both branches are drained.
    pub fn terminal(&self) -> (terminal: bool)
        requires self.inv(),
        ensures terminal == (self.ingested.value_spec() == self.max_inputs as nat
            && self.left_queue.values@.len() == 0
            && self.right_queue.values@.len() == 0),
    {
        self.ingested.value() == self.max_inputs as u64
            && self.left_queue.len() == 0
            && self.right_queue.len() == 0
    }
}

}
