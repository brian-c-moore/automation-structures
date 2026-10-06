// Executable carrier for the bounded one-source/two-sink StreamGraph fan-out
// profile. A source commit broadcasts one value to both queues. Rejected calls
// stutter, and conservation is stated independently for each branch.

use vstd::prelude::*;

use crate::connectives::buffer::Buffer;
use crate::connectives::counter::Counter;
use crate::connectives::marker::Marker;
use crate::modalities::stream_graph::TypedPublishRefusal;
use crate::primitives::budget::Budget;
use crate::primitives::resource_registry::ResourceRegistry;

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
    flow: StreamGraphFanout,
    payloads: ResourceRegistry<u64, ((T, Counter), u64)>,
    bytes: Budget,
    closed: Marker,
}

pub(crate) open spec fn fanout_queue(flow: StreamGraphFanout, branch: FanoutBranch) -> Seq<u64> {
    match branch { FanoutBranch::Left => flow.left_queue.values@,
        FanoutBranch::Right => flow.right_queue.values@ }
}
pub(crate) open spec fn fanout_consumed(flow: StreamGraphFanout, branch: FanoutBranch) -> nat {
    match branch { FanoutBranch::Left => flow.left_emitted.value_spec(),
        FanoutBranch::Right => flow.right_emitted.value_spec() }
}
pub(crate) open spec fn fanout_head(flow: StreamGraphFanout) -> nat {
    if flow.left_emitted.value_spec() < flow.right_emitted.value_spec() {
        flow.left_emitted.value_spec() } else { flow.right_emitted.value_spec() }
}
pub(crate) open spec fn fanout_references(flow: StreamGraphFanout, sequence: u64) -> nat {
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
        let mut flow = StreamGraphFanout::new(capacity, usize::MAX, u64::MAX);
        flow.left_queue = match Buffer::try_new(capacity) {
            Ok(queue) => queue, Err(_) => return Err(TypedFanoutError::StorageUnavailable),
        };
        flow.right_queue = match Buffer::try_new(capacity) {
            Ok(queue) => queue, Err(_) => return Err(TypedFanoutError::StorageUnavailable),
        };
        Ok(Self { scope, flow, payloads: ResourceRegistry::new(), bytes: Budget::new(encoded_bytes),
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
            assert(!self.payloads.contains_key(sequence)) by {
                if self.payloads.contains_key(sequence) {
                    let index = choose|index: int| 0 <= index < self.payloads.entries@.len()
                        && #[trigger] self.payloads.entries@[index].0 == sequence;
                    assert(false);
                }
            }
        }
        let references = Counter::new(2);
        self.payloads.register(sequence, ((value, references), encoded_bytes));
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
        let sequence = match branch { FanoutBranch::Left => self.flow.left_queue.values[0], FanoutBranch::Right => self.flow.right_queue.values[0] };
        proof {
            let index = sequence as int - self.retained_head_spec() as int;
            assert(0 <= index < self.payloads.entries@.len());
            assert(self.payloads.entries@[index].0 == sequence);
            crate::primitives::resource_registry::identity_entry_at(self.payloads.entries@, index);
            assert(self.payloads.contains_key_identity(sequence));
        }
        match self.payloads.lookup_query(&sequence) {
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
        match self.payloads.lookup_query(&sequence) {
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
        let sequence = match token.branch { FanoutBranch::Left => self.flow.left_queue.values[0], FanoutBranch::Right => self.flow.right_queue.values[0] };
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

/// Retained verification profile for a source fanning out to two FIFO sinks.
pub struct StreamGraphFanout {
    /// Maximum records admitted by the source.
    pub max_inputs: usize,
    /// Exclusive upper bound of record values.
    pub record_domain_size: u64,
    /// Left-branch FIFO owner.
    pub left_queue: Buffer<u64>,
    /// Right-branch FIFO owner.
    pub right_queue: Buffer<u64>,
    /// Source-admission counter.
    pub ingested: Counter,
    /// Left-sink emission counter.
    pub left_emitted: Counter,
    /// Right-sink emission counter.
    pub right_emitted: Counter,
}

impl StreamGraphFanout {
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
        &&& self.right_queue.capacity == self.left_queue.capacity
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
        StreamGraphFanout {
            max_inputs,
            record_domain_size,
            left_queue: Buffer::new(capacity),
            right_queue: Buffer::new(capacity),
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
