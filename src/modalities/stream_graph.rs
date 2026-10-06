// Faithful executable carrier for the specified three- and four-node StreamGraph chains.
// q1, q2, and q3 correspond exactly to the named TLA+ edge queues; q3 is
// empty for a three-node chain. Rejected calls stutter.

use vstd::prelude::*;

use crate::connectives::buffer::Buffer;
use crate::connectives::counter::Counter;
use crate::connectives::cursor::Cursor;
use crate::connectives::marker::Marker;
use crate::primitives::budget::Budget;
use crate::primitives::resource_registry::ResourceRegistry;

verus! {

/// Checked construction, publication, or receipt refusal for a typed FIFO.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypedStreamError {
    /// Buffer or Registry backing could not be reserved before construction.
    StorageUnavailable,
    /// The retained-slot Budget refused publication.
    SlotCapacity,
    /// The retained encoded-byte Budget refused publication.
    ByteCapacity,
    /// The next FIFO identity cannot be represented.
    SequenceExhausted,
    /// Producer closure forbids publication, or the closed FIFO has drained.
    Closed,
    /// The open FIFO has no value available for receipt.
    Empty,
}

/// Publication refusal returning the exact original, unconsumed payload.
#[derive(Debug)]
pub struct TypedPublishRefusal<T, E = TypedStreamError> {
    /// Owner action that refused the publication.
    pub error: E,
    /// Original input retained by the caller after refusal.
    pub value: T,
}

/// Original payload transferred out of a typed FIFO, with its issued identity.
#[derive(Debug)]
pub struct ReceivedStreamValue<T> {
    /// Caller-owned root scope supplied at construction.
    pub scope: u64,
    /// Monotone identity of this publication within that scope.
    pub sequence: u64,
    /// Original payload, moved without cloning.
    pub value: T,
    /// Encoded-byte charge released when custody transfers to the caller.
    pub encoded_bytes: u64,
}

/// Mathematical charge over the actual Registry's retained prefix.
pub open spec fn stream_bytes_to<T>(entries: Seq<(u64, (T, u64))>, end: int) -> int
    decreases end,
{
    if end <= 0 || end > entries.len() { 0 }
    else { stream_bytes_to(entries, end - 1) + entries[end - 1].1.1 as int }
}

pub(crate) proof fn stream_bytes_drop_first<T>(entries: Seq<(u64, (T, u64))>, end: int)
    requires 1 <= end <= entries.len(),
    ensures stream_bytes_to(entries.skip(1), end - 1)
        + entries[0].1.1 as int == stream_bytes_to(entries, end),
    decreases end,
{
    reveal_with_fuel(stream_bytes_to, 2);
    if end > 1 {
        stream_bytes_drop_first(entries, end - 1);
        assert(entries.skip(1)[end - 2] == entries[end - 1]);
    }
}

pub(crate) proof fn stream_bytes_nonnegative<T>(entries: Seq<(u64, (T, u64))>, end: int)
    requires 0 <= end <= entries.len(),
    ensures 0 <= stream_bytes_to(entries, end),
    decreases end,
{
    if end > 0 { stream_bytes_nonnegative(entries, end - 1); }
}

pub(crate) proof fn stream_bytes_append_prefix<T>(entries: Seq<(u64, (T, u64))>, added: (u64,(T,u64)), end: int)
    requires 0 <= end <= entries.len(),
    ensures stream_bytes_to(entries.push(added), end) == stream_bytes_to(entries, end),
    decreases end,
{
    reveal_with_fuel(stream_bytes_to, 2);
    if end > 0 {
        stream_bytes_append_prefix(entries, added, end - 1);
        assert(entries.push(added)[end - 1] == entries[end - 1]);
    }
}

pub(crate) proof fn stream_bytes_same_charges<T>(before: Seq<(u64,(T,u64))>, after: Seq<(u64,(T,u64))>, end: int)
    requires before.len() == after.len(), 0 <= end <= before.len(),
        forall|index: int| 0 <= index < end ==> #[trigger] before[index].1.1 == after[index].1.1,
    ensures stream_bytes_to(before, end) == stream_bytes_to(after, end),
    decreases end,
{
    if end > 0 { stream_bytes_same_charges(before, after, end - 1); }
}

/// Persistent typed linear StreamGraph profile built from the canonical owners.
/// Registry retains original payloads; Buffer retains only FIFO identities.
/// Encoded bytes cover this owner's retained content until receipt transfers it
/// to the caller. They are not a total or peak physical-memory measurement.
/// The current Buffer/Registry layouts move remaining entries on receipt.
pub struct TypedStream<T> {
    scope: u64,
    payloads: ResourceRegistry<u64, (T, u64)>,
    queue: Buffer<u64>,
    slots: Budget,
    bytes: Budget,
    published: Counter,
    consumed: Cursor,
    closed: Marker,
}

impl<T> TypedStream<T> {
    /// Original payloads and their exact Registry-issued FIFO identities.
    pub closed spec fn entries_spec(&self) -> Seq<(u64, (T, u64))> { self.payloads.entries@ }
    /// Immutable caller-owned scope.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Retained FIFO identity sequence owned by Buffer.
    pub closed spec fn queue_spec(&self) -> Seq<u64> { self.queue.values@ }
    /// Exact committed publication count.
    pub closed spec fn published_spec(&self) -> nat { self.published.value_spec() }
    /// Exact consumed prefix owned by Cursor.
    pub closed spec fn consumed_spec(&self) -> nat { self.consumed.position as nat }
    /// Producer closure owned by Marker.
    pub closed spec fn closed_spec(&self) -> bool { self.closed.marked }
    /// Immutable retained-slot ceiling.
    pub closed spec fn slot_limit_spec(&self) -> nat { self.slots.capacity as nat }
    /// Immutable encoded-byte ceiling.
    pub closed spec fn byte_limit_spec(&self) -> nat { self.bytes.capacity as nat }
    /// Exact retained encoded-byte charge owned by Budget.
    pub closed spec fn encoded_bytes_spec(&self) -> nat { self.bytes.allocated as nat }
    /// Exact admission derived from the unchanged canonical owners.
    pub closed spec fn publish_admitted_spec(&self, encoded_bytes: u64) -> bool {
        !self.closed.marked && self.slots.used() + 1 <= self.slots.capacity as int
            && self.bytes.used() + encoded_bytes as int <= self.bytes.capacity as int
            && self.published.value_spec() < u64::MAX as nat
            && self.published.value_spec() < usize::MAX as nat
    }
    /// Export admission in terms of public retained-content and identity views.
    pub proof fn expose_admission(&self, encoded_bytes: u64)
        requires self.inv(),
        ensures self.publish_admitted_spec(encoded_bytes) == (!self.closed_spec()
            && self.entries_spec().len() < self.slot_limit_spec()
            && self.encoded_bytes_spec() + encoded_bytes as nat <= self.byte_limit_spec()
            && self.published_spec() < u64::MAX as nat
            && self.published_spec() < usize::MAX as nat),
    {}
    /// Coupling of actual FIFO, payload, identity, and charge owners.
    pub closed spec fn inv(&self) -> bool {
        &&& self.queue.well_formed()
        &&& self.payloads.unique_identities()
        &&& self.slots.safety_invariant()
        &&& self.bytes.safety_invariant()
        &&& self.slots.reserved == 0 && self.slots.pending_eviction == 0
        &&& self.bytes.reserved == 0 && self.bytes.pending_eviction == 0
        &&& self.slots.capacity as nat == self.queue.capacity as nat
        &&& self.slots.allocated as nat == self.queue.values@.len()
        &&& self.bytes.allocated as int == stream_bytes_to(self.payloads.entries@,
            self.payloads.entries@.len() as int)
        &&& self.payloads.entries@.len() == self.queue.values@.len()
        &&& self.consumed.position as nat + self.queue.values@.len() == self.published.value_spec()
        &&& self.published.value_spec() <= usize::MAX as nat
        &&& forall|index: int| 0 <= index < self.queue.values@.len() ==>
            #[trigger] self.queue.values@[index] as int == self.consumed.position as int + index
                && self.payloads.entries@[index].0 == self.queue.values@[index]
    }
    /// Exact logical stutter, including all retained original payloads.
    pub closed spec fn same_state(&self, other: Self) -> bool {
        self.scope == other.scope && self.payloads.entries@ == other.payloads.entries@
            && self.queue.values@ == other.queue.values@ && self.queue.capacity == other.queue.capacity
            && self.slots == other.slots && self.bytes == other.bytes
            && self.published == other.published && self.consumed.position == other.consumed.position
            && self.closed == other.closed
    }

    /// Reserve FIFO and Registry storage once, before accepting any payload.
    /// Zero capacities are valid; positive encoded bytes then refuse as applicable.
    /// Each instance requires a distinct caller-owned scope.
    ///
    /// # Errors
    /// Returns StorageUnavailable when either physical reservation fails.
    pub fn try_new(scope: u64, slots: usize, encoded_bytes: u64)
        -> (result: Result<Self, TypedStreamError>)
        ensures result matches Ok(stream) ==> stream.inv() && stream.scope_spec() == scope
            && stream.entries_spec().len() == 0 && stream.published_spec() == 0
            && stream.consumed_spec() == 0 && !stream.closed_spec()
            && stream.encoded_bytes_spec() == 0
            && stream.slot_limit_spec() == slots as nat && stream.byte_limit_spec() == encoded_bytes as nat,
    {
        let queue = match Buffer::try_new(slots) {
            Ok(queue) => queue,
            Err(_) => return Err(TypedStreamError::StorageUnavailable),
        };
        let mut payloads = ResourceRegistry::new();
        if payloads.try_reserve_entries(slots).is_err() {
            return Err(TypedStreamError::StorageUnavailable);
        }
        Ok(Self { scope, payloads, queue, slots: Budget::new(slots as u64),
            bytes: Budget::new(encoded_bytes), published: Counter::new(0),
            consumed: Cursor::new(0), closed: Marker::new(false) })
    }

    /// Current occupancy, read from the Buffer owner.
    pub fn len(&self) -> (length: usize) requires self.inv(),
        ensures length as nat == self.entries_spec().len(),
    { self.queue.len() }
    /// Whether the actual FIFO has no retained payload.
    pub fn is_empty(&self) -> (empty: bool) requires self.inv(),
        ensures empty == (self.entries_spec().len() == 0),
    { self.queue.is_empty() }
    /// Encoded-byte charge owned by Budget, without a caller-derived total.
    pub fn retained_bytes(&self) -> (bytes: u64) requires self.inv(),
        ensures bytes as nat == self.encoded_bytes_spec(),
            bytes as int == stream_bytes_to(self.entries_spec(), self.entries_spec().len() as int),
    { self.bytes.allocated }
    /// Exact receipt count read from the retained Cursor owner.
    pub fn received_count(&self) -> (count: usize) requires self.inv(),
        ensures count as nat == self.consumed_spec(),
    { self.consumed.position }
    /// Whether producer closure and actual FIFO drainage both hold.
    pub fn is_drained(&self) -> (drained: bool) requires self.inv(),
        ensures drained == (self.closed_spec() && self.entries_spec().len() == 0),
    { self.closed.is_marked() && self.queue.is_empty() }

    /// Publish one original payload after all owner guards have admitted it.
    /// No fallible storage operation occurs between the coupled owner commits.
    ///
    /// # Errors
    /// Returns the original input on closure, slot/byte pressure, or exhausted identity.
    pub fn publish(&mut self, value: T, encoded_bytes: u64)
        -> (result: Result<u64, TypedPublishRefusal<T>>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).scope_spec() == old(self).scope_spec(),
            final(self).slot_limit_spec() == old(self).slot_limit_spec(),
            final(self).byte_limit_spec() == old(self).byte_limit_spec(),
            (result is Ok) == old(self).publish_admitted_spec(encoded_bytes),
            result matches Err(refusal) ==> refusal.value == value && final(self).same_state(*old(self)),
            result is Err ==> final(self).entries_spec() == old(self).entries_spec()
                && final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec()
                && final(self).published_spec() == old(self).published_spec()
                && final(self).consumed_spec() == old(self).consumed_spec()
                && final(self).closed_spec() == old(self).closed_spec(),
            result matches Ok(sequence) ==> sequence as nat == old(self).published_spec()
                && final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec() + encoded_bytes as nat
                && final(self).entries_spec() == old(self).entries_spec().push((sequence,(value,encoded_bytes)))
                && final(self).published_spec() == old(self).published_spec() + 1
                && final(self).consumed_spec() == old(self).consumed_spec()
                && final(self).closed_spec() == old(self).closed_spec(),
    {
        if self.closed.is_marked() {
            return Err(TypedPublishRefusal { error: TypedStreamError::Closed, value });
        }
        if !self.slots.admits_additional(1, 0) {
            return Err(TypedPublishRefusal { error: TypedStreamError::SlotCapacity, value });
        }
        if !self.bytes.admits_additional(encoded_bytes, 0) {
            return Err(TypedPublishRefusal { error: TypedStreamError::ByteCapacity, value });
        }
        if !self.published.can_increment() || self.published.value() >= usize::MAX as u64 {
            return Err(TypedPublishRefusal { error: TypedStreamError::SequenceExhausted, value });
        }
        let sequence = self.published.value();
        let ghost before = *self;
        proof {
            crate::primitives::resource_registry::identity_entries_are_exact(self.payloads.entries@);
            assert(!self.payloads.contains_key(sequence)) by {
                if self.payloads.contains_key(sequence) {
                    let index = choose|index: int| 0 <= index < self.payloads.entries@.len()
                        && #[trigger] self.payloads.entries@[index].0 == sequence;
                    assert(self.queue.values@[index] as int == self.consumed.position as int + index);
                    assert(false);
                }
            }
        }
        let _slots = self.slots.try_allocate(1);
        let _bytes = self.bytes.try_allocate(encoded_bytes);
        self.payloads.register(sequence, (value, encoded_bytes));
        let _queued = self.queue.push(sequence);
        let _published = self.published.try_increment();
        assert(_slots && _bytes && _queued is Ok && _published);
        proof {
            stream_bytes_append_prefix(before.payloads.entries@, (sequence,(value,encoded_bytes)),
                before.payloads.entries@.len() as int);
            assert(self.bytes.allocated as int == stream_bytes_to(self.payloads.entries@,
                self.payloads.entries@.len() as int));
        }
        assert forall|index: int| 0 <= index < self.queue.values@.len() implies
            #[trigger] self.queue.values@[index] as int == self.consumed.position as int + index
                && self.payloads.entries@[index].0 == self.queue.values@[index] by {
            if index < before.queue.values@.len() {
                assert(self.queue.values@[index] == before.queue.values@[index]);
            }
        }
        assert(self.inv());
        Ok(sequence)
    }

    /// Transfer the oldest original payload to the caller and release its charges.
    /// The caller must account for any retention after this ownership transfer.
    ///
    /// # Errors
    /// Returns Empty while open, or Closed after the closed FIFO has drained.
    #[expect(clippy::cast_possible_truncation, reason = "the FIFO invariant bounds issued identities by usize::MAX")]
    #[expect(clippy::arithmetic_side_effects, reason = "a nonempty FIFO places its head strictly below the representable published head")]
    pub fn receive(&mut self) -> (result: Result<ReceivedStreamValue<T>, TypedStreamError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).scope_spec() == old(self).scope_spec(),
            final(self).slot_limit_spec() == old(self).slot_limit_spec(),
            final(self).byte_limit_spec() == old(self).byte_limit_spec(),
            final(self).published_spec() == old(self).published_spec(),
            final(self).closed_spec() == old(self).closed_spec(),
            (result is Ok) == (old(self).entries_spec().len() > 0),
            (result == Err(TypedStreamError::Empty)) == (old(self).entries_spec().len() == 0 && !old(self).closed_spec()),
            (result == Err(TypedStreamError::Closed)) == (old(self).entries_spec().len() == 0 && old(self).closed_spec()),
            result is Err ==> final(self).same_state(*old(self)),
            result is Err ==> final(self).entries_spec() == old(self).entries_spec()
                && final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec()
                && final(self).consumed_spec() == old(self).consumed_spec(),
            result matches Ok(received) ==> old(self).entries_spec().len() > 0
                && received.scope == old(self).scope_spec()
                && received.sequence == old(self).entries_spec()[0].0
                && received.value == old(self).entries_spec()[0].1.0
                && received.encoded_bytes == old(self).entries_spec()[0].1.1
                && final(self).encoded_bytes_spec() + received.encoded_bytes as nat == old(self).encoded_bytes_spec()
                && final(self).entries_spec() == old(self).entries_spec().skip(1)
                && final(self).consumed_spec() == old(self).consumed_spec() + 1,
    {
        if self.queue.is_empty() {
            return Err(if self.closed.is_marked() { TypedStreamError::Closed } else { TypedStreamError::Empty });
        }
        let ghost before = *self;
        let sequence = match self.queue.pop() { Some(sequence) => sequence, None => { assert(false); return Err(TypedStreamError::Empty); } };
        proof {
            assert(self.payloads.entries@[0].0 == sequence);
        }
        let entry = match self.payloads.deregister_identity_at(0) { Some(entry) => entry, None => { assert(false); return Err(TypedStreamError::Empty); } };
        proof {
            assert(self.payloads.entries@ =~= before.payloads.entries@.skip(1));
            stream_bytes_drop_first(before.payloads.entries@, before.payloads.entries@.len() as int);
            stream_bytes_nonnegative(self.payloads.entries@, self.payloads.entries@.len() as int);
            assert(entry.1.1 <= self.bytes.allocated);
        }
        self.slots.release(1);
        self.bytes.release(entry.1.1);
        self.consumed.advance_to(sequence as usize + 1);
        assert forall|index: int| 0 <= index < self.queue.values@.len() implies
            #[trigger] self.queue.values@[index] as int == self.consumed.position as int + index
                && self.payloads.entries@[index].0 == self.queue.values@[index] by {
            assert(self.queue.values@[index] == before.queue.values@[index + 1]);
        }
        Ok(ReceivedStreamValue { scope: self.scope, sequence, value: entry.1.0, encoded_bytes: entry.1.1 })
    }

    /// Close the producer once while retaining every drainable original payload.
    pub fn close_input(&mut self) -> (changed: bool)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).closed_spec(), changed == !old(self).closed_spec(),
            final(self).entries_spec() == old(self).entries_spec(),
            final(self).encoded_bytes_spec() == old(self).encoded_bytes_spec(),
            final(self).published_spec() == old(self).published_spec(),
            final(self).consumed_spec() == old(self).consumed_spec(),
            final(self).scope_spec() == old(self).scope_spec(),
            final(self).slot_limit_spec() == old(self).slot_limit_spec(),
            final(self).byte_limit_spec() == old(self).byte_limit_spec(),
    { self.closed.set() }
}

/// Erased logical view shared by every bounded-transfer realization.
pub ghost struct BoundedTransferModel<T> {
    /// Maximum retained record count.
    pub slot_capacity: nat,
    /// Maximum retained encoded byte count.
    pub retained_byte_capacity: nat,
    /// Retained records in FIFO order.
    pub values: Seq<T>,
    /// Encoded key-size registry for retained records.
    pub registry: Seq<(u64, u64)>,
    /// Total encoded bytes retained.
    pub retained_bytes: nat,
    /// Monotone consumed-record cursor.
    pub head: nat,
    /// Monotone admitted-record cursor.
    pub tail: nat,
    /// Whether the transfer owner is closed to new records.
    pub closed: bool,
}

impl<T> BoundedTransferModel<T> {
    /// Primitive-rooted and connective-rooted state invariant.
    pub open spec fn inv(self) -> bool {
        &&& self.slot_capacity > 0
        &&& self.retained_byte_capacity > 0
        &&& crate::primitives::budget::budget_safety(
            self.slot_capacity,
            self.values.len(),
            0,
            0,
        )
        &&& crate::primitives::budget::budget_safety(
            self.retained_byte_capacity,
            self.retained_bytes,
            0,
            0,
        )
        &&& crate::connectives::buffer::buffer_bounded(
            self.values,
            self.slot_capacity,
        )
        &&& self.registry.len() == self.values.len()
        &&& crate::primitives::resource_registry::unique_mapping_entries(
            self.registry,
        )
        &&& crate::connectives::cursor::cursor_admitted(self.head, self.tail)
        &&& crate::connectives::ordering_pass::fifo_sequence_order(
            self.registry,
            self.head,
            self.tail,
        )
    }

    /// Readiness is derived from Buffer occupancy. It is not parallel state.
    pub open spec fn ready(self) -> bool {
        self.values.len() > 0
    }

    /// The closed transfer is terminal only after its Buffer drains.
    pub open spec fn terminal(self) -> bool {
        self.closed && self.values.len() == 0
    }
}

/// One successful publication through the shared bounded-transfer composition.
pub open spec fn bounded_transfer_publish<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
    value: T,
    retained_bytes: u64,
    sequence: u64,
) -> bool {
    &&& pre.inv()
    &&& post.inv()
    &&& !pre.closed
    &&& pre.values.len() < pre.slot_capacity
    &&& pre.retained_bytes + retained_bytes as nat <= pre.retained_byte_capacity
    &&& pre.tail < u64::MAX as nat
    &&& sequence as nat == pre.tail
    &&& post.slot_capacity == pre.slot_capacity
    &&& post.retained_byte_capacity == pre.retained_byte_capacity
    &&& post.values == pre.values.push(value)
    &&& post.registry == pre.registry.push((sequence, retained_bytes))
    &&& post.retained_bytes == pre.retained_bytes + retained_bytes as nat
    &&& post.head == pre.head
    &&& post.tail == pre.tail + 1
    &&& post.closed == pre.closed
}

/// One successful FIFO receipt through the shared bounded-transfer composition.
pub open spec fn bounded_transfer_receive<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
    value: T,
    retained_bytes: u64,
    sequence: u64,
) -> bool {
    &&& pre.inv()
    &&& post.inv()
    &&& pre.values.len() > 0
    &&& value == pre.values[0]
    &&& (sequence, retained_bytes) == pre.registry[0]
    &&& post.slot_capacity == pre.slot_capacity
    &&& post.retained_byte_capacity == pre.retained_byte_capacity
    &&& post.values == pre.values.skip(1)
    &&& post.registry == pre.registry.skip(1)
    &&& post.retained_bytes + retained_bytes as nat == pre.retained_bytes
    &&& post.head == pre.head + 1
    &&& post.tail == pre.tail
    &&& post.closed == pre.closed
}

/// Idempotent producer closure through the shared bounded-transfer composition.
pub open spec fn bounded_transfer_close<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
    changed: bool,
) -> bool {
    &&& pre.inv()
    &&& post.inv()
    &&& changed == !pre.closed
    &&& post.slot_capacity == pre.slot_capacity
    &&& post.retained_byte_capacity == pre.retained_byte_capacity
    &&& post.values == pre.values
    &&& post.registry == pre.registry
    &&& post.retained_bytes == pre.retained_bytes
    &&& post.head == pre.head
    &&& post.tail == pre.tail
    &&& post.closed
}

/// Every refused action stutters at the complete logical boundary.
pub open spec fn bounded_transfer_refusal_stutters<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
) -> bool {
    pre == post
}

/// Empty admitted origin for every reachable bounded-transfer execution.
///
/// Starting both ledgers and the registry at zero, then using only `publish` and `receive`, binds
/// retained-byte Budget changes to the exact ResourceRegistry charge appended or removed.
pub open spec fn bounded_transfer_initial<T>(model: BoundedTransferModel<T>) -> bool {
    &&& model.inv()
    &&& model.values == Seq::<T>::empty()
    &&& model.registry == Seq::<(u64, u64)>::empty()
    &&& model.retained_bytes == 0
    &&& model.head == 0
    &&& model.tail == 0
    &&& !model.closed
}

/// Publish one value through one StreamGraph connection.
pub open spec fn connection_publish<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
    value: T,
    retained_bytes: u64,
    sequence: u64,
) -> bool {
    bounded_transfer_publish(pre, post, value, retained_bytes, sequence)
}

/// Receive one value through one StreamGraph connection.
pub open spec fn connection_receive<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
    value: T,
    retained_bytes: u64,
    sequence: u64,
) -> bool {
    bounded_transfer_receive(pre, post, value, retained_bytes, sequence)
}

/// Close one StreamGraph connection without disturbing queued values.
pub open spec fn connection_close<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
    changed: bool,
) -> bool {
    bounded_transfer_close(pre, post, changed)
}

/// A refused StreamGraph endpoint action leaves the complete connection unchanged.
pub open spec fn connection_refusal<T>(
    pre: BoundedTransferModel<T>,
    post: BoundedTransferModel<T>,
) -> bool {
    bounded_transfer_refusal_stutters(pre, post)
}

/// Publish one value to each of two connections as one StreamGraph action.
pub open spec fn publish_pair<T>(
    left_pre: BoundedTransferModel<T>,
    left_post: BoundedTransferModel<T>,
    left_value: T,
    left_sequence: u64,
    right_pre: BoundedTransferModel<T>,
    right_post: BoundedTransferModel<T>,
    right_value: T,
    right_sequence: u64,
    retained_bytes: u64,
) -> bool {
    &&& connection_publish(
        left_pre,
        left_post,
        left_value,
        retained_bytes,
        left_sequence,
    )
    &&& connection_publish(
        right_pre,
        right_post,
        right_value,
        retained_bytes,
        right_sequence,
    )
}

/// Receive one oldest value from each of two connections as one StreamGraph action.
pub open spec fn receive_pair<T>(
    left_pre: BoundedTransferModel<T>,
    left_post: BoundedTransferModel<T>,
    left_value: T,
    left_retained_bytes: u64,
    left_sequence: u64,
    right_pre: BoundedTransferModel<T>,
    right_post: BoundedTransferModel<T>,
    right_value: T,
    right_retained_bytes: u64,
    right_sequence: u64,
) -> bool {
    &&& connection_receive(
        left_pre,
        left_post,
        left_value,
        left_retained_bytes,
        left_sequence,
    )
    &&& connection_receive(
        right_pre,
        right_post,
        right_value,
        right_retained_bytes,
        right_sequence,
    )
}

/// Close two connections together with one shared change result.
pub open spec fn close_pair<T>(
    left_pre: BoundedTransferModel<T>,
    left_post: BoundedTransferModel<T>,
    right_pre: BoundedTransferModel<T>,
    right_post: BoundedTransferModel<T>,
    changed: bool,
) -> bool {
    &&& connection_close(left_pre, left_post, changed)
    &&& connection_close(right_pre, right_post, changed)
}

/// A refused two-connection action leaves both connections unchanged.
pub open spec fn pair_refusal<T>(
    left_pre: BoundedTransferModel<T>,
    left_post: BoundedTransferModel<T>,
    right_pre: BoundedTransferModel<T>,
    right_post: BoundedTransferModel<T>,
) -> bool {
    &&& connection_refusal(left_pre, left_post)
    &&& connection_refusal(right_pre, right_post)
}

/// Move the oldest value between adjacent connections as one StreamGraph relay action.
pub open spec fn relay<T>(
    source_pre: BoundedTransferModel<T>,
    source_post: BoundedTransferModel<T>,
    destination_pre: BoundedTransferModel<T>,
    destination_post: BoundedTransferModel<T>,
    destination_sequence: u64,
) -> bool {
    let value = source_pre.values[0];
    let source_sequence = source_pre.registry[0].0;
    let retained_bytes = source_pre.registry[0].1;
    &&& connection_receive(
        source_pre,
        source_post,
        value,
        retained_bytes,
        source_sequence,
    )
    &&& connection_publish(
        destination_pre,
        destination_post,
        value,
        retained_bytes,
        destination_sequence,
    )
}

/// A refused relay leaves both adjacent connections unchanged.
pub open spec fn relay_refusal<T>(
    source_pre: BoundedTransferModel<T>,
    source_post: BoundedTransferModel<T>,
    destination_pre: BoundedTransferModel<T>,
    destination_post: BoundedTransferModel<T>,
) -> bool {
    &&& connection_refusal(source_pre, source_post)
    &&& connection_refusal(destination_pre, destination_post)
}

/// Empty admitted origin for one StreamGraph connection.
pub open spec fn connection_initial<T>(
    model: BoundedTransferModel<T>,
) -> bool {
    bounded_transfer_initial(model)
}

/// Empty admitted origin for two StreamGraph connections.
pub open spec fn pair_initial<T>(
    left: BoundedTransferModel<T>,
    right: BoundedTransferModel<T>,
) -> bool {
    &&& connection_initial(left)
    &&& connection_initial(right)
}

/// Bounded linear stream owner.
pub struct StreamGraph {
    /// Number of stages in the linear chain.
    pub chain_length: usize,
    /// Maximum records admitted at the source.
    pub max_inputs: usize,
    /// Exclusive upper bound of record values.
    pub record_domain_size: u64,
    /// First FIFO edge owner.
    pub q1: Buffer<u64>,
    /// Second FIFO edge owner.
    pub q2: Buffer<u64>,
    /// Optional third FIFO edge owner.
    pub q3: Buffer<u64>,
    /// Source-admission counter.
    pub ingested: Counter,
    /// Sink-emission counter.
    pub emitted: Counter,
}

impl StreamGraph {
    /// Whether chain length, edge capacity, and record domain form a supported configuration.
    pub open spec fn valid_config_spec(
        chain_length: usize,
        capacity: usize,
        record_domain_size: u64,
    ) -> bool {
        (chain_length == 3 || chain_length == 4)
            && capacity > 0
            && record_domain_size > 0
    }

    /// Whether every queued value lies within `domain`.
    pub open spec fn values_valid(q: Seq<u64>, domain: u64) -> bool {
        forall|i: int| 0 <= i < q.len() ==> #[trigger] q[i] < domain
    }

    /// Total number of records currently retained across all stream edges.
    pub open spec fn queue_depth(&self) -> nat {
        if self.chain_length == 3 {
            self.q1.values@.len() + self.q2.values@.len()
        } else {
            self.q1.values@.len() + self.q2.values@.len() + self.q3.values@.len()
        }
    }

    /// Whether counters, queues, and configuration values have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& Self::valid_config_spec(
            self.chain_length, self.q1.capacity, self.record_domain_size)
        &&& self.q2.capacity == self.q1.capacity
        &&& self.q3.capacity == self.q1.capacity
        &&& Self::values_valid(self.q1.values@, self.record_domain_size)
        &&& Self::values_valid(self.q2.values@, self.record_domain_size)
        &&& Self::values_valid(self.q3.values@, self.record_domain_size)
        &&& (self.chain_length == 3 ==> self.q3.values@.len() == 0)
        &&& self.ingested.value_spec() <= self.max_inputs as nat
        &&& self.emitted.value_spec() <= self.max_inputs as nat
    }

    /// Whether a full downstream edge prevents the corresponding transfer.
    pub open spec fn backpressure_correct(&self) -> bool {
        &&& self.q1.well_formed()
        &&& self.q2.well_formed()
        &&& self.q3.well_formed()
    }

    /// Whether admitted-record count equals emitted plus retained-record counts.
    pub open spec fn count_conservation(&self) -> bool {
        self.ingested.value_spec() == self.queue_depth() + self.emitted.value_spec()
    }

    /// Compatibility alias for [`Self::count_conservation`].
    ///
    /// Count equality alone does not establish record identity or provenance.
    pub open spec fn no_record_loss(&self) -> bool {
        self.count_conservation()
    }

    /// Whether at least one modeled action is enabled in this state.
    ///
    /// This is a state predicate. It does not require a scheduler to choose an enabled action and
    /// therefore does not establish temporal progress or fairness.
    pub open spec fn some_action_enabled(&self) -> bool {
        ||| (self.ingested.value_spec() < self.max_inputs as nat
            && self.q1.values@.len() < self.q1.capacity)
        ||| (self.q1.values@.len() > 0
            && self.q2.values@.len() < self.q2.capacity)
        ||| (self.chain_length == 3 && self.q2.values@.len() > 0)
        ||| (self.chain_length == 4
            && self.q2.values@.len() > 0
            && self.q3.values@.len() < self.q3.capacity)
        ||| (self.chain_length == 4 && self.q3.values@.len() > 0)
        ||| (self.ingested.value_spec() == self.max_inputs as nat
            && self.q1.values@.len() == 0
            && self.q2.values@.len() == 0
            && self.q3.values@.len() == 0)
    }

    /// Whether all linear-stream contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.backpressure_correct() && self.count_conservation()
    }

    /// Establish state-level enabledness from the retained carrier invariant.
    pub proof fn lemma_some_action_enabled(&self)
        requires self.inv(),
        ensures self.some_action_enabled(),
    {
        reveal(StreamGraph::inv);
        reveal(StreamGraph::type_invariant);
        reveal(StreamGraph::backpressure_correct);
        reveal(StreamGraph::some_action_enabled);

        if self.ingested.value_spec() < self.max_inputs as nat {
            if self.q1.values@.len() < self.q1.capacity {
            } else if self.q2.values@.len() < self.q2.capacity {
            } else if self.chain_length == 3 {
            } else if self.q3.values@.len() < self.q3.capacity {
            } else {
            }
        } else if self.q1.values@.len() > 0 {
            if self.q2.values@.len() < self.q2.capacity {
            } else if self.chain_length == 3 {
            } else if self.q3.values@.len() < self.q3.capacity {
            } else {
            }
        } else if self.q2.values@.len() > 0 {
            if self.chain_length == 3 {
            } else if self.q3.values@.len() < self.q3.capacity {
            } else {
            }
        } else if self.chain_length == 4 && self.q3.values@.len() > 0 {
        } else {
        }
    }

    /// Evaluate the state-level enabledness predicate.
    pub fn some_action_enabled_exec(&self) -> (enabled: bool)
        requires self.inv(),
        ensures enabled == self.some_action_enabled(),
    {
        proof { self.lemma_some_action_enabled(); }
        (self.ingested.value() < self.max_inputs as u64 && self.q1.len() < self.q1.capacity)
            || (!self.q1.is_empty() && self.q2.len() < self.q2.capacity)
            || (self.chain_length == 3 && !self.q2.is_empty())
            || (self.chain_length == 4
                && !self.q2.is_empty()
                && self.q3.len() < self.q3.capacity)
            || (self.chain_length == 4 && !self.q3.is_empty())
            || (self.ingested.value() == self.max_inputs as u64
                && self.q1.is_empty()
                && self.q2.is_empty()
                && self.q3.is_empty())
    }

    /// Test whether a chain configuration is represented by this carrier.
    pub fn valid_config(
        chain_length: usize,
        capacity: usize,
        record_domain_size: u64,
    ) -> (valid: bool)
        ensures valid == Self::valid_config_spec(
            chain_length, capacity, record_domain_size),
    {
        (chain_length == 3 || chain_length == 4)
            && capacity > 0
            && record_domain_size > 0
    }

    /// Capacity shared by every Buffer edge owner.
    pub fn capacity(&self) -> (capacity: usize)
        ensures capacity == self.q1.capacity,
    {
        self.q1.capacity
    }

    /// Construct an empty valid stream graph.
    pub fn new(
        chain_length: usize,
        capacity: usize,
        max_inputs: usize,
        record_domain_size: u64,
    ) -> (s: StreamGraph)
        requires Self::valid_config_spec(chain_length, capacity, record_domain_size),
        ensures
            s.chain_length == chain_length,
            s.q1.capacity == capacity,
            s.q2.capacity == capacity,
            s.q3.capacity == capacity,
            s.max_inputs == max_inputs,
            s.record_domain_size == record_domain_size,
            s.q1.values@.len() == 0,
            s.q2.values@.len() == 0,
            s.q3.values@.len() == 0,
            s.ingested.value_spec() == 0,
            s.emitted.value_spec() == 0,
            s.inv(),
    {
        StreamGraph {
            chain_length,
            max_inputs,
            record_domain_size,
            q1: Buffer::new(capacity),
            q2: Buffer::new(capacity),
            q3: Buffer::new(capacity),
            ingested: Counter::new(0),
            emitted: Counter::new(0),
        }
    }

    /// Admit one in-domain record when source and backpressure bounds permit it.
    pub fn source_ingest(&mut self, value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (value < old(self).record_domain_size
                && old(self).ingested.value_spec() < old(self).max_inputs as nat
                && old(self).q1.values@.len() < old(self).q1.capacity),
            final(self).chain_length == old(self).chain_length,
            final(self).q1.capacity == old(self).q1.capacity,
            final(self).q2.capacity == old(self).q2.capacity,
            final(self).q3.capacity == old(self).q3.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1.values@ == if accepted {
                old(self).q1.values@.push(value)
            } else { old(self).q1.values@ },
            final(self).q2.values@ == old(self).q2.values@,
            final(self).q3.values@ == old(self).q3.values@,
            accepted ==> final(self).ingested.value_spec()
                == old(self).ingested.value_spec() + 1,
            !accepted ==> final(self).ingested.value_spec()
                == old(self).ingested.value_spec(),
            final(self).emitted.value_spec() == old(self).emitted.value_spec(),
            final(self).inv(),
    {
        if value < self.record_domain_size
            && self.ingested.value() < self.max_inputs as u64
            && self.q1.len() < self.q1.capacity
        {
            let _pushed = self.q1.push(value);
            let _counted = self.ingested.try_increment();
            assert(_counted);
            assert forall|i: int| 0 <= i < self.q1.values@.len()
                implies #[trigger] self.q1.values@[i] < self.record_domain_size by {
                if i < old(self).q1.values@.len() {
                    assert(self.q1.values@[i] == old(self).q1.values@[i]);
                }
            }
            true
        } else {
            false
        }
    }

    /// Transfer the oldest first-edge record to the second edge.
    #[expect(clippy::indexing_slicing, reason = "the first-queue nonempty guard proves its oldest retained value exists")]
    pub fn middle2_fire(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).q1.values@.len() > 0
                && old(self).q2.values@.len() < old(self).q2.capacity),
            final(self).chain_length == old(self).chain_length,
            final(self).q1.capacity == old(self).q1.capacity,
            final(self).q2.capacity == old(self).q2.capacity,
            final(self).q3.capacity == old(self).q3.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1.values@ == if accepted {
                old(self).q1.values@.subrange(1, old(self).q1.values@.len() as int)
            } else { old(self).q1.values@ },
            final(self).q2.values@ == if accepted {
                old(self).q2.values@.push(old(self).q1.values@[0])
            } else { old(self).q2.values@ },
            final(self).q3.values@ == old(self).q3.values@,
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            final(self).emitted.value_spec() == old(self).emitted.value_spec(),
            final(self).inv(),
    {
        if self.q1.len() > 0 && self.q2.len() < self.q2.capacity {
            let ghost old_q1 = self.q1.values@;
            let ghost old_q2 = self.q2.values@;
            let value = self.q1.values[0];
            let _popped = self.q1.pop();
            let _pushed = self.q2.push(value);
            assert(self.q1.values@ =~= old_q1.subrange(1, old_q1.len() as int));
            assert(self.q2.values@ =~= old_q2.push(old_q1[0]));
            assert forall|i: int| 0 <= i < self.q2.values@.len()
                implies #[trigger] self.q2.values@[i] < self.record_domain_size by {
                if i < old_q2.len() {
                    assert(self.q2.values@[i] == old_q2[i]);
                } else {
                    assert(self.q2.values@[i] == old_q1[0]);
                }
            }
            true
        } else {
            false
        }
    }

    /// Transfer the oldest second-edge record through the optional fourth stage.
    #[expect(clippy::indexing_slicing, reason = "the second-queue nonempty guard proves its oldest retained value exists")]
    pub fn middle3_fire(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).chain_length == 4
                && old(self).q2.values@.len() > 0
                && old(self).q3.values@.len() < old(self).q3.capacity),
            final(self).chain_length == old(self).chain_length,
            final(self).q1.capacity == old(self).q1.capacity,
            final(self).q2.capacity == old(self).q2.capacity,
            final(self).q3.capacity == old(self).q3.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1.values@ == old(self).q1.values@,
            final(self).q2.values@ == if accepted {
                old(self).q2.values@.subrange(1, old(self).q2.values@.len() as int)
            } else { old(self).q2.values@ },
            final(self).q3.values@ == if accepted {
                old(self).q3.values@.push(old(self).q2.values@[0])
            } else { old(self).q3.values@ },
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            final(self).emitted.value_spec() == old(self).emitted.value_spec(),
            final(self).inv(),
    {
        if self.chain_length == 4 && self.q2.len() > 0
            && self.q3.len() < self.q3.capacity
        {
            let ghost old_q2 = self.q2.values@;
            let ghost old_q3 = self.q3.values@;
            let value = self.q2.values[0];
            let _popped = self.q2.pop();
            let _pushed = self.q3.push(value);
            assert(self.q2.values@ =~= old_q2.subrange(1, old_q2.len() as int));
            assert(self.q3.values@ =~= old_q3.push(old_q2[0]));
            assert forall|i: int| 0 <= i < self.q3.values@.len()
                implies #[trigger] self.q3.values@[i] < self.record_domain_size by {
                if i < old_q3.len() {
                    assert(self.q3.values@[i] == old_q3[i]);
                } else {
                    assert(self.q3.values@[i] == old_q2[0]);
                }
            }
            true
        } else {
            false
        }
    }

    /// Consume the oldest record from the final edge.
    pub fn sink_consume(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == if old(self).chain_length == 3 {
                old(self).q2.values@.len() > 0
            } else {
                old(self).q3.values@.len() > 0
            },
            final(self).chain_length == old(self).chain_length,
            final(self).q1.capacity == old(self).q1.capacity,
            final(self).q2.capacity == old(self).q2.capacity,
            final(self).q3.capacity == old(self).q3.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1.values@ == old(self).q1.values@,
            final(self).q2.values@ == if accepted && old(self).chain_length == 3 {
                old(self).q2.values@.subrange(1, old(self).q2.values@.len() as int)
            } else { old(self).q2.values@ },
            final(self).q3.values@ == if accepted && old(self).chain_length == 4 {
                old(self).q3.values@.subrange(1, old(self).q3.values@.len() as int)
            } else { old(self).q3.values@ },
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            accepted ==> final(self).emitted.value_spec()
                == old(self).emitted.value_spec() + 1,
            !accepted ==> final(self).emitted.value_spec()
                == old(self).emitted.value_spec(),
            final(self).inv(),
    {
        if self.chain_length == 3 {
            if self.q2.len() > 0 {
                let ghost old_q2 = self.q2.values@;
                let _popped = self.q2.pop();
                let _counted = self.emitted.try_increment();
                assert(_counted);
                assert(self.q2.values@ =~= old_q2.subrange(1, old_q2.len() as int));
                true
            } else {
                false
            }
        } else {
            if self.q3.len() > 0 {
                let ghost old_q3 = self.q3.values@;
                let _popped = self.q3.pop();
                let _counted = self.emitted.try_increment();
                assert(_counted);
                assert(self.q3.values@ =~= old_q3.subrange(1, old_q3.len() as int));
                true
            } else {
                false
            }
        }
    }

    /// Execute the terminal stutter after bounded input is drained.
    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (old(self).ingested.value_spec() == old(self).max_inputs as nat
                && old(self).q1.values@.len() == 0
                && old(self).q2.values@.len() == 0
                && old(self).q3.values@.len() == 0),
            final(self).chain_length == old(self).chain_length,
            final(self).q1.capacity == old(self).q1.capacity,
            final(self).q2.capacity == old(self).q2.capacity,
            final(self).q3.capacity == old(self).q3.capacity,
            final(self).max_inputs == old(self).max_inputs,
            final(self).record_domain_size == old(self).record_domain_size,
            final(self).q1.values@ == old(self).q1.values@,
            final(self).q2.values@ == old(self).q2.values@,
            final(self).q3.values@ == old(self).q3.values@,
            final(self).ingested.value_spec() == old(self).ingested.value_spec(),
            final(self).emitted.value_spec() == old(self).emitted.value_spec(),
            final(self).inv(),
    {
        self.ingested.value() == self.max_inputs as u64
            && self.q1.len() == 0
            && self.q2.len() == 0
            && self.q3.len() == 0
    }
}

}
