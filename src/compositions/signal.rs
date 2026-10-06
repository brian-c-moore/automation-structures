// AuditSink-backed Signal named composition.
//
// This is the executable construction recorded by
// SignalFromAuditSink.tla:
//
//   current_value = last AuditSink operation, or initial_value
//   pending(l)    = cursor(l) < audit length
//   notified(l)   = audit length > 0 && cursor(l) == audit length
//
// AuditSink owns append capacity and chain state. CF-002 Cursor owns each
// retained listener position. Signal adds only change detection and the fused
// listener catch-up transition. It stores no parallel pending or notified set.

use crate::connectives::cursor::Cursor;
use crate::primitives::audit_sink::AuditSink;
#[expect(
    unused_imports,
    reason = "ChainOperation is used by ghost specifications erased by rustc"
)]
use crate::primitives::audit_sink::ChainOperation;
use vstd::prelude::*;

verus! {

/// Pure latest-value content for the existing typed AuditSink Record.
#[derive(Copy)]
pub struct LastSignalValue<T: Copy> {
    initial: T,
}
impl<T: Copy> Clone for LastSignalValue<T> {
    fn clone(&self) -> (value: Self) ensures value == *self,
    { *self }
}
impl<T: Copy> crate::primitives::audit_sink::TypedChainOperation for LastSignalValue<T> {
    type Item = T;
    type Carry = T;
    closed spec fn initial_spec(&self) -> T { self.initial }
    open spec fn accepts(&self, _previous: T, _operation: T) -> bool { true }
    open spec fn combined(&self, _previous: T, operation: T) -> T { operation }
    fn initial(&self) -> (value: T) { self.initial }
    fn accepts_exec(&self, _previous: T, _operation: T) -> (yes: bool) { true }
    fn combine_typed(&self, _previous: T, operation: T) -> (value: T) { operation }
}

/// Scoped registration identity issued by a Signal's canonical Counter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignalListener {
    scope: u64,
    generation: u64,
}
impl SignalListener {
    /// Caller-supplied root scope identity.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Counter-issued generation, never reused by this owner.
    pub closed spec fn generation_spec(&self) -> u64 { self.generation }
    /// Observe the issued generation without exposing token construction.
    pub fn generation(&self) -> (generation: u64)
        ensures generation == self.generation_spec(),
    { self.generation }
}

/// One latest-value observation and its exact change head.
#[derive(Copy, Debug, PartialEq, Eq)]
pub struct SignalObservation<T: Copy> {
    /// Value at the retained AuditSink head.
    pub value: T,
    /// Exact committed change count.
    pub head: usize,
    /// Whether this notification advanced the retained listener Cursor.
    pub changed: bool,
}
impl<T: Copy> Clone for SignalObservation<T> {
    fn clone(&self) -> (value: Self) ensures value == *self,
    { *self }
}

/// Checked summary-Signal admission or listener refusal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SignalProfileError {
    /// The live-listener Budget refused one more registration.
    ListenerCapacity,
    /// The generation Counter cannot advance without representation overflow.
    GenerationExhausted,
    /// Registry storage could not be reserved before registration.
    StorageUnavailable,
    /// The token belongs to a different caller-owned scope.
    ForeignScope,
    /// The generation is absent or was removed.
    UnknownListener,
    /// The AuditSink lifetime change ceiling is exhausted.
    ChangeCapacity,
}

/// Typed coalescing Signal with actual summary storage and dynamic listeners.
/// Each instance requires a distinct caller-owned scope. Values are pure Copy
/// domain content; physical waiting and concurrent access belong to the binding.
pub struct SummarySignal<T: Copy + crate::value_eq::ValueEq> {
    scope: u64,
    audit: AuditSink<LastSignalValue<T>, crate::primitives::audit_sink::SummaryHistory<T, T>>,
    listeners: crate::primitives::resource_registry::ResourceRegistry<u64, Cursor>,
    listener_budget: crate::primitives::budget::Budget,
    issued: crate::connectives::counter::Counter,
}

impl<T: Copy + crate::value_eq::ValueEq> SummarySignal<T> {
    /// Immutable root scope supplied by the caller.
    pub closed spec fn scope_spec(&self) -> u64 { self.scope }
    /// Current value owned by the retained AuditSink carry.
    pub closed spec fn value_spec(&self) -> T { self.audit.last_hash }
    /// Exact proof-only change history for the summary retention profile.
    pub closed spec fn history_spec(&self) -> Seq<crate::primitives::audit_sink::AuditEntry<T,T>> {
        self.audit.history_spec()
    }
    /// Actual listener Registry entries, including their retained Cursors.
    pub closed spec fn listeners_spec(&self) -> Seq<(u64, Cursor)> { self.listeners.entries@ }
    /// Greatest generation issued by this Signal.
    pub closed spec fn issued_spec(&self) -> nat { self.issued.value_spec() }
    /// AuditSink-owned lifetime change ceiling.
    pub closed spec fn change_limit_spec(&self) -> nat { self.audit.max_log_len as nat }
    /// Exact retained registration under this owner's declared root scope.
    pub closed spec fn registered_spec(&self, token: SignalListener) -> bool {
        token.scope == self.scope && self.listeners.contains_key_identity(token.generation)
    }
    /// Exact pending relation from the same listener Registry and AuditSink head.
    pub closed spec fn pending_spec(&self, token: SignalListener) -> bool {
        token.scope == self.scope && exists|i: int| 0 <= i < self.listeners.entries@.len()
            && #[trigger] self.listeners.entries@[i].0 == token.generation
            && self.listeners.entries@[i].1.position < self.history_spec().len()
    }
    /// Exact catch-up relation, including an empty initial change head.
    pub closed spec fn caught_up_spec(&self, token: SignalListener) -> bool {
        token.scope == self.scope && exists|i: int| 0 <= i < self.listeners.entries@.len()
            && #[trigger] self.listeners.entries@[i].0 == token.generation
            && self.listeners.entries@[i].1.position == self.history_spec().len()
    }
    /// Exact scope, charge, generation and catch-up relation.
    pub closed spec fn inv(&self) -> bool {
        &&& self.audit.chain_valid()
        &&& self.listeners.unique_identities()
        &&& self.listener_budget.safety_invariant()
        &&& self.listener_budget.reserved == 0 && self.listener_budget.pending_eviction == 0
        &&& self.listener_budget.allocated as int == self.listeners.entries@.len()
        &&& forall|i: int| 0 <= i < self.listeners.entries@.len() ==> {
            let entry = #[trigger] self.listeners.entries@[i];
            &&& 0 < entry.0 <= self.issued.value_spec()
            &&& entry.1.position <= self.history_spec().len()
        }
    }
    /// Logical refusal/cancellation frame; physical Registry spare capacity may grow.
    pub closed spec fn same_state(&self, before: Self) -> bool {
        self.scope == before.scope && self.audit == before.audit
            && self.listeners_spec() == before.listeners_spec()
            && self.listener_budget == before.listener_budget && self.issued == before.issued
    }

    /// Export the logical frame across a refused action without exposing fields.
    pub proof fn expose_state_frame(&self, before: &Self)
        requires self.same_state(*before),
        ensures self.scope_spec() == before.scope_spec(), self.value_spec() == before.value_spec(),
            self.history_spec() == before.history_spec(), self.listeners_spec() == before.listeners_spec(),
            self.issued_spec() == before.issued_spec(),
    {}

    /// Export listener state as a projection of the actual retained entries/head.
    pub proof fn expose_listener_state(&self, token: SignalListener)
        requires self.inv(),
        ensures self.registered_spec(token) == (token.scope_spec() == self.scope_spec()
                && exists|i: int| 0 <= i < self.listeners_spec().len()
                    && #[trigger] self.listeners_spec()[i].0 == token.generation_spec()),
            self.pending_spec(token) == (token.scope_spec() == self.scope_spec()
                && exists|i: int| 0 <= i < self.listeners_spec().len()
                    && #[trigger] self.listeners_spec()[i].0 == token.generation_spec()
                    && self.listeners_spec()[i].1.position < self.history_spec().len()),
            self.caught_up_spec(token) == (token.scope_spec() == self.scope_spec()
                && exists|i: int| 0 <= i < self.listeners_spec().len()
                    && #[trigger] self.listeners_spec()[i].0 == token.generation_spec()
                    && self.listeners_spec()[i].1.position == self.history_spec().len()),
            self.caught_up_spec(token) ==> self.registered_spec(token) && !self.pending_spec(token),
            self.pending_spec(token) ==> self.registered_spec(token) && !self.caught_up_spec(token),
    {
        crate::primitives::resource_registry::identity_entries_are_exact(self.listeners.entries@);
        reveal(SignalListener::scope_spec);
        reveal(SignalListener::generation_spec);
        let entries = self.listeners_spec();
        if token.scope == self.scope {
            if self.registered_spec(token) {
                let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == token.generation;
                assert(0 <= i < self.listeners_spec().len() && self.listeners_spec()[i].0 == token.generation_spec());
            }
            if exists|i: int| 0 <= i < entries.len() && #[trigger] entries[i].0 == token.generation_spec() {
                let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == token.generation_spec();
                assert(self.listeners.contains_key_identity(token.generation));
            }
            if self.pending_spec(token) {
                let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == token.generation
                    && entries[i].1.position < self.history_spec().len();
                crate::primitives::resource_registry::identity_entry_at(entries, i);
                self.expose_listener(token.generation, entries[i].1);
                assert(!self.caught_up_spec(token));
                assert(0 <= i < self.listeners_spec().len() && self.listeners_spec()[i].0 == token.generation_spec()
                    && self.listeners_spec()[i].1.position < self.history_spec().len());
            }
            if exists|i: int| 0 <= i < entries.len() && #[trigger] entries[i].0 == token.generation_spec()
                && entries[i].1.position < self.history_spec().len() {
                let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == token.generation_spec()
                    && entries[i].1.position < self.history_spec().len();
                assert(self.pending_spec(token));
            }
            if self.caught_up_spec(token) {
                let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == token.generation
                    && entries[i].1.position == self.history_spec().len();
                crate::primitives::resource_registry::identity_entry_at(entries, i);
                self.expose_listener(token.generation, entries[i].1);
                assert(!self.pending_spec(token));
            }
        }
    }

    proof fn expose_listener(&self, generation: u64, cursor: Cursor)
        requires self.inv(), self.listeners.maps_key(generation, cursor),
        ensures 0 < generation <= self.issued_spec(), cursor.position <= self.history_spec().len(),
            self.listeners.contains_key_identity(generation),
            exists|i: int| 0 <= i < self.listeners.entries@.len()
                && #[trigger] self.listeners.entries@[i] == (generation, cursor),
            forall|i: int| 0 <= i < self.listeners.entries@.len()
                && #[trigger] self.listeners.entries@[i].0 == generation ==> self.listeners.entries@[i].1 == cursor,
    {
        crate::primitives::resource_registry::identity_entries_are_exact(self.listeners.entries@);
        let index = choose|index: int| 0 <= index < self.listeners.entries@.len()
            && self.listeners.entries@[index] == (generation, cursor);
        assert forall|i: int| 0 <= i < self.listeners.entries@.len()
            && #[trigger] self.listeners.entries@[i].0 == generation implies self.listeners.entries@[i].1 == cursor by {
            crate::primitives::resource_registry::identity_entry_at(self.listeners.entries@, i);
            assert(self.listeners.maps_key(generation, self.listeners.entries@[i].1));
            self.listeners.unique_identity_value(generation, cursor, self.listeners.entries@[i].1);
        }
    }

    /// Construct summary retention without preallocating a lifetime history.
    /// The caller assigns distinct scopes to distinct Signal instances.
    pub fn new(scope: u64, initial: T, listener_ceiling: u64, change_ceiling: usize) -> (owner: Self)
        ensures owner.inv(), owner.scope_spec() == scope, owner.value_spec() == initial,
            owner.history_spec().len() == 0, owner.listeners_spec().len() == 0, owner.issued_spec() == 0,
            owner.change_limit_spec() == change_ceiling,
    {
        Self { scope, audit: AuditSink::with_summary(change_ceiling, LastSignalValue { initial }),
            listeners: crate::primitives::resource_registry::ResourceRegistry::new(),
            listener_budget: crate::primitives::budget::Budget::new(listener_ceiling),
            issued: crate::connectives::counter::Counter::new(0) }
    }

    /// Observe the retained latest value without another value owner.
    pub fn value(&self) -> (value: T)
        requires self.inv(), ensures value == self.value_spec(),
    { self.audit.carry() }
    /// Observe the actual AuditSink change head.
    pub fn change_count(&self) -> (count: usize)
        requires self.inv(), ensures count == self.history_spec().len(),
    { self.audit.committed_count() }
    /// Observe the Budget-owned live-listener charge.
    pub fn listener_count(&self) -> (count: u64)
        requires self.inv(), ensures count as int == self.listeners_spec().len(),
    { self.listener_budget.allocated }

    /// Publish one changed value through the shared Record action.
    ///
    /// # Errors
    /// Change capacity refuses unchanged; an identical value succeeds without recording.
    pub fn set_value(&mut self, value: T) -> (result: Result<bool, SignalProfileError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).scope_spec() == old(self).scope_spec(),
            final(self).change_limit_spec() == old(self).change_limit_spec(),
            final(self).listeners_spec() == old(self).listeners_spec(),
            forall|token: SignalListener| #[trigger] final(self).registered_spec(token) == old(self).registered_spec(token),
            final(self).issued_spec() == old(self).issued_spec(),
            result == Ok(false) ==> final(self).same_state(*old(self)),
            result == Ok(true) ==> final(self).value_spec() == value
                && final(self).history_spec().len() == old(self).history_spec().len() + 1,
            result is Err ==> final(self).same_state(*old(self)) && result == Err(SignalProfileError::ChangeCapacity),
            (result == Ok(false)) == (value == old(self).value_spec()),
            (result == Ok(true)) == (value != old(self).value_spec()
                && old(self).history_spec().len() < old(self).change_limit_spec()),
    {
        if value.value_eq(&self.audit.carry()) { return Ok(false); }
        if !self.audit.record_typed(value) { return Err(SignalProfileError::ChangeCapacity); }
        Ok(true)
    }

    /// Register a new generation that can catch up to the retained latest value.
    ///
    /// # Errors
    /// Refuses the listener Budget, exhausted Counter or storage before any logical commit.
    pub fn register(&mut self) -> (result: Result<SignalListener, SignalProfileError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).scope_spec() == old(self).scope_spec(),
            final(self).change_limit_spec() == old(self).change_limit_spec(),
            final(self).history_spec() == old(self).history_spec(), final(self).value_spec() == old(self).value_spec(),
            result matches Ok(token) ==> token.scope_spec() == final(self).scope_spec()
                && final(self).registered_spec(token)
                && token.generation_spec() as nat == final(self).issued_spec()
                && final(self).issued_spec() == old(self).issued_spec() + 1
                && final(self).listeners_spec() == old(self).listeners_spec().push((token.generation_spec(), Cursor { position: 0 })),
            result is Err ==> final(self).same_state(*old(self)),
    {
        if !self.listener_budget.admits_additional(1, 0) { return Err(SignalProfileError::ListenerCapacity); }
        if !self.issued.can_increment() { return Err(SignalProfileError::GenerationExhausted); }
        if self.listeners.try_reserve_entries(1).is_err() { return Err(SignalProfileError::StorageUnavailable); }
        let _admitted = self.listener_budget.try_allocate(1); assert(_admitted);
        let _advanced = self.issued.try_increment(); assert(_advanced);
        let generation = self.issued.value();
        assert(!self.listeners.contains_key_identity(generation));
        self.listeners.register_key(generation, Cursor::new(0));
        Ok(SignalListener { scope: self.scope, generation })
    }

    /// Observe whether this actual listener Cursor trails the retained change head.
    ///
    /// # Errors
    /// Refuses a foreign scope or absent/removed generation.
    pub fn pending(&self, token: SignalListener) -> (result: Result<bool, SignalProfileError>)
        requires self.inv(),
        ensures result matches Ok(pending) ==> self.registered_spec(token) && pending == self.pending_spec(token),
            (result is Err) == !self.registered_spec(token),
            (result == Err(SignalProfileError::ForeignScope)) == (token.scope_spec() != self.scope_spec()),
            (result == Err(SignalProfileError::UnknownListener)) ==
                (token.scope_spec() == self.scope_spec() && !self.registered_spec(token)),
    {
        if token.scope != self.scope { return Err(SignalProfileError::ForeignScope); }
        proof { crate::primitives::resource_registry::identity_entries_are_exact(self.listeners.entries@); }
        match self.listeners.lookup_query(&token.generation) {
            Some(cursor) => {
                proof { self.expose_listener(token.generation, *cursor); }
                Ok(cursor.position < self.audit.committed_count())
            },
            None => Err(SignalProfileError::UnknownListener),
        }
    }

    /// Catch one retained Cursor up to the same AuditSink head, coalescing changes.
    ///
    /// # Errors
    /// Refuses foreign/removed tokens unchanged; repeated notification reports changed=false.
    pub fn notify(&mut self, token: SignalListener) -> (result: Result<SignalObservation<T>, SignalProfileError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).history_spec() == old(self).history_spec(),
            final(self).scope_spec() == old(self).scope_spec(),
            final(self).value_spec() == old(self).value_spec(), final(self).issued_spec() == old(self).issued_spec(),
            forall|other: SignalListener| #[trigger] final(self).registered_spec(other) == old(self).registered_spec(other),
            (result is Err) == !old(self).registered_spec(token),
            result is Err ==> final(self).same_state(*old(self)),
            result matches Ok(observed) ==> observed.value == old(self).value_spec()
                && observed.head == old(self).history_spec().len()
                && observed.changed == old(self).pending_spec(token)
                && final(self).caught_up_spec(token),
    {
        if token.scope != self.scope { return Err(SignalProfileError::ForeignScope); }
        let ghost before = *self;
        proof { crate::primitives::resource_registry::identity_entries_are_exact(self.listeners.entries@); }
        let head = self.audit.committed_count();
        let value = self.audit.carry();
        let result = match self.listeners.lookup_query_mut(&token.generation) {
            Some(cursor) => {
                proof { before.expose_listener(token.generation, *cursor); }
                let changed = cursor.position < head;
                assert(changed == before.pending_spec(token));
                cursor.advance_to(head);
                Ok(SignalObservation { value, head, changed })
            },
            None => Err(SignalProfileError::UnknownListener),
        };
        proof {
            crate::primitives::resource_registry::identity_entries_are_exact(self.listeners.entries@);
            if result is Ok {
                assert(self.listeners.maps_key(token.generation, Cursor { position: head }));
                assert forall|i: int| 0 <= i < self.listeners.entries@.len() implies {
                    let entry = #[trigger] self.listeners.entries@[i];
                    &&& 0 < entry.0 <= self.issued.value_spec()
                    &&& entry.1.position <= self.history_spec().len()
                } by {
                    let entry = self.listeners.entries@[i];
                    assert(entry.0 == before.listeners.entries@[i].0);
                    if entry.0 == token.generation {
                        crate::primitives::resource_registry::identity_entry_at(self.listeners.entries@, i);
                        assert(self.listeners.maps_key(token.generation, entry.1));
                        self.listeners.unique_identity_value(token.generation, Cursor { position: head }, entry.1);
                    } else { assert(entry == before.listeners.entries@[i]); }
                }
                let caught = choose|caught: int| 0 <= caught < self.listeners.entries@.len()
                    && self.listeners.entries@[caught] == (token.generation, Cursor { position: head });
                assert(self.caught_up_spec(token));
            }
            assert forall|other: SignalListener| #[trigger] self.registered_spec(other) == before.registered_spec(other) by {
                if other.scope == self.scope {
                    if self.registered_spec(other) {
                        let index = choose|index: int| 0 <= index < self.listeners.entries@.len()
                            && self.listeners.entries@[index].0 == other.generation;
                        assert(before.listeners.entries@[index].0 == other.generation);
                        assert(before.listeners.contains_key_identity(other.generation));
                    }
                    if before.registered_spec(other) {
                        let index = choose|index: int| 0 <= index < before.listeners.entries@.len()
                            && before.listeners.entries@[index].0 == other.generation;
                        assert(self.listeners.entries@[index].0 == other.generation);
                        assert(self.listeners.contains_key_identity(other.generation));
                    }
                }
            }
        }
        result
    }

    /// Remove a live generation and release its exact listener charge.
    ///
    /// # Errors
    /// Refuses foreign/removed tokens unchanged; later registration never reuses this generation.
    pub fn remove(&mut self, token: SignalListener) -> (result: Result<(), SignalProfileError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).history_spec() == old(self).history_spec(),
            final(self).scope_spec() == old(self).scope_spec(),
            final(self).value_spec() == old(self).value_spec(), final(self).issued_spec() == old(self).issued_spec(),
            (result is Err) == !old(self).registered_spec(token),
            result is Err ==> final(self).same_state(*old(self)),
            result is Ok ==> final(self).listeners_spec().len() + 1 == old(self).listeners_spec().len()
                && !final(self).registered_spec(token),
    {
        if token.scope != self.scope { return Err(SignalProfileError::ForeignScope); }
        let ghost before = *self;
        match self.listeners.take_query(&token.generation) {
            Some(_) => {
                self.listener_budget.release(1);
                proof {
                    crate::primitives::resource_registry::identity_entries_are_exact(self.listeners.entries@);
                    crate::primitives::resource_registry::identity_entries_are_exact(before.listeners.entries@);
                    assert forall|i: int| 0 <= i < self.listeners.entries@.len() implies {
                        let entry = #[trigger] self.listeners.entries@[i];
                        &&& 0 < entry.0 <= self.issued.value_spec()
                        &&& entry.1.position <= self.history_spec().len()
                    } by {
                        let entry = self.listeners.entries@[i];
                        crate::primitives::resource_registry::identity_entry_at(self.listeners.entries@, i);
                        assert(self.listeners.maps_key(entry.0, entry.1));
                        assert(entry.0 != token.generation);
                        assert(before.listeners.maps_key(entry.0, entry.1));
                        before.expose_listener(entry.0, entry.1);
                    }
                }
                Ok(())
            },
            None => Err(SignalProfileError::UnknownListener),
        }
    }
}

/// Erased one-listener logical view used by fused Signal realizations.
pub ghost struct SignalModel {
    /// Current signal value.
    pub current_value: u64,
    /// Whether any actual change has been retained.
    pub change_observed: bool,
    /// Whether the selected listener trails the current change head.
    pub pending: bool,
    /// Whether the selected listener has observed the current change head.
    pub notified: bool,
}

/// The one-listener projection preserves Signal's delivery-state invariants.
pub open spec fn model_valid(model: SignalModel) -> bool {
    &&& !(model.pending && model.notified)
    &&& (!model.change_observed ==> !model.pending && !model.notified)
    &&& (model.change_observed ==> model.pending || model.notified)
}

/// Initial Signal projection before an observed value change.
pub open spec fn model_initial(model: SignalModel, initial_value: u64) -> bool {
    &&& model_valid(model)
    &&& model.current_value == initial_value
    &&& !model.change_observed
    &&& !model.pending
    &&& !model.notified
}

/// One real value change creates exactly one pending notification.
pub open spec fn model_set_value(
    pre: SignalModel,
    post: SignalModel,
    value: u64,
) -> bool {
    &&& model_valid(pre)
    &&& model_valid(post)
    &&& value != pre.current_value
    &&& post.current_value == value
    &&& post.change_observed
    &&& post.pending
    &&& !post.notified
}

/// Delivery moves the one listener from pending to notified.
pub open spec fn model_notify(pre: SignalModel, post: SignalModel) -> bool {
    &&& model_valid(pre)
    &&& model_valid(post)
    &&& pre.pending
    &&& post.current_value == pre.current_value
    &&& post.change_observed == pre.change_observed
    &&& !post.pending
    &&& post.notified
}

/// A fused physical wake may perform Signal's change and delivery actions atomically.
pub open spec fn fused_delivery(value: u64) -> bool {
    value != 0
}

/// Every admitted fused wake has a witness through the two Signal actions.
pub proof fn fused_delivery_has_action_witness(value: u64)
    requires fused_delivery(value),
    ensures exists|initial: SignalModel, pending: SignalModel, notified: SignalModel|
        model_initial(initial, 0)
            && model_set_value(initial, pending, value)
            && model_notify(pending, notified),
{
    let initial = SignalModel {
        current_value: 0,
        change_observed: false,
        pending: false,
        notified: false,
    };
    let pending = SignalModel {
        current_value: value,
        change_observed: true,
        pending: true,
        notified: false,
    };
    let notified = SignalModel {
        current_value: value,
        change_observed: true,
        pending: false,
        notified: true,
    };
    assert(model_initial(initial, 0));
    assert(model_set_value(initial, pending, value));
    assert(model_notify(pending, notified));
}

/// A change-detecting Signal composed from AuditSink and per-listener Cursor.
pub struct Signal {
    /// Value used before the first retained change.
    pub initial_value: u64,
    /// Exclusive upper bound of the value domain.
    pub num_values: u64,
    /// Number of listener cursors.
    pub num_listeners: usize,
    /// Owner of retained value changes.
    pub audit: AuditSink,
    /// Per-listener progress owners.
    pub cursors: Vec<Cursor>,
}

impl Signal {
    /// The current value projected from the audit head or the initial value.
    pub open spec fn current_value_spec(&self) -> u64 {
        if self.audit.log@.len() == 0 {
            self.initial_value
        } else {
            self.audit.log@[self.audit.log@.len() - 1].operation
        }
    }

    /// Whether one listener trails the current audit head.
    pub open spec fn pending_spec(&self, listener: int) -> bool {
        0 <= listener < self.cursors@.len()
            && self.cursors@[listener].position < self.audit.log@.len()
    }

    /// Whether one listener has caught up to a nonempty audit head.
    pub open spec fn notified_spec(&self, listener: int) -> bool {
        &&& 0 <= listener < self.cursors@.len()
        &&& self.audit.log@.len() > 0
        &&& self.cursors@[listener].position == self.audit.log@.len()
    }

    /// Maintained construction invariant.
    pub open spec fn inv(&self) -> bool {
        &&& self.num_values > 0
        &&& self.initial_value < self.num_values
        &&& self.num_listeners == self.cursors@.len()
        &&& self.audit.inv()
        &&& forall|i: int| 0 <= i < self.audit.log@.len()
            ==> #[trigger] self.audit.log@[i].operation < self.num_values
        &&& forall|i: int| 0 <= i < self.cursors@.len()
            ==> #[trigger] self.cursors@[i].position <= self.audit.log@.len()
    }

    /// Construct an empty change log and one zero cursor per listener.
    #[expect(clippy::arithmetic_side_effects, reason = "the loop invariant and guard prove the listener index increment remains in range")]
    pub fn new(
        initial_value: u64,
        num_values: u64,
        num_listeners: usize,
        max_changes: usize,
    ) -> (signal: Self)
        requires
            num_values > 0,
            initial_value < num_values,
        ensures
            signal.inv(),
            signal.initial_value == initial_value,
            signal.num_values == num_values,
            signal.num_listeners == num_listeners,
            signal.audit.max_log_len == max_changes,
            signal.audit.log@.len() == 0,
            signal.current_value_spec() == initial_value,
            forall|i: int| 0 <= i < signal.cursors@.len()
                ==> #[trigger] signal.cursors@[i].position == 0,
    {
        let audit = AuditSink::new(max_changes);
        let mut cursors: Vec<Cursor> = Vec::new();
        let mut index: usize = 0;
        while index < num_listeners
            invariant
                index <= num_listeners,
                cursors@.len() == index,
                forall|i: int| 0 <= i < cursors@.len()
                    ==> #[trigger] cursors@[i].position == 0,
            decreases num_listeners - index,
        {
            cursors.push(Cursor::new(0));
            index += 1;
        }
        Self {
            initial_value,
            num_values,
            num_listeners,
            audit,
            cursors,
        }
    }

    /// Read the current value projection.
    #[expect(clippy::indexing_slicing, reason = "the nonempty branch proves the audit index is in bounds")]
    #[expect(clippy::arithmetic_side_effects, reason = "the nonempty branch proves the audit length can be decremented")]
    pub fn current_value(&self) -> (value: u64)
        requires self.inv(),
        ensures
            value == self.current_value_spec(),
            value < self.num_values,
    {
        if self.audit.log.is_empty() {
            self.initial_value
        } else {
            self.audit.log[self.audit.log.len() - 1].operation
        }
    }

    /// Report whether at least one value change has been recorded.
    pub fn has_changes(&self) -> (changed: bool)
        requires self.inv(),
        ensures changed == (self.audit.log@.len() > 0),
    {
        !self.audit.log.is_empty()
    }

    /// Report whether `set_value` is enabled for the supplied value.
    pub fn can_set_value(&self, value: u64) -> (enabled: bool)
        requires self.inv(),
        ensures enabled == (value < self.num_values
            && value != self.current_value_spec()
            && self.audit.log@.len() < self.audit.max_log_len),
    {
        value < self.num_values
            && value != self.current_value()
            && self.audit.log.len() < self.audit.max_log_len
    }

    /// Read whether one listener is pending.
    #[expect(clippy::indexing_slicing, reason = "the caller supplies an in-range listener")]
    pub fn is_pending(&self, listener: usize) -> (pending: bool)
        requires
            self.inv(),
            listener < self.cursors.len(),
        ensures pending == self.pending_spec(listener as int),
    {
        self.cursors[listener].position < self.audit.log.len()
    }

    /// Read whether one listener has caught up to a nonempty head.
    #[expect(clippy::indexing_slicing, reason = "the caller supplies an in-range listener")]
    pub fn is_notified(&self, listener: usize) -> (notified: bool)
        requires
            self.inv(),
            listener < self.cursors.len(),
        ensures notified == self.notified_spec(listener as int),
    {
        !self.audit.log.is_empty()
            && self.cursors[listener].position == self.audit.log.len()
    }

    /// Append one real value change through the AuditSink owner.
    pub fn set_value(&mut self, value: u64)
        requires
            old(self).inv(),
            value < old(self).num_values,
            value != old(self).current_value_spec(),
            old(self).audit.log@.len() < old(self).audit.max_log_len,
        ensures
            final(self).inv(),
            final(self).initial_value == old(self).initial_value,
            final(self).num_values == old(self).num_values,
            final(self).num_listeners == old(self).num_listeners,
            final(self).audit.operator == old(self).audit.operator,
            final(self).audit.max_log_len == old(self).audit.max_log_len,
            final(self).audit.log@.len() == old(self).audit.log@.len() + 1,
            final(self).audit.last_hash
                == old(self).audit.operator.combine_spec(old(self).audit.last_hash, value),
            final(self).audit.log@[old(self).audit.log@.len() as int].operation == value,
            final(self).audit.log@[old(self).audit.log@.len() as int].prev_hash
                == old(self).audit.last_hash,
            forall|index: int| 0 <= index < old(self).audit.log@.len() ==>
                #[trigger] final(self).audit.log@[index] == old(self).audit.log@[index],
            final(self).current_value_spec() == value,
            final(self).cursors@ == old(self).cursors@,
    {
        let ghost prior_log = self.audit.log@;
        let ghost prior_cursors = self.cursors@;
        let _accepted = self.audit.record(value);
        assert(_accepted);
        assert(self.audit.log@.len() == prior_log.len() + 1);
        assert(self.audit.log@[prior_log.len() as int].operation == value);
        assert(self.current_value_spec() == value);
        assert(self.cursors@ == prior_cursors);
        assert forall|i: int| 0 <= i < self.audit.log@.len()
            implies #[trigger] self.audit.log@[i].operation < self.num_values by {
            if i < prior_log.len() {
                assert(self.audit.log@[i] == prior_log[i]);
            } else {
                assert(i == prior_log.len());
            }
        }
        assert forall|i: int| 0 <= i < self.cursors@.len()
            implies #[trigger] self.cursors@[i].position <= self.audit.log@.len() by {
            assert(self.cursors@[i].position <= prior_log.len());
        }
    }

    /// Advance one pending listener exactly to the current audit head.
    #[expect(clippy::indexing_slicing, reason = "the caller and invariant prove the listener index is in bounds")]
    pub fn notify_listener(&mut self, listener: usize)
        requires
            old(self).inv(),
            listener < old(self).cursors.len(),
            old(self).cursors@[listener as int].position < old(self).audit.log@.len(),
        ensures
            final(self).inv(),
            final(self).initial_value == old(self).initial_value,
            final(self).num_values == old(self).num_values,
            final(self).num_listeners == old(self).num_listeners,
            final(self).audit == old(self).audit,
            final(self).cursors@
                == old(self).cursors@.update(
                    listener as int,
                    Cursor { position: old(self).audit.log@.len() as usize },
                ),
    {
        let head = self.audit.log.len();
        let ghost prior_cursors = self.cursors@;
        let mut advanced = Cursor::new(self.cursors[listener].position);
        advanced.advance_to(head);
        self.cursors.set(listener, advanced);
        assert(self.cursors@ == prior_cursors.update(listener as int, self.cursors@[listener as int]));
        assert forall|i: int| 0 <= i < self.cursors@.len()
            implies #[trigger] self.cursors@[i].position <= self.audit.log@.len() by {
            if i == listener as int {
                assert(self.cursors@[i].position == self.audit.log@.len());
            } else {
                assert(self.cursors@[i] == prior_cursors[i]);
            }
        }
    }
}

}
