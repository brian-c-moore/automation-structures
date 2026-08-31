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
use vstd::prelude::*;

verus! {

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
            final(self).audit.log@.len() == old(self).audit.log@.len() + 1,
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
            final(self).audit.log@ == old(self).audit.log@,
            final(self).audit.last_hash == old(self).audit.last_hash,
            final(self).cursors@[listener as int].position == old(self).audit.log@.len(),
            forall|i: int| 0 <= i < final(self).cursors@.len() && i != listener
                ==> final(self).cursors@[i].position == old(self).cursors@[i].position,
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
