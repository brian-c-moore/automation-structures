//! Fixed-sequence execution carrier.

use vstd::prelude::*;

verus! {

/// Transition for beginning one sequential position.
pub open spec fn begin_step_action(
    before_position: nat,
    after_position: nat,
    steps: nat,
    selected: bool,
    accepted: bool,
) -> bool {
    let enabled = selected && before_position < steps;
    &&& accepted == enabled
    &&& after_position == before_position
}

/// Transition for completing one sequential position.
pub open spec fn complete_step_action(
    before_position: nat,
    after_position: nat,
    steps: nat,
    selected: bool,
    value_admitted: bool,
    accepted: bool,
) -> bool {
    let enabled = selected
        && value_admitted
        && before_position < steps;
    &&& accepted == enabled
    &&& after_position == if accepted {
        before_position + 1
    } else {
        before_position
    }
}

/// Fixed-sequence execution owner.
pub struct Sequential {
    /// Total number of steps.
    pub steps: usize,
    /// Exclusive upper bound of carried values.
    pub value_domain_size: u64,
    /// Program counter identifying the next step.
    pub pc: usize,
    /// Current carried value.
    pub value: u64,
    /// Whether the current step is active.
    pub active: bool,
    /// Values committed by completed steps.
    pub history: Vec<u64>,
}

impl Sequential {
    /// Whether every retained value lies within the configured value domain.
    pub open spec fn values_valid(&self) -> bool {
        forall|i: int| 0 <= i < self.history@.len()
            ==> #[trigger] self.history@[i] < self.value_domain_size
    }

    /// Whether cursor, activity, history, and values have consistent shape.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.steps > 0
        &&& self.value_domain_size > 0
        &&& self.pc <= self.steps
        &&& self.value < self.value_domain_size
        &&& self.values_valid()
    }

    /// Whether committed-history length agrees with the next execution position.
    pub open spec fn history_position_agreement(&self) -> bool {
        self.history@.len() == self.pc
    }

    /// Compatibility alias for [`Self::history_position_agreement`].
    ///
    /// This predicate does not characterize a general total-order relation.
    pub open spec fn total_order(&self) -> bool {
        self.history_position_agreement()
    }

    /// Whether an active step always precedes terminal completion.
    pub open spec fn active_before_done(&self) -> bool {
        self.active ==> self.pc < self.steps
    }

    /// Whether all fixed-sequence execution contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.history_position_agreement() && self.active_before_done()
    }

    /// Construct an inactive execution at the first step.
    pub fn new(steps: usize, value_domain_size: u64, initial_value: u64) -> (s: Sequential)
        requires
            steps > 0,
            value_domain_size > 0,
            initial_value < value_domain_size,
        ensures
            s.steps == steps,
            s.value_domain_size == value_domain_size,
            s.pc == 0,
            s.value == initial_value,
            !s.active,
            s.history@.len() == 0,
            s.inv(),
    {
        Sequential {
            steps,
            value_domain_size,
            pc: 0,
            value: initial_value,
            active: false,
            history: Vec::new(),
        }
    }

    /// `BeginStep`, with disabled calls exposed as a stuttering rejection.
    pub fn begin_step(&mut self) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).pc < old(self).steps && !old(self).active),
            begin_step_action(
                old(self).pc as nat,
                final(self).pc as nat,
                old(self).steps as nat,
                !old(self).active,
                accepted,
            ),
            crate::connectives::marker::set_if(
                old(self).active,
                final(self).active,
                accepted,
            ),
            final(self).steps == old(self).steps,
            final(self).value_domain_size == old(self).value_domain_size,
            if accepted {
                final(self).active
                    && final(self).pc == old(self).pc
                    && final(self).value == old(self).value
                    && final(self).history@ == old(self).history@
            } else {
                final(self).pc == old(self).pc
                    && final(self).value == old(self).value
                    && final(self).active == old(self).active
                    && final(self).history@ == old(self).history@
            },
            final(self).inv(),
    {
        if self.pc < self.steps && !self.active {
            self.active = true;
            true
        } else {
            false
        }
    }

    /// `CompleteStep`, including its nondeterministic ValueDomain choice as an
    /// explicit caller value. An out-of-domain choice is not an enabled TLA+
    /// action and therefore stutters with `false`.
    #[expect(clippy::arithmetic_side_effects, reason = "Verus proves pc remains within the step bound")]
    pub fn complete_step(&mut self, next_value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).active && next_value < old(self).value_domain_size),
            complete_step_action(
                old(self).pc as nat,
                final(self).pc as nat,
                old(self).steps as nat,
                old(self).active,
                next_value < old(self).value_domain_size,
                accepted,
            ),
            crate::connectives::marker::clear_if(
                old(self).active,
                final(self).active,
                accepted,
            ),
            final(self).steps == old(self).steps,
            final(self).value_domain_size == old(self).value_domain_size,
            if accepted {
                !final(self).active
                    && final(self).pc == old(self).pc + 1
                    && final(self).value == next_value
                    && final(self).history@ == old(self).history@.push(next_value)
            } else {
                final(self).pc == old(self).pc
                    && final(self).value == old(self).value
                    && final(self).active == old(self).active
                    && final(self).history@ == old(self).history@
            },
            final(self).inv(),
    {
        if self.active && next_value < self.value_domain_size {
            let ghost old_history = self.history@;
            self.value = next_value;
            self.history.push(next_value);
            self.pc += 1;
            self.active = false;
            assert(self.values_valid()) by {
                assert forall|i: int| 0 <= i < self.history@.len()
                    implies #[trigger] self.history@[i] < self.value_domain_size by {
                    if i < old_history.len() {
                        assert(self.history@[i] == old_history[i]);
                    } else {
                        assert(i == old_history.len());
                        assert(self.history@[i] == next_value);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    /// `DoneStuttering`: enabled exactly at the terminal inactive state and
    /// never changes carrier state.
    pub fn done_stuttering(&mut self) -> (enabled: bool)
        requires old(self).inv(),
        ensures
            enabled == (old(self).pc == old(self).steps && !old(self).active),
            final(self).steps == old(self).steps,
            final(self).value_domain_size == old(self).value_domain_size,
            final(self).pc == old(self).pc,
            final(self).value == old(self).value,
            final(self).active == old(self).active,
            final(self).history@ == old(self).history@,
            final(self).inv(),
    {
        self.pc == self.steps && !self.active
    }
}

}
