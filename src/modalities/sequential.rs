// Faithful executable carrier for formal/execution/carriers/Sequential.tla.
// A finite value domain is represented by indices 0..value_domain_size.

use vstd::prelude::*;

verus! {

pub struct Sequential {
    pub steps: usize,
    pub value_domain_size: u64,
    pub pc: usize,
    pub value: u64,
    pub active: bool,
    pub history: Vec<u64>,
}

impl Sequential {
    pub open spec fn values_valid(&self) -> bool {
        forall|i: int| 0 <= i < self.history@.len()
            ==> #[trigger] self.history@[i] < self.value_domain_size
    }

    pub open spec fn type_invariant(&self) -> bool {
        &&& self.steps > 0
        &&& self.value_domain_size > 0
        &&& self.pc <= self.steps
        &&& self.value < self.value_domain_size
        &&& self.values_valid()
    }

    pub open spec fn total_order(&self) -> bool {
        self.history@.len() == self.pc
    }

    pub open spec fn active_before_done(&self) -> bool {
        self.active ==> self.pc < self.steps
    }

    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.total_order() && self.active_before_done()
    }

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
    pub fn complete_step(&mut self, next_value: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            accepted == (old(self).active && next_value < old(self).value_domain_size),
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
            self.pc = self.pc + 1;
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
