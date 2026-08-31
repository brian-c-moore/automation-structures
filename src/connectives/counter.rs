//! Counter connective relations for retained integer progress.

use vstd::prelude::*;

verus! {

/// A retained count remains nonnegative.
pub open spec fn nonnegative(value: int) -> bool {
    0 <= value
}

/// A retained generation or occurrence count is present and nonzero.
pub open spec fn positive(value: int) -> bool {
    &&& nonnegative(value)
    &&& value > 0
}

/// One occurrence advances retained progress by one.
pub open spec fn increment(pre: int, post: int) -> bool {
    post == pre + 1
}

/// A counted occurrence that leaves its retained count unchanged is rejected.
pub proof fn stalled_increment_rejected(pre: int)
    ensures !increment(pre, pre),
{
}

/// An unselected occurrence preserves retained progress.
pub open spec fn stutter(pre: int, post: int) -> bool {
    post == pre
}

/// One selected occurrence decrements while every unselected occurrence stutters.
pub open spec fn decrement_if(pre: int, post: int, selected: bool) -> bool {
    post == pre - if selected { 1int } else { 0int }
}

/// A selected decrement has available credit and preserves nonnegativity.
pub open spec fn guarded_decrement_if(pre: int, post: int, selected: bool) -> bool {
    &&& nonnegative(pre)
    &&& decrement_if(pre, post, selected)
    &&& nonnegative(post)
    &&& (selected ==> 0 < pre)
}

/// A retained nonnegative occurrence or generation count.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Counter {
    /// Retained occurrence or generation count.
    pub value: u64,
}

impl Counter {
    /// Mathematical view of the retained count.
    pub open spec fn value_spec(&self) -> nat {
        self.value as nat
    }

    /// Construct a counter at `value`.
    pub fn new(value: u64) -> (counter: Self)
        ensures counter.value_spec() == value as nat,
    {
        Self { value }
    }

    /// Current retained count.
    pub fn value(&self) -> (value: u64)
        ensures value as nat == self.value_spec(),
    {
        self.value
    }

    /// Increment unless the `u64` representation is exhausted.
    #[must_use]
    pub fn try_increment(&mut self) -> (accepted: bool)
        ensures
            accepted == (old(self).value_spec() < u64::MAX as nat),
            accepted ==> final(self).value_spec() == old(self).value_spec() + 1,
            !accepted ==> final(self).value_spec() == old(self).value_spec(),
    {
        if self.value == u64::MAX {
            return false;
        }
        self.value = self.value + 1;
        true
    }

    /// Decrement when positive.
    #[must_use]
    pub fn try_decrement(&mut self) -> (accepted: bool)
        ensures
            accepted == (old(self).value_spec() > 0),
            accepted ==> final(self).value_spec() + 1 == old(self).value_spec(),
            !accepted ==> final(self).value_spec() == old(self).value_spec(),
    {
        if self.value == 0 {
            return false;
        }
        self.value = self.value - 1;
        true
    }
}

}
