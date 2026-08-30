//! Canonical Counter connective relations for retained integer progress.

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

}
