//! Reusable boolean marker relations.

use vstd::prelude::*;

verus! {

/// Set a marker when selected and otherwise preserve it.
pub open spec fn set_if(before: bool, after: bool, selected: bool) -> bool {
    after == if selected { true } else { before }
}

/// A selected transition that leaves the marker clear is rejected.
pub proof fn selected_unset_rejected(before: bool)
    ensures !set_if(before, false, true),
{
}

/// Clear a marker when selected and otherwise preserve it.
pub open spec fn clear_if(before: bool, after: bool, selected: bool) -> bool {
    after == if selected { false } else { before }
}

}
