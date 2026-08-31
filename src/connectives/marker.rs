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

/// A reusable retained boolean marker.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Marker {
    /// Retained marker state.
    pub marked: bool,
}

impl Marker {
    /// Construct a marker with an explicit initial state.
    pub fn new(marked: bool) -> (marker: Self)
        ensures marker.marked == marked,
    {
        Self { marked }
    }

    /// Whether the marker is set.
    pub fn is_marked(&self) -> (marked: bool)
        ensures marked == self.marked,
    {
        self.marked
    }

    /// Set the marker and return whether its state changed.
    pub fn set(&mut self) -> (changed: bool)
        ensures
            final(self).marked,
            changed == !old(self).marked,
    {
        let changed = !self.marked;
        self.marked = true;
        changed
    }

    /// Clear the marker and return whether its state changed.
    pub fn clear(&mut self) -> (changed: bool)
        ensures
            !final(self).marked,
            changed == old(self).marked,
    {
        let changed = self.marked;
        self.marked = false;
        changed
    }
}

}
