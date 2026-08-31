//! Executable Cursor connective.
//!
//! Cursor retains a position. It carries no delivery, replay, persistence, or exactly-once
//! obligation. Its owner supplies the admissible bound and movement rule.

use vstd::prelude::*;

verus! {

/// Owner-supplied bound for a retained cursor position.
pub open spec fn cursor_admitted(position: nat, head: nat) -> bool {
    position <= head
}

/// A retained position beyond the admitted head is rejected.
pub proof fn regression_rejected(position: nat, head: nat)
    requires position > head,
    ensures !cursor_admitted(position, head),
{
}

/// A retained position with owner-supplied movement obligations.
pub struct Cursor {
    /// Retained monotone position.
    pub position: usize,
}

impl Cursor {
    /// Construct a cursor at an admitted position.
    pub fn new(position: usize) -> (cursor: Self)
        ensures cursor.position == position,
    {
        Self { position }
    }

    /// Move monotonically to `position`.
    pub fn advance_to(&mut self, position: usize)
        requires old(self).position <= position,
        ensures final(self).position == position,
    {
        self.position = position;
    }
}

}
