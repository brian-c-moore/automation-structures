//! Executable Cursor connective.
//!
//! Cursor retains a position. It carries no delivery, replay, persistence, or exactly-once
//! contract clause. Its owner supplies the admissible bound and movement rule.

use vstd::prelude::*;

mod position_seal {
    use vstd::prelude::*;
    verus! {
        pub trait Sealed {}
    }
}

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

/// Sealed integer-domain content for the existing retained-position owner.
/// This adapter holds no Cursor, generation, queue or other governed state.
pub trait CursorPosition: Copy + Sized + position_seal::Sealed {
    /// Exact mathematical interpretation of this integer representation.
    spec fn ordinal(self) -> nat;
    /// Greatest ordinal represented by this integer type on the selected target.
    spec fn max_ordinal() -> nat;
    /// Expose the integer bound; sealing alone is not a logical proof premise.
    proof fn expose_integer_bound(self)
        ensures self.ordinal() <= Self::max_ordinal(),
            Self::max_ordinal() <= u64::MAX as nat;
    /// Initial position, with no conversion or admission failure.
    fn zero() -> (position: Self)
        ensures position.ordinal() == 0;
    /// Executable ceiling used by the publication owner before minting identity.
    fn limit() -> (limit: u64)
        ensures limit as nat == Self::max_ordinal();
    /// Pure integer comparison used by the checked Cursor's existing refusal.
    fn less_than(self, other: Self) -> (less: bool)
        ensures less == (self.ordinal() < other.ordinal());
    /// Pure checked integer successor; it advances no retained owner state.
    fn checked_successor(self) -> (next: Option<Self>)
        ensures (next is Some) == (self.ordinal() < Self::max_ordinal()),
            next matches Some(position) ==> position.ordinal() == self.ordinal() + 1;
}

impl position_seal::Sealed for usize {}
impl position_seal::Sealed for u64 {}

impl CursorPosition for usize {
    open spec fn ordinal(self) -> nat { self as nat }
    open spec fn max_ordinal() -> nat { usize::MAX as nat }
    proof fn expose_integer_bound(self) {}
    fn zero() -> (position: Self) { 0 }
    fn limit() -> (limit: u64) { usize::MAX as u64 }
    fn less_than(self, other: Self) -> (less: bool) { self < other }
    fn checked_successor(self) -> (next: Option<Self>) { self.checked_add(1) }
}

impl CursorPosition for u64 {
    open spec fn ordinal(self) -> nat { self as nat }
    open spec fn max_ordinal() -> nat { u64::MAX as nat }
    proof fn expose_integer_bound(self) {}
    fn zero() -> (position: Self) { 0 }
    fn limit() -> (limit: u64) { u64::MAX }
    fn less_than(self, other: Self) -> (less: bool) { self < other }
    fn checked_successor(self) -> (next: Option<Self>) { self.checked_add(1) }
}

/// A retained position with owner-supplied movement contract clauses.
pub struct Cursor<P: CursorPosition = usize> {
    /// Retained monotone position.
    pub position: P,
}

impl Cursor<usize> {
    /// Construct a cursor at an admitted position.
    pub fn new(position: usize) -> (cursor: Self)
        ensures cursor.position == position,
    {
        Self::from_position(position)
    }
}

impl<P: CursorPosition> Cursor<P> {
    /// Mathematical observation of this owner's selected integer position.
    pub closed spec fn position_spec(&self) -> nat { self.position.ordinal() }

    /// Expose this retained observation's exact relationship and integer bound.
    pub proof fn expose_position_bound(&self)
        ensures self.position_spec() == self.position.ordinal(),
            self.position_spec() <= P::max_ordinal(), P::max_ordinal() <= u64::MAX as nat,
    {
        self.position.expose_integer_bound();
    }

    /// Construct the selected profile without another retained-position owner.
    pub fn from_position(position: P) -> (cursor: Self)
        ensures cursor.position == position,
            cursor.position_spec() == position.ordinal(),
    {
        Self { position }
    }

    /// Move monotonically to `position`.
    pub fn advance_to(&mut self, position: P)
        requires old(self).position.ordinal() <= position.ordinal(),
        ensures final(self).position == position,
            final(self).position_spec() == position.ordinal(),
            final(self).position_spec() >= old(self).position_spec(),
    {
        self.position = position;
    }
}

}
