//! Executable equality adapters whose contracts are tied to Verus equality.

use vstd::prelude::*;

verus! {

/// Executable equality for values used by generic verified carriers.
pub trait ValueEq: Sized {
    /// Compare two values using the equality seen by specifications.
    fn value_eq(&self, other: &Self) -> (equal: bool)
        ensures equal == (*self == *other);
}

impl ValueEq for u64 {
    fn value_eq(&self, other: &Self) -> (equal: bool) {
        *self == *other
    }
}

impl ValueEq for usize {
    fn value_eq(&self, other: &Self) -> (equal: bool) {
        *self == *other
    }
}

impl ValueEq for (usize, usize, u64) {
    fn value_eq(&self, other: &Self) -> (equal: bool) {
        self.0 == other.0 && self.1 == other.1 && self.2 == other.2
    }
}

}
