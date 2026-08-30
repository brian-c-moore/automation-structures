//! Reusable Buffer connective contract.
//!
//! Buffer is a connective role rather than a second queue implementation. It owns the generic
//! retained-sequence bound used by compositions. A compact ring, fixed array, or other physical
//! layout receives Buffer credit only through a checked view satisfying this contract.

use vstd::prelude::*;

verus! {

/// A retained logical sequence fits within its admitted capacity.
pub open spec fn buffer_bounded<T>(values: Seq<T>, capacity: nat) -> bool {
    values.len() <= capacity
}

/// A retained sequence at exact capacity remains admitted.
pub proof fn exact_capacity_admitted<T>(values: Seq<T>, capacity: nat)
    requires values.len() == capacity,
    ensures buffer_bounded(values, capacity),
{
}

}
