//! Reusable OrderingPass connective contract.
//!
//! The first executable role is FIFO sequence order. It is expressed over a logical registry view
//! so every matching realization reuses one ordering predicate.

use vstd::prelude::*;

verus! {

/// One ranked item is strictly ordered before another.
pub open spec fn strictly_before(left: nat, right: nat) -> bool {
    left < right
}

/// Executable check for the shared strict-order relation.
pub fn is_strictly_before(left: usize, right: usize) -> (ordered: bool)
    ensures ordered == strictly_before(left as nat, right as nat),
{
    left < right
}

/// The selected value is the first value in one ordered sequence.
pub open spec fn selects_first<T>(items: Seq<T>, selected: T) -> bool {
    items.len() > 0 && items[0] == selected
}

/// A value different from the retained head is not the first ordered selection.
pub proof fn non_head_rejected<T>(items: Seq<T>, selected: T)
    requires
        items.len() > 0,
        items[0] != selected,
    ensures !selects_first(items, selected),
{
}

/// Registry keys form one contiguous FIFO interval from `head` through `tail`.
pub open spec fn fifo_sequence_order(
    entries: Seq<(u64, u64)>,
    head: nat,
    tail: nat,
) -> bool {
    &&& head + entries.len() == tail
    &&& forall|index: int| 0 <= index < entries.len() ==>
        #[trigger] entries[index].0 as nat == head + index as nat
}

}
