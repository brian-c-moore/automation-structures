//! Reusable Buffer connective contract.
//!
//! Buffer is a connective role rather than a second queue implementation. It owns the generic
//! retained-sequence bound used by compositions. A compact ring, fixed array, or other physical
//! layout receives Buffer credit only through a checked view satisfying this contract.

use vstd::prelude::*;

use crate::compositions::reduction::{IncrementalReduction, ReductionProjection};
use crate::primitives::audit_sink::AdditiveChain;
use crate::value_eq::ValueEq;

verus! {

// Delegate through pinned vstd's generic Iterator contract. Its concrete Vec
// specialization has no next binding, while the standard trait specification
// supplies the same FIFO transfer law without introducing another assumption.
pub(crate) fn advance_owned_transfer<T, I: core::iter::Iterator<Item=T>>(transfer: &mut I) -> (value: Option<T>)
    requires vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(old(transfer)),
    ensures vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(final(transfer)),
        if vstd::std_specs::iter::IteratorSpec::remaining(old(transfer)).len() > 0 {
            value == Some(vstd::std_specs::iter::IteratorSpec::remaining(old(transfer))[0])
                && vstd::std_specs::iter::IteratorSpec::remaining(final(transfer))
                    == vstd::std_specs::iter::IteratorSpec::remaining(old(transfer)).drop_first()
        } else {
            value == None && vstd::std_specs::iter::IteratorSpec::remaining(final(transfer))
                == vstd::std_specs::iter::IteratorSpec::remaining(old(transfer))
        },
{ core::iter::Iterator::next(transfer) }

/// Pure domain sizing of one retained Buffer value.
pub trait BufferSizeProjection<T> {
    /// Mathematical encoded size, independent of automation state.
    spec fn size_spec(&self, value: T) -> usize;
    /// Evaluate the declared size without retaining a counter or aggregate.
    fn size(&self, value: &T) -> (size: usize)
        ensures size == self.size_spec(*value);
}

/// A projected total cannot be represented by the public size type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum BufferSizeError {
    /// The exact projected total exceeds usize::MAX.
    Overflow,
}

/// Mathematical projected size of an immutable retained prefix.
pub open spec fn projected_size_to<T, P: BufferSizeProjection<T>>(
    values: Seq<T>, end: int, projection: P,
) -> int
    decreases end,
{
    if end <= 0 || end > values.len() { 0 }
    else { projected_size_to(values, end - 1, projection)
        + projection.size_spec(values[end - 1]) as int }
}

/// Nonnegative sizes make every retained prefix no larger than a later prefix.
pub proof fn projected_size_monotone<T, P: BufferSizeProjection<T>>(
    values: Seq<T>, earlier: int, later: int, projection: P,
)
    requires 0 <= earlier <= later <= values.len(),
    ensures projected_size_to(values, earlier, projection)
        <= projected_size_to(values, later, projection),
    decreases later - earlier,
{
    if earlier < later {
        projected_size_monotone(values, earlier, later - 1, projection);
    }
}

// Borrowed sizing content; the named Reduction owns its entire traversal.
struct BufferSizeInput<'a, T, P: BufferSizeProjection<T>> {
    buffer: &'a Buffer<T>,
    projection: &'a P,
}
impl<'a, T, P: BufferSizeProjection<T>> ReductionProjection<AdditiveChain>
    for BufferSizeInput<'a, T, P>
{
    closed spec fn domain_len(&self) -> nat { self.buffer.values@.len() }
    closed spec fn item_spec(&self, position: int) -> u64 {
        self.projection.size_spec(self.buffer.values@[position]) as u64
    }
    fn len(&self) -> (length: usize) { self.buffer.values.len() }
    #[expect(clippy::indexing_slicing, reason = "ReductionProjection requires position below the retained Buffer value length")]
    fn item(&self, position: usize) -> (item: u64) {
        self.projection.size(&self.buffer.values[position]) as u64
    }
}
impl<'a, T, P: BufferSizeProjection<T>> BufferSizeInput<'a, T, P> {
    proof fn prefix_correct(&self, end: int)
        requires 0 <= end <= self.buffer.values@.len(),
            crate::compositions::reduction::projected_prefix_admitted(*self, AdditiveChain, end),
        ensures crate::compositions::reduction::projected_fold_to(*self, AdditiveChain, end) as int
            == projected_size_to(self.buffer.values@, end, *self.projection),
        decreases end,
    {
        if end > 0 { self.prefix_correct(end - 1); }
    }
}

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

/// Whether `value` occurs in the first `end` retained positions.
pub open spec fn contains_up_to<T>(values: Seq<T>, end: int, value: T) -> bool {
    exists|index: int| 0 <= index < end && index < values.len() && values[index] == value
}

/// Whether `value` is retained by a Buffer.
pub open spec fn contains_value<T>(values: Seq<T>, value: T) -> bool {
    contains_up_to(values, values.len() as int, value)
}

/// Whether every retained value is distinct.
pub open spec fn all_distinct<T>(values: Seq<T>) -> bool {
    forall|left: int, right: int|
        0 <= left < values.len() && 0 <= right < values.len() && left != right
            ==> #[trigger] values[left] != #[trigger] values[right]
}

/// Extending a considered prefix exposes exactly its new final value.
pub proof fn lemma_contains_extend<T>(values: Seq<T>, end: int, value: T)
    requires 0 <= end < values.len(),
    ensures contains_up_to(values, end + 1, value)
        == (contains_up_to(values, end, value) || values[end] == value),
{
    if contains_up_to(values, end + 1, value) {
        let index = choose|index: int|
            0 <= index < end + 1 && index < values.len() && values[index] == value;
        assert(index < end || index == end);
    }
    if contains_up_to(values, end, value) {
        let index = choose|index: int|
            0 <= index < end && index < values.len() && values[index] == value;
        assert(0 <= index < end + 1 && index < values.len());
    }
    if values[end] == value {
        assert(0 <= end < end + 1 && end < values.len());
    }
}

/// Appending one value extends membership by exactly that value.
pub proof fn lemma_push_contains<T>(values: Seq<T>, added: T, value: T)
    ensures contains_value(values.push(added), value)
        == (contains_value(values, value) || value == added),
{
    let pushed = values.push(added);
    if contains_value(pushed, value) {
        let index = choose|index: int| 0 <= index < pushed.len() && pushed[index] == value;
        if index < values.len() {
            assert(pushed[index] == values[index]);
        } else {
            assert(index == values.len());
        }
    }
    if contains_value(values, value) {
        let index = choose|index: int| 0 <= index < values.len() && values[index] == value;
        assert(pushed[index] == values[index]);
    }
    if value == added {
        assert(pushed[values.len() as int] == value);
    }
}

/// Every in-range retained position witnesses membership of its value.
pub proof fn indexed_value_contained<T>(values: Seq<T>, index: int)
    requires 0 <= index < values.len(),
    ensures contains_value(values, values[index]),
{
    assert(0 <= index < values.len() && values[index] == values[index]);
}

/// Removing one position from a distinct sequence removes exactly that value.
pub proof fn contains_remove_distinct<T>(values: Seq<T>, removed: int, value: T)
    requires
        all_distinct(values),
        0 <= removed < values.len(),
    ensures
        contains_value(values.remove(removed), value)
            == (contains_value(values, value) && value != values[removed]),
{
    values.remove_ensures(removed);
    let reduced = values.remove(removed);
    if contains_value(reduced, value) {
        let index = choose|index: int|
            0 <= index < reduced.len() && reduced[index] == value;
        let old_index = if index < removed { index } else { index + 1 };
        assert(0 <= old_index < values.len());
        assert(old_index != removed);
        assert(reduced[index] == values[old_index]);
        assert(contains_value(values, value));
        if value == values[removed] {
            assert(values[old_index] == values[removed]);
            assert(false);
        }
    }
    if contains_value(values, value) && value != values[removed] {
        let old_index = choose|index: int|
            0 <= index < values.len() && values[index] == value;
        assert(old_index != removed);
        let index = if old_index < removed { old_index } else { old_index - 1 };
        assert(0 <= index < reduced.len());
        assert(reduced[index] == values[old_index]);
    }
}

/// A bounded FIFO connective.
pub struct Buffer<T> {
    /// Maximum number of retained values.
    pub capacity: usize,
    /// Retained values in FIFO order.
    pub values: Vec<T>,
}

impl<T> Buffer<T> {
    /// Adopt an already owned sequence without allocation or copying values.
    /// Its initial length is the fixed admitted capacity.
    pub fn from_values(values: Vec<T>) -> (buffer: Self)
        ensures buffer.well_formed(), buffer.values@ == values@,
            buffer.capacity == values@.len(),
    { Self { capacity: values.len(), values } }

    /// Transfer the retained sequence once in FIFO order without shifting it.
    /// This consumes the Buffer. Vec's owned iterator is the pinned data-library
    /// binding; it moves each value once and allocates no replacement sequence.
    pub fn into_transfer(self) -> (transfer: std::vec::IntoIter<T>)
        ensures vstd::std_specs::iter::IteratorSpec::remaining(&transfer) == self.values@,
            vstd::std_specs::iter::IteratorSpec::obeys_prophetic_iter_laws(&transfer),
    { self.values.into_iter() }

    /// Whether the retained FIFO contents fit within the configured capacity.
    pub closed spec fn well_formed(&self) -> bool {
        buffer_bounded(self.values@, self.capacity as nat)
    }

    /// Expose the retained capacity bound without exposing another queue owner.
    pub proof fn expose_capacity_bound(&self)
        requires self.well_formed(),
        ensures self.values@.len() <= self.capacity,
    { reveal(Buffer::well_formed); }

    /// Construct an empty FIFO with a fixed capacity.
    pub fn new(capacity: usize) -> (buffer: Self)
        ensures
            buffer.well_formed(),
            buffer.capacity == capacity,
            buffer.values@.len() == 0,
    {
        Self { capacity, values: Vec::new() }
    }

    /// Construct an empty FIFO after reserving storage for its admitted capacity.
    ///
    /// Allocation uses the standard allocator. Successful construction avoids storage growth
    /// while pushes stay within the logical bound; allocator behavior is a runtime rely.
    ///
    /// # Errors
    ///
    /// Returns the allocation error if the requested storage cannot be reserved.
    pub fn try_new(capacity: usize) -> (result: Result<Self, std::collections::TryReserveError>)
        ensures
            result is Ok ==> result->Ok_0.well_formed(),
            result is Ok ==> result->Ok_0.capacity == capacity,
            result is Ok ==> result->Ok_0.values@ == Seq::<T>::empty(),
    {
        let mut buffer = Self::new(capacity);
        buffer.values.try_reserve(capacity)?;
        Ok(buffer)
    }

    /// Fixed FIFO capacity.
    pub fn capacity(&self) -> (capacity: usize)
        ensures capacity == self.capacity,
    {
        self.capacity
    }

    /// Number of retained values.
    pub fn len(&self) -> (length: usize)
        ensures length == self.values@.len(),
    {
        self.values.len()
    }

    /// Whether no values are retained.
    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.values@.len() == 0),
    {
        self.values.is_empty()
    }

    /// Whether the FIFO is at capacity.
    pub fn is_full(&self) -> (full: bool)
        ensures full == (self.values@.len() == self.capacity),
    {
        self.values.len() == self.capacity
    }

    /// Sum a pure size projection through the named canonical Reduction.
    /// The Buffer remains immutably borrowed; no total is retained or cached.
    ///
    /// # Errors
    /// Returns overflow exactly when the mathematical total exceeds usize::MAX.
    #[expect(clippy::cast_possible_truncation, reason = "the total > usize::MAX guard rejects every unrepresentable Reduction result")]
    pub fn projected_size<P: BufferSizeProjection<T>>(&self, projection: &P)
        -> (result: Result<usize, BufferSizeError>)
        ensures
            result matches Ok(total) ==> total as int
                == projected_size_to(self.values@, self.values@.len() as int, *projection),
            result is Err <==> projected_size_to(self.values@,
                self.values@.len() as int, *projection) > usize::MAX as int,
            result is Err ==> result == Err(BufferSizeError::Overflow),
    {
        let length = self.values.len();
        let mut reduction = IncrementalReduction::new(length, AdditiveChain);
        let source = BufferSizeInput { buffer: self, projection };
        let folded = reduction.try_fold_projection(&source);
        let ghost end = reduction.processed_spec() as int;
        proof { source.prefix_correct(end); }
        if folded.is_err() {
            proof {
                assert(reduction.result_spec() as int + source.item_spec(end) as int > u64::MAX as int);
                projected_size_monotone(self.values@, end + 1, length as int, *projection);
            }
            return Err(BufferSizeError::Overflow);
        }
        let total = reduction.result();
        if total > usize::MAX as u64 { Err(BufferSizeError::Overflow) }
        else { Ok(total as usize) }
    }

    /// Push one value, returning it unchanged when the FIFO is full.
    ///
    /// # Errors
    ///
    /// Returns the supplied value when the buffer is full.
    pub fn push(&mut self, value: T) -> (result: Result<(), T>)
        requires old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).capacity == old(self).capacity,
            old(self).values@.len() < old(self).capacity ==> result is Ok,
            old(self).values@.len() >= old(self).capacity ==> result == Err(value),
            old(self).values@.len() < old(self).capacity ==>
                final(self).values@ == old(self).values@.push(value),
            old(self).values@.len() >= old(self).capacity ==>
                final(self).values@ == old(self).values@,
    {
        if self.values.len() >= self.capacity { return Err(value); }
        self.values.push(value);
        Ok(())
    }

    /// Remove and return the oldest retained value.
    pub fn pop(&mut self) -> (value: Option<T>)
        requires old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).capacity == old(self).capacity,
            old(self).values@.len() == 0 ==> value is None,
            old(self).values@.len() > 0 ==> value == Some(old(self).values@[0]),
            old(self).values@.len() == 0 ==> final(self).values@ == old(self).values@,
            old(self).values@.len() > 0 ==>
                final(self).values@ == old(self).values@.skip(1),
            all_distinct(old(self).values@) ==> all_distinct(final(self).values@),
    {
        if self.values.is_empty() { None } else { Some(self.values.remove(0)) }
    }
}

/// Query membership in a retained sequence using its verified equality adapter.
#[expect(clippy::indexing_slicing, reason = "the membership loop checks index < values.len() before the read")]
#[expect(clippy::arithmetic_side_effects, reason = "the membership cursor advances only while strictly below values.len()")]
pub fn retained_contains<T: ValueEq + Copy>(values: &Vec<T>, value: T) -> (present: bool)
    ensures present == contains_value(values@, value),
{
        let mut index: usize = 0;
        while index < values.len()
            invariant
                index <= values.len(),
                !contains_up_to(values@, index as int, value),
            decreases values.len() - index,
        {
            if values[index].value_eq(&value) {
                assert(contains_value(values@, value));
                return true;
            }
            proof { lemma_contains_extend(values@, index as int, value); }
            index = index + 1;
        }
        false
    }

impl<T: ValueEq + Copy> Buffer<T> {
    /// Query retained membership through the Buffer owner.
    pub fn contains(&self, value: T) -> (present: bool)
        ensures present == contains_value(self.values@, value),
    {
        retained_contains(&self.values, value)
    }

    /// Append a value only when it is absent and capacity remains.
    pub fn push_unique(&mut self, value: T) -> (accepted: bool)
        requires
            old(self).well_formed(),
            all_distinct(old(self).values@),
        ensures
            final(self).well_formed(),
            all_distinct(final(self).values@),
            final(self).capacity == old(self).capacity,
            accepted == (old(self).values@.len() < old(self).capacity
                && !contains_value(old(self).values@, value)),
            accepted ==> final(self).values@ == old(self).values@.push(value),
            !accepted ==> final(self).values@ == old(self).values@,
    {
        if self.values.len() >= self.capacity || self.contains(value) {
            return false;
        }
        let ghost before = self.values@;
        self.values.push(value);
        proof {
            assert(all_distinct(self.values@)) by {
                assert forall|left: int, right: int|
                    0 <= left < self.values@.len()
                        && 0 <= right < self.values@.len()
                        && left != right
                    implies #[trigger] self.values@[left] != #[trigger] self.values@[right] by {
                    if left < before.len() && right < before.len() {
                    } else if left == before.len() && right < before.len() {
                        assert(self.values@[right] == before[right]);
                        assert(contains_value(before, before[right]));
                    } else if right == before.len() && left < before.len() {
                        assert(self.values@[left] == before[left]);
                        assert(contains_value(before, before[left]));
                    }
                }
            }
        }
        true
    }

    /// Remove one distinct retained value wherever it occurs.
    #[expect(clippy::indexing_slicing, reason = "the removal loop checks index < the unchanged retained length before matching or removing an item")]
    #[expect(clippy::arithmetic_side_effects, reason = "the removal cursor advances only while strictly below retained length")]
    pub fn remove_value(&mut self, value: T) -> (removed: bool)
        requires
            old(self).well_formed(),
            all_distinct(old(self).values@),
        ensures
            final(self).well_formed(),
            all_distinct(final(self).values@),
            final(self).capacity == old(self).capacity,
            removed == contains_value(old(self).values@, value),
            removed ==> exists|index: int|
                0 <= index < old(self).values@.len()
                    && old(self).values@[index] == value
                    && final(self).values@ == old(self).values@.remove(index),
            !removed ==> final(self).values@ == old(self).values@,
            forall|candidate: T| #[trigger] contains_value(final(self).values@, candidate)
                == (contains_value(old(self).values@, candidate) && candidate != value),
    {
        let ghost before = self.values@;
        assert(before == old(self).values@);
        assert(buffer_bounded(before, self.capacity as nat)) by {
            reveal(Buffer::well_formed);
        }
        let mut index: usize = 0;
        while index < self.values.len()
            invariant
                index <= self.values.len(),
                self.values@ == before,
                before == old(self).values@,
                self.capacity == old(self).capacity,
                buffer_bounded(before, self.capacity as nat),
                all_distinct(before),
                forall|prior: int| 0 <= prior < index ==>
                    before[prior] != value,
            decreases self.values.len() - index,
        {
            if self.values[index].value_eq(&value) {
                proof {
                    assert(before[index as int] == value);
                    indexed_value_contained(before, index as int);
                    assert(contains_value(before, value));
                }
                let _removed_value = self.values.remove(index);
                assert(_removed_value == value);
                proof { before.remove_ensures(index as int); }
                assert(self.values@ == before.remove(index as int));
                assert(self.values@.len() < before.len());
                assert(self.well_formed()) by {
                    reveal(Buffer::well_formed);
                    reveal(buffer_bounded);
                }
                assert(all_distinct(self.values@)) by {
                    before.remove_ensures(index as int);
                    assert forall|left: int, right: int|
                        0 <= left < self.values@.len()
                            && 0 <= right < self.values@.len()
                            && left != right
                        implies #[trigger] self.values@[left] != #[trigger] self.values@[right] by {
                        let old_left = if left < index { left } else { left + 1 };
                        let old_right = if right < index { right } else { right + 1 };
                        assert(0 <= old_left < before.len());
                        assert(0 <= old_right < before.len());
                        assert(old_left != old_right);
                        assert(self.values@[left] == before[old_left]);
                        assert(self.values@[right] == before[old_right]);
                    }
                }
                assert forall|candidate: T|
                    #[trigger] contains_value(self.values@, candidate)
                        == (contains_value(before, candidate) && candidate != value) by {
                    contains_remove_distinct(before, index as int, candidate);
                    assert(before[index as int] == value);
                }
                assert(exists|old_index: int|
                    0 <= old_index < before.len()
                        && before[old_index] == value
                        && self.values@ == before.remove(old_index)) by {
                    assert(0 <= index as int);
                    assert((index as int) < before.len());
                }
                return true;
            }
            index = index + 1;
        }
        assert(!contains_value(before, value)) by {
            if contains_value(before, value) {
                let present = choose|present: int|
                    0 <= present < before.len() && before[present] == value;
                assert(false);
            }
        }
        false
    }
}

}

impl_public_error!(BufferSizeError, {
    BufferSizeError::Overflow => "projected Buffer size exceeds usize::MAX",
});

impl<T: core::fmt::Debug> core::fmt::Debug for Buffer<T> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("Buffer")
            .field("capacity", &self.capacity)
            .field("values", &self.values)
            .finish()
    }
}
