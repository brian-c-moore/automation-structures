//! Checked public entry points for reusable connective roles.
//!
//! Connectives retain or relate the state passed between structures. Their
//! checked facades keep the state carrier private, so ordinary Rust code
//! cannot bypass a connective's invariant.

use vstd::prelude::*;

use crate::connectives::accumulator::Accumulator as AccumulatorCarrier;
use crate::connectives::buffer::Buffer as BufferCarrier;
use crate::connectives::counter::Counter as CounterCarrier;
use crate::connectives::marker::Marker as MarkerCarrier;
use crate::value_eq::ValueEq;

verus! {

/// An ordered partial result paired with its pending suffix.
///
/// `Accumulator` preserves the original order while values move from the
/// pending suffix into the accumulated prefix.
///
/// # Examples
///
/// ```rust
/// use automation_structures::Accumulator;
///
/// let mut values = Accumulator::new(vec![10, 20]);
/// assert_eq!(values.advance(), Some(10));
/// assert_eq!(values.accumulated_iter().collect::<Vec<_>>(), vec![&10]);
/// assert_eq!(values.pending_iter().collect::<Vec<_>>(), vec![&20]);
/// ```
pub struct Accumulator<T: Copy> {
    inner: AccumulatorCarrier<T>,
}

impl<T: Copy> Accumulator<T> {
    /// Whether the owner reconstructs one complete ordered sequence.
    pub closed spec fn well_formed(&self) -> bool {
        self.inner.well_formed()
    }

    /// Whether no values remain in the pending suffix.
    pub closed spec fn complete(&self) -> bool {
        self.inner.pending@.len() == 0
    }

    /// Total logical length of the accumulated prefix and pending suffix.
    pub closed spec fn total_len(&self) -> nat {
        self.inner.accumulated@.len() + self.inner.pending@.len()
    }

    /// Construct an accumulator with an empty consumed prefix.
    pub fn new(values: Vec<T>) -> (accumulator: Self)
        ensures accumulator.well_formed(),
    {
        Self { inner: AccumulatorCarrier::new(values) }
    }

    /// Construct an accumulator whose supplied prefix is already incorporated.
    pub fn from_accumulated(values: Vec<T>) -> (accumulator: Self)
        ensures
            accumulator.well_formed(),
            accumulator.complete(),
    {
        Self { inner: AccumulatorCarrier::from_accumulated(values) }
    }

    /// Total number of values across both segments when representable by `usize`.
    pub fn checked_len(&self) -> Option<usize> {
        self.inner
            .accumulated_len()
            .checked_add(self.inner.pending_len())
    }

    /// Whether both segments are empty.
    pub fn is_empty(&self) -> bool {
        self.inner.accumulated_len() == 0 && self.inner.pending_len() == 0
    }

    /// Number of values already accumulated.
    pub fn accumulated_len(&self) -> usize { self.inner.accumulated_len() }

    /// Number of values still pending.
    pub fn pending_len(&self) -> usize { self.inner.pending_len() }

    /// Whether no values remain pending.
    pub fn is_complete(&self) -> (complete: bool)
        ensures complete == self.complete(),
    {
        self.inner.is_complete()
    }

    /// Read one accumulated value by original order.
    pub fn accumulated(&self, index: usize) -> Option<T> { self.inner.accumulated(index) }

    /// Read one pending value by original order.
    pub fn pending(&self, index: usize) -> Option<T> { self.inner.pending(index) }

    /// Move the next pending value into the accumulated prefix.
    pub fn advance(&mut self) -> (value: Option<T>)
        requires old(self).well_formed(),
        ensures final(self).well_formed(),
    {
        self.inner.advance()
    }

    /// Append one value when the pending suffix is empty.
    ///
    /// # Errors
    ///
    /// Returns the supplied value unchanged while pending values remain.
    pub fn try_append(&mut self, value: T) -> (result: Result<(), T>)
        requires old(self).well_formed(),
        ensures final(self).well_formed(),
    {
        if !self.inner.is_complete() { return Err(value); }
        self.inner.append(value);
        Ok(())
    }
}

/// A bounded first-in, first-out connective.
///
/// Capacity and contents remain private; mutation is possible only through
/// the checked FIFO operations.
///
/// # Examples
///
/// ```rust
/// use automation_structures::Buffer;
///
/// let mut buffer = Buffer::new(2);
/// assert_eq!(buffer.push("first"), Ok(()));
/// assert_eq!(buffer.push("second"), Ok(()));
/// assert_eq!(buffer.push("full"), Err("full"));
/// assert_eq!(buffer.pop(), Some("first"));
/// ```
pub struct Buffer<T> {
    inner: BufferCarrier<T>,
}

impl<T> Buffer<T> {
    /// Logical FIFO contents used by proof consumers.
    pub closed spec fn retained(&self) -> Seq<T> {
        self.inner.values@
    }

    /// Logical capacity used by proof consumers.
    pub closed spec fn admitted_capacity(&self) -> nat {
        self.inner.capacity as nat
    }

    /// Whether a logical value occurs in the retained FIFO contents.
    pub closed spec fn contains_retained(&self, value: T) -> bool {
        crate::connectives::buffer::contains_value(self.inner.values@, value)
    }

    /// Whether the retained values fit within the configured capacity.
    pub closed spec fn well_formed(&self) -> bool {
        self.inner.well_formed()
    }

    /// Whether every retained value occurs at most once.
    pub closed spec fn distinct(&self) -> bool {
        crate::connectives::buffer::all_distinct(self.inner.values@)
    }

    /// Construct an empty FIFO with a fixed capacity.
    pub fn new(capacity: usize) -> (buffer: Self)
        ensures
            buffer.well_formed(),
            buffer.distinct(),
            buffer.admitted_capacity() == capacity as nat,
            buffer.retained() == Seq::<T>::empty(),
            forall|value: T| !buffer.contains_retained(value),
    {
        Self { inner: BufferCarrier::new(capacity) }
    }

    /// Fixed FIFO capacity.
    pub fn capacity(&self) -> (capacity: usize)
        ensures capacity as nat == self.admitted_capacity(),
    {
        self.inner.capacity()
    }

    /// Number of retained values.
    pub fn len(&self) -> (length: usize)
        ensures length as nat == self.retained().len(),
    {
        self.inner.len()
    }

    /// Whether no values are retained.
    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.retained().len() == 0),
    {
        self.inner.is_empty()
    }

    /// Whether the FIFO is at capacity.
    pub fn is_full(&self) -> (full: bool)
        ensures full == (self.retained().len() == self.admitted_capacity()),
    {
        self.inner.is_full()
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
            final(self).admitted_capacity() == old(self).admitted_capacity(),
            old(self).retained().len() < old(self).admitted_capacity() ==>
                final(self).retained() == old(self).retained().push(value),
            old(self).retained().len() >= old(self).admitted_capacity() ==>
                final(self).retained() == old(self).retained(),
    {
        self.inner.push(value)
    }

    /// Remove and return the oldest retained value.
    pub fn pop(&mut self) -> (value: Option<T>)
        requires old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).admitted_capacity() == old(self).admitted_capacity(),
            old(self).retained().len() == 0 ==>
                final(self).retained() == old(self).retained(),
            old(self).retained().len() > 0 ==>
                final(self).retained() == old(self).retained().skip(1),
            old(self).distinct() ==> final(self).distinct(),
    {
        self.inner.pop()
    }
}

impl<T: ValueEq + Copy> Buffer<T> {
    /// Query retained membership using the shared equality adapter.
    pub fn contains(&self, value: T) -> (present: bool)
        ensures present == self.contains_retained(value),
    {
        self.inner.contains(value)
    }

    /// Append a value only when it is absent and capacity remains.
    #[must_use]
    pub fn push_unique(&mut self, value: T) -> (accepted: bool)
        requires old(self).well_formed(), old(self).distinct(),
        ensures
            final(self).well_formed(),
            final(self).distinct(),
            final(self).admitted_capacity() == old(self).admitted_capacity(),
            accepted == (old(self).retained().len() < old(self).admitted_capacity()
                && !old(self).contains_retained(value)),
            accepted ==> final(self).retained() == old(self).retained().push(value),
            !accepted ==> final(self).retained() == old(self).retained(),
    {
        self.inner.push_unique(value)
    }

    /// Remove one distinct retained value wherever it occurs.
    #[must_use]
    pub fn remove(&mut self, value: T) -> (removed: bool)
        requires old(self).well_formed(), old(self).distinct(),
        ensures
            final(self).well_formed(),
            final(self).distinct(),
            final(self).admitted_capacity() == old(self).admitted_capacity(),
            removed == old(self).contains_retained(value),
            forall|candidate: T| #[trigger] final(self).contains_retained(candidate)
                == (old(self).contains_retained(candidate) && candidate != value),
    {
        self.inner.remove_value(value)
    }
}

/// A retained nonnegative occurrence or generation count.
///
/// # Examples
///
/// ```rust
/// use automation_structures::Counter;
///
/// let mut count = Counter::default();
/// assert!(count.try_increment());
/// assert_eq!(count.value(), 1);
/// ```
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Counter {
    inner: CounterCarrier,
}

impl Counter {
    /// Construct a counter at `value`.
    pub fn new(value: u64) -> Self { Self { inner: CounterCarrier::new(value) } }

    /// Current retained count.
    pub fn value(&self) -> u64 { self.inner.value() }

    /// Increment unless the `u64` representation is exhausted.
    #[must_use]
    pub fn try_increment(&mut self) -> bool { self.inner.try_increment() }

    /// Decrement when positive.
    #[must_use]
    pub fn try_decrement(&mut self) -> bool { self.inner.try_decrement() }
}

/// A reusable retained boolean marker.
///
/// # Examples
///
/// ```rust
/// use automation_structures::Marker;
///
/// let mut marker = Marker::default();
/// assert!(marker.set());
/// assert!(marker.is_marked());
/// assert!(marker.clear());
/// ```
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Marker {
    inner: MarkerCarrier,
}

impl Marker {
    /// Construct a marker with an explicit initial state.
    pub fn new(marked: bool) -> Self { Self { inner: MarkerCarrier::new(marked) } }

    /// Whether the marker is set.
    pub fn is_marked(&self) -> bool { self.inner.is_marked() }

    /// Set the marker and return whether its state changed.
    #[must_use]
    pub fn set(&mut self) -> bool { self.inner.set() }

    /// Clear the marker and return whether its state changed.
    #[must_use]
    pub fn clear(&mut self) -> bool { self.inner.clear() }
}

/// Test agreement between a projected membership answer and its source.
///
/// # Examples
///
/// ```rust
/// use automation_structures::projection_consistent;
///
/// assert!(projection_consistent(true, true));
/// assert!(!projection_consistent(true, false));
/// ```
pub fn projection_consistent(projected: bool, source: bool) -> (consistent: bool)
    ensures consistent == crate::connectives::projection::membership_consistent(projected, source),
{
    projected == source
}

/// Test the strict ordering relation between two positions.
///
/// # Examples
///
/// ```rust
/// use automation_structures::strictly_before;
///
/// assert!(strictly_before(1, 2));
/// assert!(!strictly_before(2, 2));
/// ```
pub fn strictly_before(left: usize, right: usize) -> (ordered: bool) {
    crate::connectives::ordering_pass::is_strictly_before(left, right)
}

}

impl<T: Copy> Accumulator<T> {
    /// Borrow the accumulated prefix in original order.
    pub fn accumulated_iter(&self) -> impl ExactSizeIterator<Item = &T> {
        self.inner.accumulated.iter()
    }

    /// Borrow the pending suffix in original order.
    pub fn pending_iter(&self) -> impl ExactSizeIterator<Item = &T> {
        self.inner.pending.iter()
    }

    /// Borrow the complete sequence in original order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.inner
            .accumulated
            .iter()
            .chain(self.inner.pending.iter())
    }
}

impl<T: Copy> Default for Accumulator<T> {
    fn default() -> Self {
        Self::new(Vec::new())
    }
}

impl<T: Copy + core::fmt::Debug> core::fmt::Debug for Accumulator<T> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("Accumulator")
            .field("accumulated", &self.inner.accumulated)
            .field("pending", &self.inner.pending)
            .finish()
    }
}

impl<T> Buffer<T> {
    /// Borrow a retained value by FIFO position.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.inner.values.get(index)
    }

    /// Borrow the retained FIFO contents.
    pub fn as_slice(&self) -> &[T] {
        self.inner.values.as_slice()
    }

    /// Borrow the retained values in FIFO order.
    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.inner.values.iter()
    }
}

impl<T> Default for Buffer<T> {
    fn default() -> Self {
        Self::new(0)
    }
}

impl<T: Clone> Clone for Buffer<T> {
    fn clone(&self) -> Self {
        Self {
            inner: BufferCarrier {
                capacity: self.inner.capacity,
                values: self.inner.values.clone(),
            },
        }
    }
}

impl<T: PartialEq> PartialEq for Buffer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner.capacity == other.inner.capacity && self.inner.values == other.inner.values
    }
}

impl<T: Eq> Eq for Buffer<T> {}

impl<T: core::fmt::Debug> core::fmt::Debug for Buffer<T> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("Buffer")
            .field("capacity", &self.inner.capacity)
            .field("values", &self.inner.values)
            .finish()
    }
}

impl<T> AsRef<[T]> for Buffer<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<'a, T> IntoIterator for &'a Buffer<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> IntoIterator for Buffer<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.values.into_iter()
    }
}

impl From<u64> for Counter {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

impl From<Counter> for u64 {
    fn from(counter: Counter) -> Self {
        counter.value()
    }
}

impl From<bool> for Marker {
    fn from(marked: bool) -> Self {
        Self::new(marked)
    }
}

impl From<Marker> for bool {
    fn from(marker: Marker) -> Self {
        marker.is_marked()
    }
}
