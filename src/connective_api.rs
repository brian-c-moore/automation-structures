//! Public runtime forms for the canonical connective roles.
//!
//! Connectives are intentionally smaller than obligation-bearing structures.
//! They carry values or express agreement between adjacent structures without
//! inventing a second domain-specific implementation of the same role.

use vstd::prelude::*;

verus! {

/// An ordered partial result paired with its pending suffix.
pub struct Accumulator<T: Copy> {
    #[allow(dead_code)]
    original: Ghost<Seq<T>>,
    accumulated: Vec<T>,
    pending: Vec<T>,
}

impl<T: Copy> Accumulator<T> {
    pub closed spec fn well_formed(&self) -> bool {
        crate::connectives::accumulator::carries(
            self.original@,
            self.accumulated@,
            self.pending@,
        )
    }

    /// Construct an accumulator with an empty consumed prefix.
    pub fn new(values: Vec<T>) -> (accumulator: Self)
        ensures accumulator.well_formed(),
    {
        let ghost original = values@;
        Self { original: Ghost(original), accumulated: Vec::new(), pending: values }
    }

    /// Number of values already accumulated.
    pub fn accumulated_len(&self) -> usize { self.accumulated.len() }

    /// Number of values still pending.
    pub fn pending_len(&self) -> usize { self.pending.len() }

    /// Whether no values remain pending.
    pub fn is_complete(&self) -> bool { self.pending.is_empty() }

    /// Read one accumulated value by original order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the accumulated index is in bounds")]
    pub fn accumulated(&self, index: usize) -> Option<T> {
        if index < self.accumulated.len() { Some(self.accumulated[index]) } else { None }
    }

    /// Read one pending value by original order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the pending index is in bounds")]
    pub fn pending(&self, index: usize) -> Option<T> {
        if index < self.pending.len() { Some(self.pending[index]) } else { None }
    }

    /// Move the next pending value into the accumulated prefix.
    #[expect(clippy::indexing_slicing, reason = "the nonempty guard proves the pending head exists")]
    pub fn advance(&mut self) -> (value: Option<T>)
        requires old(self).well_formed(),
        ensures final(self).well_formed(),
    {
        if self.pending.is_empty() { return None; }
        let ghost old_accumulated = self.accumulated@;
        let ghost old_pending = self.pending@;
        let value = self.pending[0];
        self.pending.remove(0);
        self.accumulated.push(value);
        proof {
            crate::connectives::accumulator::consume_pending_head(
                old_accumulated,
                old_pending,
            );
            assert(self.accumulated@ =~= old_accumulated.push(old_pending[0]));
            assert(self.pending@ =~= old_pending.skip(1));
        }
        Some(value)
    }
}

/// A bounded FIFO connective.
pub struct Buffer<T> {
    capacity: usize,
    values: Vec<T>,
}

impl<T> Buffer<T> {
    pub closed spec fn well_formed(&self) -> bool {
        crate::connectives::buffer::buffer_bounded(self.values@, self.capacity as nat)
    }

    /// Construct an empty FIFO with a fixed capacity.
    pub fn new(capacity: usize) -> (buffer: Self)
        ensures buffer.well_formed(),
    {
        Self { capacity, values: Vec::new() }
    }

    /// Fixed FIFO capacity.
    pub fn capacity(&self) -> usize { self.capacity }

    /// Number of retained values.
    pub fn len(&self) -> usize { self.values.len() }

    /// Whether no values are retained.
    pub fn is_empty(&self) -> bool { self.values.is_empty() }

    /// Whether the FIFO is at capacity.
    pub fn is_full(&self) -> bool { self.values.len() == self.capacity }

    /// Push one value, returning it unchanged when the FIFO is full.
    pub fn push(&mut self, value: T) -> (result: Result<(), T>)
        requires old(self).well_formed(),
        ensures final(self).well_formed(),
    {
        if self.values.len() >= self.capacity { return Err(value); }
        self.values.push(value);
        Ok(())
    }

    /// Remove and return the oldest retained value.
    pub fn pop(&mut self) -> (value: Option<T>)
        requires old(self).well_formed(),
        ensures final(self).well_formed(),
    {
        if self.values.is_empty() { None } else { Some(self.values.remove(0)) }
    }
}

/// A retained nonnegative occurrence or generation count.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Counter {
    value: u64,
}

impl Counter {
    /// Construct a counter at `value`.
    pub fn new(value: u64) -> (counter: Self) { Self { value } }

    /// Current retained count.
    pub fn value(&self) -> u64 { self.value }

    /// Increment unless the `u64` representation is exhausted.
    #[must_use]
    pub fn try_increment(&mut self) -> (accepted: bool) {
        if self.value == u64::MAX { return false; }
        self.value = self.value + 1;
        true
    }

    /// Decrement when positive.
    #[must_use]
    pub fn try_decrement(&mut self) -> (accepted: bool) {
        if self.value == 0 { return false; }
        self.value = self.value - 1;
        true
    }
}

/// A reusable retained boolean marker.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Marker {
    marked: bool,
}

impl Marker {
    /// Construct a marker with an explicit initial state.
    pub fn new(marked: bool) -> (marker: Self) { Self { marked } }

    /// Whether the marker is set.
    pub fn is_marked(&self) -> bool { self.marked }

    /// Set the marker and return whether its state changed.
    pub fn set(&mut self) -> (changed: bool) {
        let changed = !self.marked;
        self.marked = true;
        changed
    }

    /// Clear the marker and return whether its state changed.
    pub fn clear(&mut self) -> (changed: bool) {
        let changed = self.marked;
        self.marked = false;
        changed
    }
}

/// Test agreement between a projected membership answer and its source.
pub fn projection_consistent(projected: bool, source: bool) -> (consistent: bool)
    ensures consistent == crate::connectives::projection::membership_consistent(projected, source),
{
    projected == source
}

/// Test the canonical strict ordering relation between two positions.
pub fn strictly_before(left: usize, right: usize) -> (ordered: bool) {
    crate::connectives::ordering_pass::is_strictly_before(left, right)
}

}

impl<T: Copy + core::fmt::Debug> core::fmt::Debug for Accumulator<T> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("Accumulator")
            .field("accumulated", &self.accumulated)
            .field("pending", &self.pending)
            .finish()
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for Buffer<T> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("Buffer")
            .field("capacity", &self.capacity)
            .field("values", &self.values)
            .finish()
    }
}
