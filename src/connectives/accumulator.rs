//! Accumulator connective relations for partial results carried between steps.

use vstd::prelude::*;

verus! {

/// The accumulated prefix and pending suffix reconstruct the complete value sequence.
pub open spec fn carries<T>(
    complete: Seq<T>,
    accumulated: Seq<T>,
    pending: Seq<T>,
) -> bool {
    complete == accumulated.add(pending)
}

/// Segments that do not reconstruct the complete sequence are not a valid accumulation.
pub proof fn mismatched_partition_rejected<T>(
    complete: Seq<T>,
    accumulated: Seq<T>,
    pending: Seq<T>,
)
    requires complete != accumulated.add(pending),
    ensures !carries(complete, accumulated, pending),
{
}

/// One step appends a value to the carried partial result.
pub open spec fn append<T>(before: Seq<T>, after: Seq<T>, value: T) -> bool {
    after == before.push(value)
}

/// An unselected step preserves the carried partial result.
pub open spec fn stutter<T>(before: Seq<T>, after: Seq<T>) -> bool {
    after == before
}

/// Appending to a pending suffix preserves its accumulated prefix.
pub proof fn append_pending<T>(prefix: Seq<T>, pending: Seq<T>, value: T)
    ensures
        prefix.add(pending).push(value) == prefix.add(pending.push(value)),
{
    Seq::push_distributes_over_add(prefix, pending, value);
}

/// Moving one pending head into the accumulator preserves the reconstructed complete sequence.
pub proof fn consume_pending_head<T>(accumulated: Seq<T>, pending: Seq<T>)
    requires pending.len() > 0,
    ensures
        accumulated.add(pending)
            == accumulated.push(pending[0]).add(pending.skip(1)),
{
    assert(pending =~= seq![pending[0]].add(pending.skip(1)));
    assert(accumulated.push(pending[0]) =~= accumulated.add(seq![pending[0]]));
    assert(accumulated.add(pending)
        =~= accumulated.push(pending[0]).add(pending.skip(1)));
}

/// Moving one head between adjacent pending segments preserves the reconstructed sequence.
pub proof fn move_pending_head<T>(
    prefix: Seq<T>,
    destination: Seq<T>,
    source: Seq<T>,
)
    requires source.len() > 0,
    ensures
        prefix.add(destination).add(source)
            == prefix.add(destination.push(source[0])).add(source.skip(1)),
{
    assert(source =~= seq![source[0]].add(source.skip(1)));
    assert(destination.push(source[0]) =~= destination.add(seq![source[0]]));
    assert(prefix.add(destination).add(source)
        =~= prefix.add(destination.push(source[0])).add(source.skip(1)));
}

/// Moving one head between adjacent pending segments preserves any pending prefix and suffix.
pub proof fn move_pending_head_with_suffix<T>(
    prefix: Seq<T>,
    destination: Seq<T>,
    source: Seq<T>,
    suffix: Seq<T>,
)
    requires source.len() > 0,
    ensures
        prefix.add(destination).add(source).add(suffix)
            == prefix
                .add(destination.push(source[0]))
                .add(source.skip(1))
                .add(suffix),
{
    move_pending_head(prefix, destination, source);
}

/// Folding the first pending segment head preserves any later pending suffix.
pub proof fn consume_pending_head_with_suffix<T>(
    accumulated: Seq<T>,
    source: Seq<T>,
    suffix: Seq<T>,
)
    requires source.len() > 0,
    ensures
        accumulated.add(source.add(suffix))
            == accumulated.push(source[0]).add(source.skip(1).add(suffix)),
{
    consume_pending_head(accumulated, source);
    assert(accumulated.add(source.add(suffix))
        =~= accumulated.add(source).add(suffix));
    assert(accumulated.push(source[0]).add(source.skip(1).add(suffix))
        =~= accumulated.push(source[0]).add(source.skip(1)).add(suffix));
}

/// Skipping a present head commutes with appending a later pending suffix.
pub proof fn skip_pending_head_with_suffix<T>(source: Seq<T>, suffix: Seq<T>)
    requires source.len() > 0,
    ensures
        source.add(suffix).skip(1) == source.skip(1).add(suffix),
{
    assert(source.add(suffix).skip(1) =~= source.skip(1).add(suffix));
}

/// An ordered partial result paired with its pending suffix.
pub struct Accumulator<T: Copy> {
    /// Ghost reconstruction of the complete ordered value sequence.
    pub original: Ghost<Seq<T>>,
    /// Values already incorporated into the partial result.
    pub accumulated: Vec<T>,
    /// Values not yet incorporated into the partial result.
    pub pending: Vec<T>,
}

impl<T: Copy> Accumulator<T> {
    /// The accumulated prefix and pending suffix reconstruct the complete sequence.
    pub closed spec fn well_formed(&self) -> bool {
        carries(self.original@, self.accumulated@, self.pending@)
    }

    /// Construct an accumulator with an empty consumed prefix.
    pub fn new(values: Vec<T>) -> (accumulator: Self)
        ensures
            accumulator.well_formed(),
            accumulator.original@ == values@,
            accumulator.accumulated@.len() == 0,
            accumulator.pending@ == values@,
    {
        let ghost original = values@;
        Self { original: Ghost(original), accumulated: Vec::new(), pending: values }
    }

    /// Construct an accumulator whose supplied prefix is already incorporated.
    pub fn from_accumulated(values: Vec<T>) -> (accumulator: Self)
        ensures
            accumulator.well_formed(),
            accumulator.original@ == values@,
            accumulator.accumulated@ == values@,
            accumulator.pending@.len() == 0,
    {
        let ghost original = values@;
        Self { original: Ghost(original), accumulated: values, pending: Vec::new() }
    }

    /// Number of values already accumulated.
    pub fn accumulated_len(&self) -> (length: usize)
        ensures length == self.accumulated@.len(),
    {
        self.accumulated.len()
    }

    /// Number of values in the accumulated prefix.
    pub fn len(&self) -> (length: usize)
        ensures length == self.accumulated@.len(),
    {
        self.accumulated.len()
    }

    /// Whether the accumulated prefix is empty.
    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.accumulated@.len() == 0),
    {
        self.accumulated.is_empty()
    }

    /// Number of values still pending.
    pub fn pending_len(&self) -> (length: usize)
        ensures length == self.pending@.len(),
    {
        self.pending.len()
    }

    /// Whether no values remain pending.
    pub fn is_complete(&self) -> (complete: bool)
        ensures complete == (self.pending@.len() == 0),
    {
        self.pending.is_empty()
    }

    /// Read one accumulated value by original order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the accumulated index is in bounds")]
    pub fn accumulated(&self, index: usize) -> (value: Option<T>)
        ensures value == if index < self.accumulated@.len() {
            Some(self.accumulated@[index as int])
        } else {
            None
        },
    {
        if index < self.accumulated.len() { Some(self.accumulated[index]) } else { None }
    }

    /// Read one value from the accumulated prefix by order.
    pub fn value(&self, index: usize) -> (value: Option<T>)
        ensures value == if index < self.accumulated@.len() {
            Some(self.accumulated@[index as int])
        } else {
            None
        },
    {
        self.accumulated(index)
    }

    /// Read one pending value by original order.
    #[expect(clippy::indexing_slicing, reason = "the branch proves the pending index is in bounds")]
    pub fn pending(&self, index: usize) -> (value: Option<T>)
        ensures value == if index < self.pending@.len() {
            Some(self.pending@[index as int])
        } else {
            None
        },
    {
        if index < self.pending.len() { Some(self.pending[index]) } else { None }
    }

    /// Move the next pending value into the accumulated prefix.
    #[expect(clippy::indexing_slicing, reason = "the nonempty guard proves the pending head exists")]
    pub fn advance(&mut self) -> (value: Option<T>)
        requires old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).original@ == old(self).original@,
            value == if old(self).pending@.len() > 0 {
                Some(old(self).pending@[0])
            } else {
                None
            },
            final(self).accumulated@ == if old(self).pending@.len() > 0 {
                old(self).accumulated@.push(old(self).pending@[0])
            } else {
                old(self).accumulated@
            },
            final(self).pending@ == if old(self).pending@.len() > 0 {
                old(self).pending@.skip(1)
            } else {
                old(self).pending@
            },
    {
        if self.pending.is_empty() { return None; }
        let ghost old_accumulated = self.accumulated@;
        let ghost old_pending = self.pending@;
        let value = self.pending[0];
        self.pending.remove(0);
        self.accumulated.push(value);
        proof {
            consume_pending_head(old_accumulated, old_pending);
            assert(self.accumulated@ =~= old_accumulated.push(old_pending[0]));
            assert(self.pending@ =~= old_pending.skip(1));
        }
        Some(value)
    }

    /// Append one value after a completed accumulated prefix.
    pub fn append(&mut self, value: T)
        requires
            old(self).well_formed(),
            old(self).pending@.len() == 0,
        ensures
            final(self).well_formed(),
            final(self).original@ == old(self).original@.push(value),
            final(self).accumulated@ == old(self).accumulated@.push(value),
            final(self).pending@ == old(self).pending@,
    {
        let ghost old_original = self.original@;
        let ghost old_accumulated = self.accumulated@;
        let ghost old_pending = self.pending@;
        self.accumulated.push(value);
        self.original = Ghost(old_original.push(value));
        proof {
            assert(old_pending =~= Seq::<T>::empty());
            assert(old_original == old_accumulated.add(old_pending));
            assert(old_original =~= old_accumulated);
            assert(self.pending@ =~= Seq::<T>::empty());
            assert(self.original@ == self.accumulated@.add(self.pending@));
        }
    }
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
