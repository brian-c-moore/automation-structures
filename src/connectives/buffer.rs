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

mod buffer_storage_seal {
    pub trait Sealed {}
    pub trait Layout<T>: Sealed {}
}

/// Sealed physical sequence representation; logical Buffer actions remain shared.
pub trait BufferLayout<T>: buffer_storage_seal::Layout<T> {
    /// The single retained data container.
    type Values: BufferStorage<T>;
}
/// Original contiguous Vec representation, preserving public slice and Vec APIs.
pub struct ContiguousStorage;
/// Standard deque representation for constant-time FIFO front removal.
pub struct FifoStorage;
impl buffer_storage_seal::Sealed for ContiguousStorage {}
impl buffer_storage_seal::Sealed for FifoStorage {}
impl<T> buffer_storage_seal::Layout<T> for ContiguousStorage {}
impl<T> buffer_storage_seal::Layout<T> for FifoStorage {}
impl<T> BufferLayout<T> for ContiguousStorage { type Values = Vec<T>; }
impl<T> BufferLayout<T> for FifoStorage { type Values = FifoValues<T>; }

/// Mirrored u64 FIFO storage with a contiguous chronological borrow.
/// Growth is lazy and geometric; unrepresentable doubled extents use ordinary Vec storage.
pub struct MirroredU64Storage;
impl buffer_storage_seal::Sealed for MirroredU64Storage {}
impl buffer_storage_seal::Layout<u64> for MirroredU64Storage {}
impl BufferLayout<u64> for MirroredU64Storage { type Values = MirroredU64Values; }

/// Physical layout only: logical order and admission remain owned by Buffer.
pub struct MirroredU64Values {
    values: Vec<u64>,
    head: usize,
    length: usize,
    span: usize,
    linear: bool,
}
impl View for MirroredU64Values {
    type V = Seq<u64>;
    closed spec fn view(&self) -> Seq<u64> {
        self.values@.subrange(self.head as int, self.head as int + self.length as int)
    }
}
impl MirroredU64Values {
    #[verifier::type_invariant]
    closed spec fn valid(&self) -> bool {
        if self.linear {
            self.head == 0 && self.span == 0 && self.length == self.values@.len()
        } else {
            &&& self.span <= usize::MAX / 2
            &&& self.values@.len() == 2 * self.span
            &&& self.length <= self.span
            &&& if self.span == 0 { self.head == 0 } else { self.head < self.span }
            &&& forall|i: int| 0 <= i < self.span
                ==> #[trigger] self.values@[i] == self.values@[i + self.span]
        }
    }

    proof fn lemma_mirrored_append(previous: Seq<u64>, after: Seq<u64>, head: int,
        length: int, span: int, slot: int, value: u64)
        requires 0 < span, 0 <= head < span, 0 <= length < span,
            previous.len() == 2 * span,
            slot == if head + length < span { head + length } else { head + length - span },
            after == previous.update(slot, value).update(slot + span, value),
            forall|i: int| 0 <= i < span
                ==> #[trigger] previous[i] == previous[i + span],
        ensures after.len() == 2 * span,
            forall|i: int| 0 <= i < span ==> #[trigger] after[i] == after[i + span],
            after.subrange(head, head + length + 1)
                == previous.subrange(head, head + length).push(value),
    {
        let tail = head + length;
        assert(0 <= tail < 2 * span);
        assert(0 <= slot < span);
        assert(span <= slot + span < 2 * span);
        assert(after.len() == previous.len());
        assert forall|i: int| 0 <= i < span
            implies #[trigger] after[i] == after[i + span] by {
            if i == slot {
                assert(after[i] == value && after[i + span] == value);
            } else {
                assert(i != slot + span && i + span != slot && i + span != slot + span);
                assert(after[i] == previous[i]);
                assert(after[i + span] == previous[i + span]);
                assert(previous[i] == previous[i + span]);
            }
        }
        assert forall|i: int| 0 <= i < length
            implies #[trigger] after[head + i] == previous[head + i] by {
            if tail < span {
                assert(slot == tail);
                assert(head + i < slot && head + i < slot + span);
            } else {
                assert(slot == tail - span && slot < head);
                assert(slot < head + i && head + i < slot + span);
            }
            assert(head + i != slot && head + i != slot + span);
        }
        if tail < span {
            assert(tail == slot && tail != slot + span);
        } else {
            assert(tail == slot + span);
        }
        assert(after[tail] == value);
        assert(after.subrange(head, head + length + 1)
            =~= previous.subrange(head, head + length).push(value)) by {
            assert forall|i: int| 0 <= i < length + 1 implies
                #[trigger] after.subrange(head, head + length + 1)[i]
                    == previous.subrange(head, head + length).push(value)[i] by {
                if i < length {
                    assert(after[head + i] == previous[head + i]);
                } else {
                    assert(i == length && head + i == tail);
                }
            }
        }
    }

    /// Reserve first when requested, then move the same logical sequence into its new layout.
    #[expect(clippy::indexing_slicing, reason = "the copy cursor is bounded by the old logical view and the new extent")]
    #[expect(clippy::arithmetic_side_effects, reason = "the representation invariant bounds every doubled extent and cursor")]
    fn relayout(&mut self, span: usize, linear: bool, fallible: bool)
        -> (result: Result<(), std::collections::TryReserveError>)
        requires old(self).length <= span, linear || span <= usize::MAX / 2,
        ensures final(self)@ == old(self)@,
            !fallible ==> result is Ok,
            result is Ok ==> final(self).linear == linear,
            result is Ok && !linear ==> final(self).span == span,
    {
        proof { use_type_invariant(&*self); }
        let ghost before = self@;
        let length = self.length;
        let reserve = if linear { span } else { span * 2 };
        let initialized = if linear { length } else { reserve };
        let mut values = Vec::new();
        if fallible { values.try_reserve(reserve)?; }
        let mut i = 0;
        while i < initialized
            invariant i <= initialized, values@.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] values@[j] == 0,
            decreases initialized - i,
        {
            values.push(0);
            i += 1;
        }
        i = 0;
        while i < length
            invariant i <= length, length == self.length, before == self@,
                length <= span, values@.len() == initialized,
                initialized as int == if linear { length as int } else { 2 * span as int },
                self.valid(), linear || span <= usize::MAX / 2,
                forall|j: int| 0 <= j < i ==> #[trigger] values@[j] == before[j],
                !linear ==> (forall|j: int| 0 <= j < span
                    ==> #[trigger] values@[j] == values@[j + span]),
            decreases length - i,
        {
            let value = self.values[self.head + i];
            let ghost previous = values@;
            values.set(i, value);
            if !linear { values.set(i + span, value); }
            assert forall|j: int| 0 <= j < i + 1 implies #[trigger] values@[j] == before[j] by {
                if j < i { assert(values@[j] == previous[j]); }
            }
            if !linear {
                assert forall|j: int| 0 <= j < span
                    implies #[trigger] values@[j] == values@[j + span] by {
                    if j != i { assert(values@[j] == previous[j]); }
                }
            }
            i += 1;
        }
        assert(values@.subrange(0, length as int) =~= before);
        *self = Self { values, head: 0, length, span: if linear { 0 } else { span }, linear };
        Ok(())
    }

    #[expect(clippy::integer_division, reason = "the exact u64 byte-width ceiling keeps both mirrored halves within Vec's isize extent")]
    #[expect(clippy::arithmetic_side_effects, reason = "the guarded geometric span fits within the mirrored byte extent")]
    fn prepare(&mut self, required: usize, fallible: bool)
        -> (result: Result<(), std::collections::TryReserveError>)
        requires !old(self).linear, old(self).length <= required,
        ensures final(self)@ == old(self)@, !fallible ==> result is Ok,
            result is Ok ==> final(self).linear || required <= final(self).span,
    {
        proof { use_type_invariant(&*self); }
        if required <= self.span { return Ok(()); }
        // Vec's extent is bounded in bytes by isize::MAX. Each u64 needs
        // eight bytes in each half; usize::MAX / 32 equals isize::MAX / 16.
        let limit = usize::MAX / 32;
        if required > limit {
            return self.relayout(required, true, fallible);
        }
        let doubled = if self.span <= limit / 2 { self.span * 2 } else { limit };
        let span = if required > doubled { required } else { doubled };
        self.relayout(span, false, fallible)
    }

    /// The mirrored halves make this one borrow contiguous even across physical wrap.
    #[expect(clippy::indexing_slicing, reason = "the private layout bounds the entire chronological slice")]
    #[expect(clippy::arithmetic_side_effects, reason = "head plus retained length lies within the physical extent")]
    pub fn as_slice(&self) -> (values: &[u64]) ensures values@ == self@,
    {
        proof { use_type_invariant(&*self); }
        &self.values[self.head..self.head + self.length]
    }
}
impl buffer_storage_seal::Sealed for MirroredU64Values {}
impl BufferStorage<u64> for MirroredU64Values {
    fn empty() -> (values: Self) {
        Self { values: Vec::new(), head: 0, length: 0, span: 0, linear: false }
    }
    fn len(&self) -> (length: usize) {
        proof { use_type_invariant(&*self); }
        self.length
    }
    #[expect(clippy::indexing_slicing, reason = "the checked logical index lies inside the chronological physical slice")]
    #[expect(clippy::arithmetic_side_effects, reason = "the private extent bounds head plus an admitted logical index")]
    fn value_at(&self, index: usize) -> (value: Option<&u64>) {
        proof { use_type_invariant(&*self); }
        if index < self.length { Some(&self.values[self.head + index]) } else { None }
    }
    #[expect(clippy::arithmetic_side_effects, reason = "the explicit subtraction guard makes the requested logical sum representable")]
    fn try_reserve_values(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
    {
        proof { use_type_invariant(&*self); }
        if self.linear || additional > usize::MAX - self.length {
            // In the overflow case physical len >= logical len, so standard Vec
            // reservation reports the same impossible logical extent.
            // Reservation borrows an owned Vec while this carrier is valid and empty.
            let ghost physical = self.values@;
            let ghost before = self@;
            let mut owned = Self::empty();
            proof { use_type_invariant(&owned); }
            core::mem::swap(self, &mut owned);
            assert(self.valid());
            proof { use_type_invariant(&owned); }
            let MirroredU64Values { values: storage_values, head: storage_head,
                length: storage_length, span: storage_span, linear: storage_linear } = owned;
            let (mut values, head, length, span, linear) =
                (storage_values, storage_head, storage_length, storage_span, storage_linear);
            let result = values.try_reserve(additional);
            assert(values@ == physical);
            *self = Self { values, head, length, span, linear };
            assert(self.values@ == physical);
            assert(self.valid());
            assert(self@ == before);
            return result;
        }
        self.prepare(self.length + additional, true)
    }
    #[expect(clippy::arithmetic_side_effects, reason = "the mirrored invariant and prepared free slot bound all index arithmetic")]
    fn push(&mut self, value: u64) {
        proof { use_type_invariant(&*self); }
        let ghost before = self@;
        assert(before.len() == self.length);
        if !self.linear && self.length == self.span {
            let _prepared = self.prepare(self.length + 1, false);
            assert(_prepared is Ok);
        }
        proof { use_type_invariant(&*self); }
        assert(self@ == before);
        assert(!self.linear ==> self.length < self.span);
        let mut owned = Self::empty();
        proof { use_type_invariant(&owned); }
        core::mem::swap(self, &mut owned);
        assert(self.valid());
        proof { use_type_invariant(&owned); }
        let MirroredU64Values { values: storage_values, head: storage_head,
            length: storage_length, span: storage_span, linear: storage_linear } = owned;
        let (mut values, head, length, span, linear) =
            (storage_values, storage_head, storage_length, storage_span, storage_linear);
        if linear {
            values.push(value);
            let new_length = values.len();
            *self = Self { values, head, length: new_length, span, linear };
            assert(self.valid());
            assert(self.values@.subrange(0, self.length as int) =~= self.values@);
            assert(self@ =~= before.push(value));
            return;
        }
        assert(0 < span && length < span && head < span);
        assert(values@.len() == 2 * span);
        let ghost previous = values@;
        assert(before == previous.subrange(head as int, head as int + length as int));
        let tail = head + length;
        let slot = if tail < span { tail } else { tail - span };
        assert(slot < span && slot + span < values@.len());
        values.set(slot, value);
        values.set(slot + span, value);
        assert(values@ == previous.update(slot as int, value).update(slot as int + span as int, value));
        proof {
            Self::lemma_mirrored_append(previous, values@, head as int, length as int,
                span as int, slot as int, value);
        }
        assert(values@.len() == 2 * span && length + 1 <= span && head < span);
        assert forall|i: int| 0 <= i < span
            implies #[trigger] values@[i] == values@[i + span] by {
            assert(values@[i] == values@[i + span]);
        }
        assert(values@.subrange(head as int, head as int + length as int + 1) == before.push(value));
        *self = Self { values, head, length: length + 1, span, linear };
        assert(self.valid());
        assert(self@ =~= before.push(value));
    }
    #[expect(clippy::indexing_slicing, reason = "nonempty retained length bounds the oldest physical slot")]
    #[expect(clippy::arithmetic_side_effects, reason = "nonempty length and the private span bound decrement and head advance")]
    fn pop_front(&mut self) -> (value: Option<u64>) {
        proof { use_type_invariant(&*self); }
        let ghost before = self@;
        if self.length == 0 { return None; }
        if self.linear {
            let mut owned = Self::empty();
            proof { use_type_invariant(&owned); }
            core::mem::swap(self, &mut owned);
            assert(self.valid());
            proof { use_type_invariant(&owned); }
            let MirroredU64Values { values: storage_values, head: storage_head,
                length: storage_length, span: storage_span, linear: storage_linear } = owned;
            let (mut values, head, _length, span, linear) =
                (storage_values, storage_head, storage_length, storage_span, storage_linear);
            assert(_length > 0 && values@.len() == _length);
            let value = values.remove(0);
            let length = values.len();
            *self = Self { values, head, length, span, linear };
            assert(self.valid());
            assert(self@ =~= before.skip(1));
            return Some(value);
        }
        let value = self.values[self.head];
        let _old_head = self.head;
        self.head = if self.head + 1 < self.span { self.head + 1 } else { 0 };
        self.length -= 1;
        assert forall|i: int| 0 <= i < self.length
            implies #[trigger] self.values@[self.head + i] == before[i + 1] by {
            if _old_head + 1 == self.span {
                assert(self.values@[i] == self.values@[i + self.span]);
            }
        }
        assert(self@ =~= before.skip(1));
        Some(value)
    }
}
impl Buffer<u64, MirroredU64Storage> {
    /// Borrow this owner's exact retained FIFO order without copying or normalization.
    pub fn as_slice(&self) -> (values: &[u64]) ensures values@ == self.values@,
    { self.values.as_slice() }
}

/// One physical deque binding; its logical view is the pinned standard view.
pub struct FifoValues<T> { pub(crate) values: std::collections::VecDeque<T> }
impl<T> View for FifoValues<T> {
    type V = Seq<T>;
    closed spec fn view(&self) -> Seq<T> { self.values@ }
}
impl<T> FifoValues<T> {
    /// Proved physical-view equality within the private representation boundary.
    pub(crate) proof fn expose_view(&self)
        ensures self@ == self.values@,
    {}
}


/// Physical data operations beneath the one Buffer owner; no admission state.
pub trait BufferStorage<T>: buffer_storage_seal::Sealed + View<V = Seq<T>> {
    /// Empty physical sequence.
    fn empty() -> (values: Self) where Self: Sized,
        ensures values@ == Seq::<T>::empty();
    /// Exact retained length.
    fn len(&self) -> (length: usize) ensures length == self@.len();
    /// Empty observation derived from that exact retained length.
    fn is_empty(&self) -> (empty: bool) ensures empty == (self@.len() == 0),
    { self.len() == 0 }
    /// Borrow one exact retained value without changing custody.
    fn value_at(&self, index: usize) -> (value: Option<&T>)
        ensures value is Some <==> index < self@.len(),
            value matches Some(value) ==> *value == self@[index as int];
    /// Fallible physical reservation without logical mutation.
    ///
    /// # Errors
    /// Returns the standard allocation refusal without changing retained values.
    fn try_reserve_values(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
        ensures final(self)@ == old(self)@;
    /// Append one original value; the Buffer supplies its admission guard.
    fn push(&mut self, value: T) ensures final(self)@ == old(self)@.push(value);
    /// Transfer the oldest value, or retain an empty sequence.
    fn pop_front(&mut self) -> (value: Option<T>)
        ensures match value {
            Some(value) => old(self)@.len() > 0 && value == old(self)@[0]
                && final(self)@ == old(self)@.skip(1),
            None => old(self)@.len() == 0 && final(self)@ == old(self)@,
        };
}

/// Copy tuple storage with inline capacity N and fallible Vec growth for wider rows.
pub struct InlineStorage<const N: usize>;
impl<const N: usize> buffer_storage_seal::Sealed for InlineStorage<N> {}
impl<A: Copy, B: Copy, const N: usize> buffer_storage_seal::Layout<(A, B)> for InlineStorage<N> {}
impl<A: Copy, B: Copy, const N: usize> BufferLayout<(A, B)> for InlineStorage<N> {
    type Values = InlinePairValues<A, B, N>;
}

/// The initialized inline prefix has the only private representation invariant.
pub(crate) struct InlinePrefix<T: Copy, const N: usize> {
    inline: [Option<T>; N],
    length: usize,
}
impl<T: Copy, const N: usize> View for InlinePrefix<T, N> {
    type V = Seq<T>;
    closed spec fn view(&self) -> Seq<T> {
        Seq::new(self.length as nat, |i: int| self.inline@[i]->Some_0)
    }
}
impl<T: Copy, const N: usize> InlinePrefix<T, N> {
    #[verifier::type_invariant]
    closed spec fn valid(&self) -> bool {
        &&& self.length <= N
        &&& forall|i: int| 0 <= i < self.length ==> (#[trigger] self.inline@[i]) is Some
    }

    fn empty() -> (values: Self)
        ensures values@ == Seq::<T>::empty(),
    {
        let values = Self { inline: [None; N], length: 0 };
        assert(values.valid());
        assert(values@ =~= Seq::<T>::empty());
        values
    }

    #[expect(clippy::indexing_slicing, reason = "the retained-length guard bounds the borrowed inline slot")]
    fn value_at(&self, index: usize) -> (value: Option<&T>)
        ensures value is Some <==> index < self@.len(),
            value matches Some(value) ==> *value == self@[index as int],
    {
        proof { use_type_invariant(self); }
        if index < self.length {
            match &self.inline[index] {
                Some(value) => Some(value),
                None => { proof { assert(false); } None },
            }
        } else { None }
    }

    #[cold]
    #[inline(never)]
    fn try_heap_reservation(&self, additional: usize)
        -> (result: Result<Vec<T>, std::collections::TryReserveError>)
        ensures result matches Ok(values) ==> values@ == self@,
    {
        proof { use_type_invariant(self); }
        let mut values = Vec::new();
        values.try_reserve(self.length)?;
        self.copy_inline(&mut values);
        values.try_reserve(additional)?;
        Ok(values)
    }

    #[cold]
    #[inline(never)]
    fn heap_with_appended(&self, value: T) -> (values: Vec<T>)
        ensures values@ == self@.push(value),
    {
        let mut values = Vec::new();
        self.copy_inline(&mut values);
        values.push(value);
        values
    }

    #[expect(clippy::indexing_slicing, reason = "the Copy cursor is bounded by the admitted inline prefix")]
    #[expect(clippy::arithmetic_side_effects, reason = "the Copy cursor advances strictly below the inline length")]
    fn copy_inline(&self, values: &mut Vec<T>)
        requires old(values)@.len() == 0,
        ensures final(values)@ == self@,
    {
        proof { use_type_invariant(self); }
        let mut position = 0;
        while position < self.length
            invariant self.valid(), position <= self.length, values@.len() == position,
                forall|i: int| 0 <= i < position ==> #[trigger] values@[i] == self@[i],
            decreases self.length - position,
        {
            let value = match self.inline[position] {
                Some(value) => value,
                None => { proof { assert(false); } return; },
            };
            values.push(value);
            position += 1;
        }
        assert(values@ =~= self@);
    }

    #[expect(clippy::indexing_slicing, reason = "the inline append branch guards its next physical slot")]
    #[expect(clippy::arithmetic_side_effects, reason = "the inline append length is strictly below its usize extent")]
    fn push_inline(&mut self, value: T)
        requires old(self).length < N,
        ensures final(self)@ == old(self)@.push(value),
    {
        proof { use_type_invariant(&*self); }
        let ghost before = self@;
        let position = self.length;
        let ghost previous = self.inline@;
        self.inline[position] = Some(value);
        self.length += 1;
        assert forall|i: int| 0 <= i < self.length implies
            (#[trigger] self.inline@[i]) is Some by {
            if i < position { assert(self.inline@[i] == previous[i]); }
        }
        assert(self.valid());
        assert(self@ =~= before.push(value));
    }

    #[expect(clippy::indexing_slicing, reason = "the nonempty prefix and shift cursor bound each inline read")]
    #[expect(clippy::arithmetic_side_effects, reason = "the nonempty inline prefix bounds shift indices and length decrement")]
    fn pop_front(&mut self) -> (value: Option<T>)
        ensures match value {
            Some(value) => old(self)@.len() > 0 && value == old(self)@[0]
                && final(self)@ == old(self)@.skip(1),
            None => old(self)@.len() == 0 && final(self)@ == old(self)@,
        },
    {
        proof { use_type_invariant(&*self); }
        let ghost before = self@;
        if self.length == 0 { return None; }
        let value = match self.inline[0] {
            Some(value) => value,
            None => { proof { assert(false); } return None; },
        };
        let length = self.length;
        let ghost previous = self.inline@;
        let mut position = 1;
        while position < length
            invariant 1 <= position <= length, length == self.length,
                length <= N, previous.len() == N,
                forall|i: int| 0 <= i < length ==> (#[trigger] self.inline@[i]) is Some,
                forall|i: int| 0 <= i < position - 1 ==> #[trigger] self.inline@[i] == previous[i + 1],
                forall|i: int| position - 1 <= i < N ==> #[trigger] self.inline@[i] == previous[i],
            decreases length - position,
        {
            self.inline[position - 1] = self.inline[position];
            position += 1;
        }
        self.length = length - 1;
        self.inline[length - 1] = None;
        assert(self.valid());
        assert(self@ =~= before.skip(1));
        Some(value)
    }
}

/// Exactly one active physical sequence, with arbitrary-width fallible Vec growth.
pub(crate) enum InlineValues<T: Copy, const N: usize> {
    Inline(InlinePrefix<T, N>),
    Heap(Vec<T>),
}
impl<T: Copy, const N: usize> View for InlineValues<T, N> {
    type V = Seq<T>;
    closed spec fn view(&self) -> Seq<T> {
        match self {
            Self::Inline(prefix) => prefix@,
            Self::Heap(values) => values@,
        }
    }
}
impl<T: Copy, const N: usize> buffer_storage_seal::Sealed for InlineValues<T, N> {}
impl<T: Copy, const N: usize> BufferStorage<T> for InlineValues<T, N> {
    fn empty() -> (values: Self) {
        let values = Self::Inline(InlinePrefix::empty());
        assert(values@ =~= Seq::<T>::empty());
        values
    }
    fn len(&self) -> (length: usize) {
        match self {
            Self::Inline(prefix) => {
                proof { use_type_invariant(prefix); }
                prefix.length
            },
            Self::Heap(values) => values.len(),
        }
    }
    fn value_at(&self, index: usize) -> (value: Option<&T>) {
        match self {
            Self::Inline(prefix) => prefix.value_at(index),
            Self::Heap(values) => values.value_at(index),
        }
    }
    #[expect(clippy::arithmetic_side_effects, reason = "the inline prefix invariant bounds length by the physical extent")]
    #[inline(always)]
    fn try_reserve_values(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
    {
        let ghost before = self@;
        let result = match self {
            Self::Heap(values) => values.try_reserve(additional),
            Self::Inline(prefix) => {
                proof { use_type_invariant(&*prefix); }
                if additional <= N - prefix.length { return Ok(()); }
                let values = prefix.try_heap_reservation(additional)?;
                *self = Self::Heap(values);
                Ok(())
            },
        };
        assert(self@ == before);
        result
    }
    fn push(&mut self, value: T) {
        let ghost before = self@;
        match self {
            Self::Heap(values) => values.push(value),
            Self::Inline(prefix) => {
                proof { use_type_invariant(&*prefix); }
                if prefix.length < N {
                    prefix.push_inline(value);
                } else {
                    let values = prefix.heap_with_appended(value);
                    *self = Self::Heap(values);
                }
            },
        }
        assert(self@ =~= before.push(value));
    }
    fn pop_front(&mut self) -> (value: Option<T>) {
        let ghost before = self@;
        let value = match self {
            Self::Inline(prefix) => prefix.pop_front(),
            Self::Heap(values) => values.pop_front(),
        };
        assert(match value {
            Some(value) => before.len() > 0 && value == before[0] && self@ == before.skip(1),
            None => before.len() == 0 && self@ == before,
        });
        value
    }
}

// A named Copy carrier avoids the pinned checker's missing tuple Copy impl.
#[derive(Copy)]
struct InlinePair<A: Copy, B: Copy> { pair: (A, B) }
impl<A: Copy, B: Copy> Clone for InlinePair<A, B> {
    fn clone(&self) -> (result: Self)
        ensures result == *self,
    { *self }
}

/// Tuple carrier for InlineStorage's single retained sequence.
pub struct InlinePairValues<A: Copy, B: Copy, const N: usize> {
    inner: InlineValues<InlinePair<A, B>, N>,
}
impl<A: Copy, B: Copy, const N: usize> View for InlinePairValues<A, B, N> {
    type V = Seq<(A, B)>;
    closed spec fn view(&self) -> Seq<(A, B)> {
        self.inner@.map(|_i: int, value: InlinePair<A, B>| value.pair)
    }
}
impl<A: Copy, B: Copy, const N: usize> buffer_storage_seal::Sealed for InlinePairValues<A, B, N> {}
impl<A: Copy, B: Copy, const N: usize> BufferStorage<(A, B)> for InlinePairValues<A, B, N> {
    fn empty() -> (values: Self) {
        let values = Self { inner: InlineValues::empty() };
        assert(values@ =~= Seq::<(A, B)>::empty());
        values
    }
    fn len(&self) -> (length: usize) { self.inner.len() }
    fn value_at(&self, index: usize) -> (value: Option<&(A, B)>) {
        match self.inner.value_at(index) {
            Some(value) => Some(&value.pair),
            None => None,
        }
    }
    #[inline(always)]
    fn try_reserve_values(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
    {
        let ghost before = self@;
        let result = self.inner.try_reserve_values(additional);
        assert(self@ == before);
        result
    }
    fn push(&mut self, value: (A, B)) {
        let ghost before = self@;
        self.inner.push(InlinePair { pair: value });
        assert(self@ =~= before.push(value));
    }
    fn pop_front(&mut self) -> (value: Option<(A, B)>) {
        let ghost before = self@;
        match self.inner.pop_front() {
            Some(value) => {
                assert(self@ =~= before.skip(1));
                Some(value.pair)
            },
            None => None,
        }
    }
}

impl<T> buffer_storage_seal::Sealed for Vec<T> {}
impl<T> BufferStorage<T> for Vec<T> {
    fn empty() -> (values: Self) { Vec::new() }
    fn len(&self) -> (length: usize) { self.len() }
    #[expect(clippy::indexing_slicing, reason = "the storage guard checks the retained position before borrowing its value")]
    fn value_at(&self, index: usize) -> (value: Option<&T>) {
        if index < self.len() { Some(&self[index]) } else { None }
    }
    fn try_reserve_values(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
    { self.try_reserve(additional) }
    fn push(&mut self, value: T) { self.push(value); }
    fn pop_front(&mut self) -> (value: Option<T>) {
        if self.is_empty() { None } else { Some(self.remove(0)) }
    }
}

impl<T> buffer_storage_seal::Sealed for FifoValues<T> {}
impl<T> BufferStorage<T> for FifoValues<T> {
    fn empty() -> (values: Self) { Self { values: std::collections::VecDeque::new() } }
    fn len(&self) -> (length: usize) { self.values.len() }
    #[expect(clippy::indexing_slicing, reason = "the storage guard checks the retained deque position before borrowing its value")]
    fn value_at(&self, index: usize) -> (value: Option<&T>) {
        if index < self.values.len() { Some(&self.values[index]) } else { None }
    }
    /// Standard allocator premise absent from pinned vstd: reservation preserves
    /// the exact logical sequence and returns the standard allocation refusal.
    #[verifier::external_body]
    fn try_reserve_values(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
    { self.values.try_reserve(additional) }
    fn push(&mut self, value: T) { self.values.push_back(value); }
    fn pop_front(&mut self) -> (value: Option<T>) { self.values.pop_front() }
}

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
pub struct Buffer<T, S: BufferLayout<T> = ContiguousStorage> {
    /// Maximum number of retained values.
    pub capacity: usize,
    /// Retained values in FIFO order.
    pub values: S::Values,
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

}

impl<T, S: BufferLayout<T>> Buffer<T, S> {
    /// Whether the retained FIFO contents fit within the configured capacity.
    pub closed spec fn well_formed(&self) -> bool {
        buffer_bounded(self.values@, self.capacity as nat)
    }

    /// Expose the retained capacity bound without exposing another queue owner.
    pub proof fn expose_capacity_bound(&self)
        requires self.well_formed(),
        ensures self.values@.len() <= self.capacity,
    { reveal(Buffer::well_formed); }

    /// Establish the existing Buffer invariant from its exact retained length bound.
    /// This proof bridge grants no mutation, storage reservation or FIFO transition.
    pub proof fn establish_capacity_bound(&self)
        requires self.values@.len() <= self.capacity,
        ensures self.well_formed(),
    { reveal(Buffer::well_formed); }

    /// Construct the selected physical layout under the same logical bound.
    pub fn with_storage(capacity: usize) -> (buffer: Self)
        ensures buffer.well_formed(), buffer.capacity == capacity,
            buffer.values@ == Seq::<T>::empty(),
    { Self { capacity, values: S::Values::empty() } }

    /// Reserve the selected layout before any Buffer publication.
    ///
    /// # Errors
    /// Returns the standard allocator refusal with no Buffer publication.
    #[inline(always)]
    pub fn try_with_storage(capacity: usize)
        -> (result: Result<Self, std::collections::TryReserveError>)
        ensures result is Ok ==> result->Ok_0.well_formed(),
            result is Ok ==> result->Ok_0.capacity == capacity,
            result is Ok ==> result->Ok_0.values@ == Seq::<T>::empty(),
    {
        let mut buffer = Self::with_storage(capacity);
        buffer.values.try_reserve_values(capacity)?;
        Ok(buffer)
    }
}

impl<T> Buffer<T> {
    /// Construct an empty FIFO with a fixed capacity.
    pub fn new(capacity: usize) -> (buffer: Self)
        ensures
            buffer.well_formed(),
            buffer.capacity == capacity,
            buffer.values@.len() == 0,
    {
        Self::with_storage(capacity)
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
        Self::try_with_storage(capacity)
    }

}
impl<T, S: BufferLayout<T>> Buffer<T, S> {
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

}
impl<T> Buffer<T> {

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

}
impl<T, S: BufferLayout<T>> Buffer<T, S> {

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
        self.values.pop_front()
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
