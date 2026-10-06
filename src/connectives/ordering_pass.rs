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


/// Pure comparison data for an immutable finite row universe.
pub trait PositionOrder: Sized {
    /// Number of admitted rows.
    spec fn domain_len(&self) -> nat;
    /// The domain's total preorder; equal keys may occur at different row positions.
    spec fn key_le(&self, left: usize, right: usize) -> bool;
    /// Establish the comparator's domain law before arrangement.
    proof fn establish(&self)
        ensures
            forall|a: usize| a < self.domain_len() ==> #[trigger] self.key_le(a, a),
            forall|a: usize, b: usize| a < self.domain_len() && b < self.domain_len()
                ==> (#[trigger] self.key_le(a, b) || self.key_le(b, a)),
            forall|a: usize, b: usize, c: usize|
                a < self.domain_len() && b < self.domain_len() && c < self.domain_len()
                && #[trigger] self.key_le(a, b) && #[trigger] self.key_le(b, c) ==> self.key_le(a, c);
    /// Executable admitted length.
    fn len(&self) -> (n: usize) ensures n == self.domain_len();
    /// Whether the admitted domain is empty.
    fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.domain_len() == 0),
    { self.len() == 0 }
    /// Three-way domain comparison, without retaining or advancing automation state.
    fn compare(&self, left: usize, right: usize) -> (ordering: i8)
        requires left < self.domain_len(), right < self.domain_len(),
        ensures -1 <= ordering <= 1,
            (ordering <= 0) == self.key_le(left, right),
            (ordering >= 0) == self.key_le(right, left);
}

/// The admitted comparator is reflexive, total and transitive.
pub open spec fn total_preorder<C: PositionOrder>(order: &C) -> bool {
    &&& forall|a: usize| a < order.domain_len() ==> #[trigger] order.key_le(a, a)
    &&& forall|a: usize, b: usize| a < order.domain_len() && b < order.domain_len()
        ==> (#[trigger] order.key_le(a, b) || order.key_le(b, a))
    &&& forall|a: usize, b: usize, c: usize|
        a < order.domain_len() && b < order.domain_len() && c < order.domain_len()
        && #[trigger] order.key_le(a, b) && #[trigger] order.key_le(b, c) ==> order.key_le(a, c)
}

/// Canonical deterministic ties preserve original input position.
pub open spec fn position_le<C: PositionOrder>(order: &C, left: usize, right: usize) -> bool {
    order.key_le(left, right) && (order.key_le(right, left) ==> left <= right)
}

/// Exact finite coverage, with no missing, foreign or duplicate positions.
pub open spec fn permutation(positions: Seq<usize>, count: nat) -> bool {
    &&& positions.len() == count
    &&& forall|i: int| 0 <= i < positions.len() ==> #[trigger] positions[i] < count
    &&& forall|i: int, j: int| 0 <= i < positions.len() && 0 <= j < positions.len() && i != j
        ==> #[trigger] positions[i] != #[trigger] positions[j]
    &&& forall|p: usize| p < count ==> #[trigger] positions.contains(p)
}

/// Every earlier output position precedes every later one under the admitted order.
pub open spec fn arranged<C: PositionOrder>(positions: Seq<usize>, order: &C) -> bool {
    forall|i: int, j: int| 0 <= i < j < positions.len()
        ==> position_le(order, #[trigger] positions[i], #[trigger] positions[j])
}

/// A failed arrangement exposes no output sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArrangementError {
    /// The requested prefix is outside the comparator's immutable row universe.
    OutsideDomain,
    /// Standard-library reservation refused the index allocation.
    Allocation,
}

/// Domain data for signed numeric rows, with explicit direction and null placement.
pub struct SignedRowOrder<'a> {
    /// Immutable row values in original input order.
    pub values: &'a Vec<crate::primitives::audit_sink::NullableSigned>,
    /// Whether larger nonnull keys appear first.
    pub descending: bool,
    /// Whether nulls appear before nonnull keys.
    pub nulls_first: bool,
}

impl PositionOrder for SignedRowOrder<'_> {
    open spec fn domain_len(&self) -> nat { self.values@.len() }
    open spec fn key_le(&self, left: usize, right: usize) -> bool {
        use crate::primitives::audit_sink::NullableSigned::{Missing, Value};
        match (self.values@[left as int], self.values@[right as int]) {
            (Missing, Missing) => true,
            (Missing, Value(_)) => self.nulls_first,
            (Value(_), Missing) => !self.nulls_first,
            (Value(a), Value(b)) => if self.descending { a >= b } else { a <= b },
        }
    }
    proof fn establish(&self) {
        assert forall|a: usize| a < self.domain_len() implies #[trigger] self.key_le(a, a) by {}
        assert forall|a: usize, b: usize| a < self.domain_len() && b < self.domain_len()
            implies #[trigger] self.key_le(a, b) || self.key_le(b, a) by {}
        assert forall|a: usize, b: usize, c: usize|
            a < self.domain_len() && b < self.domain_len() && c < self.domain_len()
            && #[trigger] self.key_le(a, b) && #[trigger] self.key_le(b, c)
            implies self.key_le(a, c) by {}
    }
    fn len(&self) -> (n: usize) { self.values.len() }
    #[expect(clippy::indexing_slicing, reason = "PositionOrder requires both positions below the immutable row-value length")]
    fn compare(&self, left: usize, right: usize) -> (ordering: i8) {
        use crate::primitives::audit_sink::NullableSigned::{Missing, Value};
        match (self.values[left], self.values[right]) {
            (Missing, Missing) => 0,
            (Missing, Value(_)) => if self.nulls_first { -1 } else { 1 },
            (Value(_), Missing) => if self.nulls_first { 1 } else { -1 },
            (Value(a), Value(b)) => {
                if a == b { 0 }
                else if self.descending { if a > b { -1 } else { 1 } }
                else { if a < b { -1 } else { 1 } }
            }
        }
    }
}

/// Library premise: extending an empty Vec by the identity range stores exactly that range.
/// The caller has already attempted fallible reservation; no iterator or sort is reimplemented.
#[verifier::external_body]
fn extend_identity(positions: &mut Vec<usize>, count: usize)
    requires old(positions)@.len() == 0,
    ensures final(positions)@ == Seq::new(count as nat, |i: int| i as usize),
{ positions.extend(0..count); }

/// Standard sorting-library premise, parameterized by the admitted pure comparator.
/// `sort_unstable_by` does not allocate; original positions resolve equal-key ties.
#[verifier::external_body]
fn arrange_library<C: PositionOrder>(positions: &mut Vec<usize>, count: usize, order: &C)
    requires permutation(old(positions)@, count as nat), count <= order.domain_len(), total_preorder(order),
    ensures permutation(final(positions)@, count as nat), arranged(final(positions)@, order),
{
    let _ = count;
    positions.sort_unstable_by(|left, right| {
        let comparison = order.compare(*left, *right);
        if comparison < 0 { std::cmp::Ordering::Less }
        else if comparison > 0 { std::cmp::Ordering::Greater }
        else { left.cmp(right) }
    });
}

/// Standard identity positions satisfy exact finite coverage.
pub proof fn identity_permutation(count: usize)
    ensures permutation(Seq::new(count as nat, |i: int| i as usize), count as nat),
{
    let positions = Seq::new(count as nat, |i: int| i as usize);
    assert forall|p: usize| p < count implies #[trigger] positions.contains(p) by {
        assert(positions[p as int] == p);
    }
}

/// Construct the finite arrangement that a downstream Cursor will actually consume.
///
/// # Errors
/// Refuses an out-of-domain row count before allocation, or a failed index reservation.
pub fn try_arrange_indices<C: PositionOrder>(row_count: usize, order: &C)
    -> (result: Result<Vec<usize>, ArrangementError>)
    ensures
        result is Ok ==> permutation(result.unwrap()@, row_count as nat)
            && arranged(result.unwrap()@, order) && row_count <= order.domain_len(),
        (result matches Err(ArrangementError::OutsideDomain)) == (row_count > order.domain_len()),
{
    proof { order.establish(); }
    if row_count > order.len() { return Err(ArrangementError::OutsideDomain); }
    let mut positions = Vec::new();
    if positions.try_reserve(row_count).is_err() { return Err(ArrangementError::Allocation); }
    extend_identity(&mut positions, row_count);
    proof { identity_permutation(row_count); }
    arrange_library(&mut positions, row_count, order);
    Ok(positions)
}

/// The forward and inverse arrays describe the same exact finite permutation.
pub open spec fn inverse_permutation(positions: Seq<usize>, inverse: Seq<usize>) -> bool {
    &&& permutation(positions, positions.len())
    &&& inverse.len() == positions.len()
    &&& forall|rank: int| 0 <= rank < positions.len() ==>
        #[trigger] inverse[positions[rank] as int] == rank
    &&& forall|original: int| 0 <= original < inverse.len() ==>
        #[trigger] inverse[original] < positions.len()
            && positions[inverse[original] as int] == original
}

/// Immutable forward and inverse views of one canonical finite arrangement.
/// The two arrays are jointly owned certificates of the same permutation.
/// Neither view permits mutation or a replacement ordering authority.
///
/// ```rust
/// use automation_structures::connectives::ordering_pass::{IndexArrangement, SignedRowOrder};
/// use automation_structures::NullableSigned::Value;
/// let values = vec![Value(9), Value(2), Value(9)];
/// let order = SignedRowOrder { values: &values, descending: false, nulls_first: false };
/// let arranged = IndexArrangement::try_new(values.len(), &order)?;
/// assert_eq!(arranged.positions(), &[1, 0, 2]);
/// assert_eq!(arranged.rank_of(0), Some(1));
/// # Ok::<(), automation_structures::ArrangementError>(())
/// ```
/// An immutable view cannot replace an arranged position:
/// ```compile_fail
/// use automation_structures::connectives::ordering_pass::{IndexArrangement, SignedRowOrder};
/// let values = vec![automation_structures::NullableSigned::Value(1)];
/// let order = SignedRowOrder { values: &values, descending: false, nulls_first: false };
/// let arranged = IndexArrangement::try_new(1, &order)?;
/// arranged.positions()[0] = 9;
/// # Ok::<(), automation_structures::ArrangementError>(())
/// ```
pub struct IndexArrangement {
    positions: Vec<usize>,
    inverse: Vec<usize>,
}

impl IndexArrangement {
    /// Exact immutable finite universe and its two mutually inverse views.
    pub closed spec fn inv(&self) -> bool {
        inverse_permutation(self.positions@, self.inverse@)
    }
    /// Original input position at every arranged rank.
    pub closed spec fn positions_spec(&self) -> Seq<usize> { self.positions@ }
    /// Arranged rank at every original input position.
    pub closed spec fn inverse_spec(&self) -> Seq<usize> { self.inverse@ }
    /// Expose the same owner's joint permutation facts to verified compositions.
    pub proof fn expose_certificate(&self)
        requires self.inv(),
        ensures inverse_permutation(self.positions_spec(), self.inverse_spec()),
    {}

    /// Reuse the existing finite arrangement and construct its inverse once.
    /// Cursor owns visitation; no sorting algorithm or caller scan is added.
    ///
    /// # Errors
    /// Refuses an out-of-domain count or either fallible array reservation.
    #[expect(clippy::indexing_slicing, reason = "the arrangement Cursor and admitted permutation certificate bound each original-position read")]
    #[expect(clippy::arithmetic_side_effects, reason = "the arrangement Cursor advances only while strictly below the fixed count")]
    pub fn try_new<C: PositionOrder>(count: usize, order: &C)
        -> (result: Result<Self, ArrangementError>)
        ensures result is Ok ==> result.unwrap().inv()
            && inverse_permutation(result.unwrap().positions_spec(), result.unwrap().inverse_spec())
            && result.unwrap().positions_spec().len() == count
            && arranged(result.unwrap().positions_spec(), order)
            && count <= order.domain_len(),
            (result matches Err(ArrangementError::OutsideDomain)) == (count > order.domain_len()),
    {
        let positions = match try_arrange_indices(count, order) {
            Ok(positions) => positions,
            Err(reason) => { return Err(reason); },
        };
        let mut inverse = Vec::new();
        if inverse.try_reserve(count).is_err() { return Err(ArrangementError::Allocation); }
        extend_identity(&mut inverse, count);
        let mut cursor = crate::connectives::cursor::Cursor::new(0);
        while cursor.position < count
            invariant cursor.position <= count,
                count <= order.domain_len(),
                permutation(positions@, count as nat), arranged(positions@, order),
                inverse@.len() == count,
                forall|rank: int| 0 <= rank < cursor.position ==>
                    #[trigger] inverse@[positions@[rank] as int] == rank,
            decreases count - cursor.position,
        {
            let rank = cursor.position;
            let original = positions[rank];
            inverse.set(original, rank);
            cursor.advance_to(rank + 1);
        }
        assert forall|original: int| 0 <= original < inverse@.len() implies
            #[trigger] inverse@[original] < positions@.len()
                && positions@[inverse@[original] as int] == original by {
            assert(positions@.contains(original as usize));
            let rank = choose|rank: int| 0 <= rank < positions@.len()
                && positions@[rank] == original;
            assert(inverse@[original] == rank);
        }
        Ok(Self { positions, inverse })
    }

    /// Borrow the arranged original positions without a mutable array escape.
    pub fn positions(&self) -> (positions: &[usize])
        requires self.inv(), ensures positions@ == self.positions_spec(),
    { self.positions.as_slice() }
    /// Borrow the inverse certificate without a mutable array escape.
    pub fn inverse(&self) -> (inverse: &[usize])
        requires self.inv(), ensures inverse@ == self.inverse_spec(),
    { self.inverse.as_slice() }
    /// Number of admitted positions.
    pub fn len(&self) -> (length: usize)
        requires self.inv(), ensures length == self.positions_spec().len(),
    { self.positions.len() }
    /// Whether the admitted universe is empty.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.inv(), ensures empty == (self.positions_spec().len() == 0),
    { self.positions.is_empty() }
    /// Observe an original position at one rank; foreign ranks return None.
    #[expect(clippy::indexing_slicing, reason = "the runtime rank guard checks the immutable positions length")]
    pub fn original_at(&self, rank: usize) -> (original: Option<usize>)
        requires self.inv(), ensures original ==
            if rank < self.positions_spec().len() { Some(self.positions_spec()[rank as int]) }
            else { None },
    { if rank < self.positions.len() { Some(self.positions[rank]) } else { None } }
    /// Observe an arranged rank for an original position; foreign inputs return None.
    #[expect(clippy::indexing_slicing, reason = "the runtime original-position guard checks the immutable inverse length")]
    pub fn rank_of(&self, original: usize) -> (rank: Option<usize>)
        requires self.inv(), ensures rank ==
            if original < self.inverse_spec().len() { Some(self.inverse_spec()[original as int]) }
            else { None },
    { if original < self.inverse.len() { Some(self.inverse[original]) } else { None } }
}

}

impl core::fmt::Debug for IndexArrangement {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("IndexArrangement")
            .field("positions", &self.positions())
            .finish()
    }
}
