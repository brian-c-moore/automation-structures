//! Complete minimum selection with an inspectable arrangement and canonical winner.
//!
//! OrderingPass retains the stable arrangement and inverse. Fixed equivalence-class
//! ranks supply domain scores to the existing Hard owner. Cursor and Buffer retain
//! visitation and all tied results. This is a composition of the existing structures.

use crate::connectives::buffer::Buffer;
use crate::connectives::cursor::Cursor;
use crate::connectives::ordering_pass::{ArrangementError, IndexArrangement, PositionOrder};
use crate::primitives::competitive_selection as selection;
use vstd::prelude::*;

verus! {

/// First rank of this key's contiguous equivalence class in the frozen arrangement.
pub open spec fn class_start<C: PositionOrder>(positions: Seq<usize>, order: C, rank: int) -> int
    decreases rank,
{
    if rank <= 0 || rank >= positions.len() { 0 }
    else if order.key_le(positions[rank], positions[rank - 1])
        && order.key_le(positions[rank - 1], positions[rank]) {
        class_start(positions, order, rank - 1)
    } else { rank }
}

/// Fixed numeric quality of the full arrangement; ties share one positive score.
pub open spec fn arranged_score<C: PositionOrder>(positions: Seq<usize>, order: C, rank: int) -> nat {
    if 0 <= rank < positions.len() { (positions.len() as int - class_start(positions, order, rank)) as nat }
    else { 0 }
}

proof fn class_start_bounds<C: PositionOrder>(positions: Seq<usize>, order: C, rank: int)
    requires 0 <= rank < positions.len(),
    ensures 0 <= class_start(positions, order, rank) <= rank,
        1 <= arranged_score(positions, order, rank) <= positions.len(),
    decreases rank,
{
    if rank > 0 { class_start_bounds(positions, order, rank - 1); }
}

proof fn class_start_is_minimum<C: PositionOrder>(positions: Seq<usize>, order: C, rank: int)
    requires 0 <= rank < positions.len(),
        crate::connectives::ordering_pass::permutation(positions, order.domain_len()),
        crate::connectives::ordering_pass::arranged(positions, &order),
        crate::connectives::ordering_pass::total_preorder(&order),
    ensures (arranged_score(positions, order, rank) == positions.len())
        == (order.key_le(positions[rank], positions[0]) && order.key_le(positions[0], positions[rank])),
    decreases rank,
{
    class_start_bounds(positions, order, rank);
    if rank > 0 {
        class_start_is_minimum(positions, order, rank - 1);
        let item = positions[rank];
        let previous = positions[rank - 1];
        let first = positions[0];
        if rank > 1 { assert(order.key_le(first, previous)); }
        else { assert(first == previous); }
        assert(order.key_le(previous, item));
        if order.key_le(item, previous) && order.key_le(previous, item) {
            assert(order.key_le(item, first) == order.key_le(previous, first));
        } else if order.key_le(item, first) && order.key_le(first, item) {
            assert(order.key_le(item, previous));
            assert(false);
        }
    }
}

/// Equivalence classes have increasing starts, with equality exactly for tied keys.
proof fn class_start_order<C: PositionOrder>(positions: Seq<usize>, order: C, left: int, right: int)
    requires 0 <= left <= right < positions.len(),
        crate::connectives::ordering_pass::permutation(positions, order.domain_len()),
        crate::connectives::ordering_pass::arranged(positions, &order),
        crate::connectives::ordering_pass::total_preorder(&order),
    ensures class_start(positions, order, left) <= class_start(positions, order, right),
        (class_start(positions, order, left) == class_start(positions, order, right))
            == order.key_le(positions[right], positions[left]),
    decreases right - left,
{
    class_start_bounds(positions, order, left);
    class_start_bounds(positions, order, right);
    if left < right {
        class_start_order(positions, order, left, right - 1);
        let item = positions[right];
        let previous = positions[right - 1];
        let first = positions[left];
        assert(order.key_le(first, previous));
        assert(order.key_le(previous, item));
        if order.key_le(item, previous) {
            assert(order.key_le(item, first) == order.key_le(previous, first));
        } else {
            assert(class_start(positions, order, right) == right);
            if order.key_le(item, first) { assert(order.key_le(item, previous)); }
            assert(!order.key_le(item, first));
        }
    } else { assert(order.key_le(positions[left], positions[left])); }
}

/// A sorted suffix after the first nonminimum cannot add another minimum.
proof fn minimum_prefix_stops<C: PositionOrder>(positions: Seq<usize>, order: C, start: int, end: int)
    requires 0 <= start < end <= positions.len(),
        crate::connectives::ordering_pass::permutation(positions, order.domain_len()),
        crate::connectives::ordering_pass::arranged(positions, &order),
        crate::connectives::ordering_pass::total_preorder(&order),
        !(order.key_le(positions[start], positions[0])
            && order.key_le(positions[0], positions[start])),
    ensures selection::minimum_prefix(positions, order, end)
        == selection::minimum_prefix(positions, order, start),
    decreases end - start,
{
    assert(positions[0] < order.domain_len());
    if start == 0 {
        assert(order.key_le(positions[0], positions[0]));
        assert(false);
    }
    assert(0 < start);
    assert(crate::connectives::ordering_pass::position_le(&order, positions[0], positions[start]));
    assert(order.key_le(positions[0], positions[start]));
    assert(!order.key_le(positions[start], positions[0]));
    let last = end - 1;
    assert(positions[start] < order.domain_len());
    assert(positions[last] < order.domain_len());
    if last > start {
        assert(crate::connectives::ordering_pass::position_le(&order, positions[start], positions[last]));
        assert(order.key_le(positions[start], positions[last]));
        if order.key_le(positions[last], positions[0]) {
            assert(order.key_le(positions[start], positions[0]));
            assert(false);
        }
    } else { assert(last == start); }
    assert(!order.key_le(positions[last], positions[0]));
    if end > start + 1 {
        minimum_prefix_stops(positions, order, start, end - 1);
    } else { assert(end - 1 == start); }
    reveal_with_fuel(selection::minimum_prefix, 1);
    assert(selection::minimum_prefix(positions, order, end)
        == selection::minimum_prefix(positions, order, end - 1));
}

/// Immutable all-minimum capture composed from the original canonical owners.
///
/// The full arrangement certificate requires O(n log n) comparisons in the
/// general comparison model. Score configuration, Hard evaluation and result
/// retention add O(n) work. Each comparison has its domain's own cost.
pub struct MinimumSelection<C: PositionOrder> {
    order: C,
    arrangement: IndexArrangement,
    hard: selection::CompetitiveSelectionHard,
    selected: Buffer<usize>,
}

impl<C: PositionOrder> MinimumSelection<C> {
    /// Immutable original comparator/context.
    pub closed spec fn order_spec(&self) -> C { self.order }
    /// Complete stable arrangement retained by OrderingPass.
    pub closed spec fn arranged_spec(&self) -> Seq<usize> { self.arrangement.positions_spec() }
    /// Original-position inverse retained by the same arrangement owner.
    pub closed spec fn inverse_spec(&self) -> Seq<usize> { self.arrangement.inverse_spec() }
    /// Exact Buffer-owned complete tied result.
    pub closed spec fn selected_spec(&self) -> Seq<usize> { self.selected.values@ }
    /// The retained Hard winner; an empty domain has no winner.
    pub closed spec fn winner_spec(&self) -> Option<usize> { self.hard.allocation }
    /// The sole Hard-owned fixed domain scores.
    pub closed spec fn scores_spec(&self) -> Seq<u64> { self.hard.scores@ }
    /// Arrangement, winner and complete stable tie coverage at the composition boundary.
    pub closed spec fn inv(&self) -> bool {
        &&& self.arrangement.inv()
        &&& crate::connectives::ordering_pass::inverse_permutation(self.arranged_spec(), self.inverse_spec())
        &&& self.arranged_spec().len() == self.order.domain_len()
        &&& crate::connectives::ordering_pass::arranged(self.arranged_spec(), &self.order)
        &&& crate::connectives::ordering_pass::total_preorder(&self.order)
        &&& self.hard.inv() && self.hard.scores@.len() == self.order.domain_len()
        &&& forall|rank: int| 0 <= rank < self.arranged_spec().len() ==>
            #[trigger] self.hard.scores@[self.arranged_spec()[rank] as int] as nat
                == arranged_score(self.arranged_spec(), self.order, rank)
        &&& (self.hard.allocation is Some) == (self.order.domain_len() > 0)
        &&& self.hard.allocation matches Some(winner) ==> winner < self.order.domain_len()
            && self.order.key_le(winner, self.arranged_spec()[0])
            && self.order.key_le(self.arranged_spec()[0], winner)
        &&& self.selected.well_formed() && self.selected.capacity == self.order.domain_len()
        &&& self.selected_spec() == selection::minimum_prefix(self.arranged_spec(), self.order,
            self.arranged_spec().len() as int)
    }

    /// Capture the full arrangement, select its canonical winner and retain every tie.
    ///
    /// # Errors
    /// Return the original context if arrangement, score or result storage is unavailable.
    #[expect(clippy::indexing_slicing, reason = "the arrangement permutation and Cursor bounds admit every original-position and neighboring-rank read")]
    #[expect(clippy::arithmetic_side_effects, reason = "class starts and visitation Cursors remain below the fixed admitted arrangement length")]
    pub fn try_new(order: C) -> (result: Result<Self, (ArrangementError, C)>)
        ensures result matches Ok(owner) ==> owner.inv() && owner.order_spec() == order,
            result matches Err((_, returned)) ==> returned == order,
    {
        let count = order.len();
        proof { order.establish(); }
        let arrangement = match IndexArrangement::try_new(count, &order) {
            Ok(arrangement) => arrangement,
            Err(reason) => return Err((reason, order)),
        };
        let mut hard = match selection::CompetitiveSelectionHard::try_new(count) {
            Ok(hard) => hard,
            Err(_) => return Err((ArrangementError::Allocation, order)),
        };
        let mut selected = match Buffer::try_new(count) {
            Ok(selected) => selected,
            Err(_) => return Err((ArrangementError::Allocation, order)),
        };
        proof { arrangement.expose_certificate(); }
        let mut cursor = Cursor::new(0);
        let mut class = Cursor::new(0);
        while cursor.position < count
            invariant cursor.position <= count, count == order.domain_len(),
                arrangement.inv(),
                crate::connectives::ordering_pass::inverse_permutation(arrangement.positions_spec(), arrangement.inverse_spec()),
                crate::connectives::ordering_pass::permutation(arrangement.positions_spec(), count as nat),
                arrangement.positions_spec().len() == count,
                crate::connectives::ordering_pass::arranged(arrangement.positions_spec(), &order),
                crate::connectives::ordering_pass::total_preorder(&order),
                hard.inv(), hard.allocation is None, hard.scores@.len() == count,
                class.position <= cursor.position,
                class.position as int == if cursor.position == 0 { 0 }
                    else { class_start(arrangement.positions_spec(), order, cursor.position as int - 1) },
                forall|rank: int| 0 <= rank < cursor.position ==>
                    #[trigger] hard.scores@[arrangement.positions_spec()[rank] as int] as nat
                        == arranged_score(arrangement.positions_spec(), order, rank),
                forall|rank: int| cursor.position <= rank < count ==>
                    #[trigger] hard.scores@[arrangement.positions_spec()[rank] as int] == 0,
            decreases count - cursor.position,
        {
            let positions = arrangement.positions();
            let rank = cursor.position;
            let item = positions[rank];
            if rank > 0 && order.compare(positions[rank - 1], item) != 0 {
                class.advance_to(rank);
            }
            proof {
                class_start_bounds(positions@, order, rank as int);
                assert(class.position as int == class_start(positions@, order, rank as int));
                assert(count as nat <= u64::MAX as nat);
            }
            let score = (count - class.position) as u64;
            let ghost before_scores = hard.scores@;
            hard.update_score(item, score);
            assert forall|other: int| 0 <= other < count && other != rank as int implies
                #[trigger] positions@[other] != item by {
                assert(arrangement.inverse_spec()[positions@[other] as int] == other);
                assert(arrangement.inverse_spec()[item as int] == rank as int);
            }
            assert forall|other: int| 0 <= other <= rank implies
                #[trigger] hard.scores@[positions@[other] as int] as nat == arranged_score(positions@, order, other) by {
                if other < rank { assert(hard.scores@[positions@[other] as int] == before_scores[positions@[other] as int]); }
            }
            cursor.advance_to(rank + 1);
        }
        if count > 0 { hard.evaluate(); }
        if let Some(winner) = hard.allocation {
            proof {
                let positions = arrangement.positions_spec();
                let rank = arrangement.inverse_spec()[winner as int] as int;
                assert(0 <= rank < count && positions[rank] == winner);
                class_start_bounds(positions, order, rank);
                class_start_is_minimum(positions, order, rank);
                assert(hard.scores@[positions[0] as int] as nat == count as nat);
                assert(hard.scores@[winner as int] >= hard.scores@[positions[0] as int]);
                assert(arranged_score(positions, order, rank) == count as nat);
                assert(order.key_le(winner, positions[0]) && order.key_le(positions[0], winner));
            }
            let mut cursor = Cursor::new(0);
            while cursor.position < count
                invariant cursor.position <= count, count == order.domain_len(),
                    arrangement.inv(),
                    crate::connectives::ordering_pass::inverse_permutation(arrangement.positions_spec(), arrangement.inverse_spec()),
                    arrangement.positions_spec().len() == count,
                    crate::connectives::ordering_pass::arranged(arrangement.positions_spec(), &order),
                    crate::connectives::ordering_pass::total_preorder(&order),
                    hard.inv(), hard.allocation == Some(winner), hard.scores@.len() == count,
                    winner < count, count > 0,
                    order.key_le(winner, arrangement.positions_spec()[0]),
                    order.key_le(arrangement.positions_spec()[0], winner),
                    forall|rank: int| 0 <= rank < count ==>
                        #[trigger] hard.scores@[arrangement.positions_spec()[rank] as int] as nat
                            == arranged_score(arrangement.positions_spec(), order, rank),
                    selected.well_formed(), selected.capacity == count,
                    selected.values@.len() <= cursor.position,
                    selected.values@ == selection::minimum_prefix(arrangement.positions_spec(), order, cursor.position as int),
                decreases count - cursor.position,
            {
                let positions = arrangement.positions();
                let item = positions[cursor.position];
                let tied = order.compare(item, winner) == 0;
                proof {
                    assert((order.key_le(item, winner) && order.key_le(winner, item))
                        == (order.key_le(item, positions[0]) && order.key_le(positions[0], item)));
                }
                if tied {
                    let _pushed = selected.push(item);
                    assert(_pushed is Ok);
                    cursor.advance_to(cursor.position + 1);
                } else {
                    proof {
                        minimum_prefix_stops(positions@, order, cursor.position as int, count as int);
                        assert(selected.values@ == selection::minimum_prefix(positions@, order, count as int));
                    }
                    cursor.advance_to(count);
                }
            }
        } else {
            assert(count == 0);
        }
        Ok(Self { order, arrangement, hard, selected })
    }

    /// Export the retained full arrangement and its inverse without another sorting owner.
    pub proof fn expose_arrangement(&self)
        requires self.inv(),
        ensures crate::connectives::ordering_pass::inverse_permutation(self.arranged_spec(), self.inverse_spec()),
            crate::connectives::ordering_pass::arranged(self.arranged_spec(), &self.order_spec()),
            self.arranged_spec().len() == self.order_spec().domain_len(),
            self.selected_spec() == selection::minimum_prefix(self.arranged_spec(), self.order_spec(), self.arranged_spec().len() as int),
    {}

    /// Export exact minimum membership through the canonical arrangement certificate.
    pub proof fn expose_minima(&self)
        requires self.inv(),
        ensures forall|item: usize| self.selected_spec().contains(item) <==>
            (item < self.order_spec().domain_len()
                && forall|other: usize| other < self.order_spec().domain_len()
                    ==> #[trigger] self.order_spec().key_le(item, other)),
    {
        self.arrangement.expose_certificate();
        let positions = self.arranged_spec();
        assert forall|item: usize| self.selected_spec().contains(item) <==>
            (item < self.order.domain_len()
                && forall|other: usize| other < self.order.domain_len()
                    ==> #[trigger] self.order.key_le(item, other)) by {
            selection::minimum_prefix_membership(positions, self.order, positions.len() as int, item);
            if self.selected_spec().contains(item) {
                let rank = choose|rank: int| 0 <= rank < positions.len() && #[trigger] positions[rank] == item
                    && self.order.key_le(item, positions[0]) && self.order.key_le(positions[0], item);
                assert forall|other: usize| other < self.order.domain_len() implies
                    #[trigger] self.order.key_le(item, other) by {
                    assert(positions.contains(other));
                    let index = choose|index: int| 0 <= index < positions.len() && positions[index] == other;
                    if index > 0 { assert(self.order.key_le(positions[0], other)); }
                    else { assert(positions[0] == other); }
                }
            }
            if item < self.order.domain_len()
                && forall|other: usize| other < self.order.domain_len() ==> #[trigger] self.order.key_le(item, other) {
                assert(positions.contains(item));
                let rank = choose|rank: int| 0 <= rank < positions.len() && positions[rank] == item;
                if rank > 0 { assert(self.order.key_le(positions[0], item)); }
                assert(self.order.key_le(item, positions[0]));
                assert(self.selected_spec().contains(item));
            }
        }
    }

    /// Export the retained score representation's exact domain-order correspondence.
    pub proof fn expose_scores(&self)
        requires self.inv(),
        ensures self.scores_spec().len() == self.order_spec().domain_len(),
            forall|left: usize, right: usize| left < self.order_spec().domain_len()
                && right < self.order_spec().domain_len() ==>
                (#[trigger] self.order_spec().key_le(left, right)
                    == (self.scores_spec()[left as int] >= self.scores_spec()[right as int])),
    {
        self.arrangement.expose_certificate();
        assert forall|left: usize, right: usize| left < self.order.domain_len()
            && right < self.order.domain_len() implies
            (#[trigger] self.order.key_le(left, right)
                == (self.scores_spec()[left as int] >= self.scores_spec()[right as int])) by {
            let positions = self.arranged_spec();
            let left_rank = self.inverse_spec()[left as int] as int;
            let right_rank = self.inverse_spec()[right as int] as int;
            assert(positions[left_rank] == left && positions[right_rank] == right);
            class_start_bounds(positions, self.order, left_rank);
            class_start_bounds(positions, self.order, right_rank);
            assert(self.scores_spec()[left as int] as nat == arranged_score(positions, self.order, left_rank));
            assert(self.scores_spec()[right as int] as nat == arranged_score(positions, self.order, right_rank));
            if left_rank <= right_rank {
                class_start_order(positions, self.order, left_rank, right_rank);
                assert(self.order.key_le(left, right));
            } else {
                class_start_order(positions, self.order, right_rank, left_rank);
            }
        }
    }

    /// Borrow all selected original positions in stable authored order.
    pub fn selected(&self) -> (positions: &[usize])
        requires self.inv(), ensures positions@ == self.selected_spec(),
    { self.selected.values.as_slice() }
    /// Read the Buffer-owned selected count.
    pub fn len(&self) -> (length: usize)
        requires self.inv(), ensures length == self.selected_spec().len(),
    { self.selected.len() }
    /// Whether the admitted domain has no minimum.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.inv(), ensures empty == (self.selected_spec().len() == 0),
    { self.selected.is_empty() }
    /// Borrow the actual canonical Hard owner with its existing guarantees.
    pub fn selection(&self) -> (owner: &selection::CompetitiveSelectionHard)
        requires self.inv(),
        ensures owner.inv(), owner.allocation == self.winner_spec(),
            owner.scores@ == self.scores_spec(),
    { &self.hard }
    /// Observe the retained Hard winner without mutable selection authority.
    pub fn winner(&self) -> (winner: Option<usize>)
        requires self.inv(), ensures winner == self.winner_spec(),
    { self.hard.allocation }
    /// Borrow the actual Hard-owned score representation for audit.
    pub fn scores(&self) -> (scores: &[u64])
        requires self.inv(), ensures scores@ == self.scores_spec(),
    { self.hard.scores.as_slice() }
    /// Borrow the original immutable comparison context.
    pub fn order(&self) -> (order: &C)
        requires self.inv(), ensures *order == self.order_spec(),
    { &self.order }
    /// Borrow the actual OrderingPass-owned arrangement.
    pub fn arrangement(&self) -> (positions: &[usize])
        requires self.inv(), ensures positions@ == self.arranged_spec(),
    { self.arrangement.positions() }
    /// Borrow the inverse from the same arrangement owner.
    pub fn inverse(&self) -> (inverse: &[usize])
        requires self.inv(), ensures inverse@ == self.inverse_spec(),
    { self.arrangement.inverse() }
}

}
