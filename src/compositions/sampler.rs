//! Sampler assembled from the ActuationPass and Budget primitives.
//!
//! ActuationPass owns the live support and selected-effect projection. Budget owns the sample
//! ceiling. Sampler adds only the atomic coupling between an actuation and one Budget allocation,
//! plus caller-supplied proposal admission rules.

use crate::primitives::actuation_pass::ActuationPass;
use crate::primitives::budget::Budget;
use vstd::prelude::*;

verus! {

/// Integer indicator for an occupied ActuationPass slot.
pub open spec fn present<T>(value: Option<T>) -> int {
    if value is Some { 1 } else { 0 }
}

/// Number of present effects in the first `n` ActuationPass seats.
pub open spec fn selected_count<T>(effects: Seq<Option<T>>, n: int) -> int
    decreases n,
{
    if n <= 0 || n > effects.len() {
        0
    } else {
        present(effects[n - 1]) + selected_count(effects, n - 1)
    }
}

proof fn selected_count_none<T>(effects: Seq<Option<T>>, n: int)
    requires
        0 <= n <= effects.len(),
        forall|i: int| 0 <= i < effects.len() ==> #[trigger] effects[i] is None,
    ensures selected_count(effects, n) == 0,
    decreases n,
{
    if n > 0 {
        selected_count_none(effects, n - 1);
    }
}

proof fn selected_count_update_unaffected<T>(
    effects: Seq<Option<T>>,
    index: int,
    replacement: Option<T>,
    n: int,
)
    requires 0 <= n <= index < effects.len(),
    ensures selected_count(effects.update(index, replacement), n)
        == selected_count(effects, n),
    decreases n,
{
    if n > 0 {
        selected_count_update_unaffected(effects, index, replacement, n - 1);
        assert(effects.update(index, replacement)[n - 1] == effects[n - 1]);
    }
}

proof fn selected_count_update<T>(
    effects: Seq<Option<T>>,
    index: int,
    replacement: Option<T>,
    n: int,
)
    requires 0 <= index < n <= effects.len(),
    ensures selected_count(effects.update(index, replacement), n)
        == selected_count(effects, n) - present(effects[index]) + present(replacement),
    decreases n,
{
    if n == index + 1 {
        selected_count_update_unaffected(effects, index, replacement, index);
        assert(effects.update(index, replacement)[index] == replacement);
    } else {
        selected_count_update(effects, index, replacement, n - 1);
        assert(effects.update(index, replacement)[n - 1] == effects[n - 1]);
    }
}

/// A bounded without-replacement sampler composed from ActuationPass and Budget.
pub struct Sampler {
    /// Owner of support, selection, and applied effects.
    pub actuation: ActuationPass,
    /// Owner of the sample-size ceiling.
    pub budget: Budget,
}

impl Sampler {
    /// Whether one item is selected in the ActuationPass effect projection.
    pub open spec fn contains(&self, item: usize) -> bool {
        item < self.actuation.effects.len() && self.actuation.effects@[item as int] is Some
    }

    /// Default the absent ActuationPass allocation to zero support weight.
    pub open spec fn support_weight(&self, item: usize) -> u64 {
        if item < self.actuation.allocation.len()
            && self.actuation.allocation@[item as int] is Some
        {
            self.actuation.allocation@[item as int]->Some_0
        } else {
            0
        }
    }

    /// Exact admission predicate for a caller-proposed weighted draw.
    pub open spec fn weighted_draw_enabled(&self, item: usize, entropy: u64) -> bool {
        &&& item < self.actuation.num_seats
        &&& self.budget.allocated < self.budget.capacity
        &&& entropy < self.support_weight(item)
        &&& !self.contains(item)
    }

    /// Exact admission predicate for a caller-proposed uniform draw.
    pub open spec fn uniform_draw_enabled(&self, item: usize) -> bool {
        &&& item < self.actuation.num_seats
        &&& self.budget.allocated < self.budget.capacity
        &&& self.support_weight(item) > 0
        &&& !self.contains(item)
    }

    /// Every live ActuationPass allocation has positive support weight.
    pub open spec fn support_domain(&self) -> bool {
        forall|i: int| 0 <= i < self.actuation.allocation.len()
            && #[trigger] self.actuation.allocation@[i] is Some
            ==> self.actuation.allocation@[i]->Some_0 > 0
    }

    /// The two primitive states and their coupling are well formed.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.actuation.invariant()
        &&& !self.actuation.complete
        &&& self.support_domain()
        &&& self.budget.safety_invariant()
        &&& self.budget.reserved == 0
        &&& self.budget.pending_eviction == 0
        &&& self.budget.allocated as int
            == selected_count(self.actuation.effects@, self.actuation.effects.len() as int)
    }

    /// Selected cardinality is owned by the Budget.
    pub open spec fn bounded_sample(&self) -> bool {
        self.budget.allocated <= self.budget.capacity
    }

    /// Every selected effect is tied to a positive live ActuationPass allocation.
    pub open spec fn support_consistency(&self) -> bool {
        forall|i: int| 0 <= i < self.actuation.effects.len()
            && #[trigger] self.actuation.effects@[i] is Some
            ==> self.actuation.allocation@[i] is Some
                && self.actuation.allocation@[i]->Some_0 > 0
    }

    /// Full composition invariant.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.bounded_sample() && self.support_consistency()
    }

    /// Build the ActuationPass support projection and an empty sample Budget.
    pub fn new(distribution: Vec<u64>, sample_size: usize) -> (sampler: Self)
        ensures
            sampler.actuation.num_seats == distribution@.len(),
            sampler.budget.capacity == sample_size as u64,
            sampler.budget.allocated == 0,
            sampler.budget.reserved == 0,
            sampler.budget.pending_eviction == 0,
            !sampler.actuation.complete,
            forall|i: int| 0 <= i < distribution@.len() ==>
                #[trigger] sampler.actuation.effects@[i] is None,
            sampler.inv(),
            forall|i: int| 0 <= i < distribution@.len() ==> {
                let allocation = #[trigger] sampler.actuation.allocation@[i];
                if distribution@[i] == 0 {
                    allocation is None
                } else {
                    allocation == Some(distribution@[i])
                }
            },
    {
        let length = distribution.len();
        let mut allocation: Vec<Option<u64>> = Vec::new();
        let mut index: usize = 0;
        while index < length
            invariant
                index <= length,
                length == distribution@.len(),
                allocation.len() == index,
                forall|i: int| 0 <= i < index ==> {
                    let value = #[trigger] allocation@[i];
                    if distribution@[i] == 0 {
                        value is None
                    } else {
                        value == Some(distribution@[i])
                    }
                },
            decreases length - index,
        {
            let weight = distribution[index];
            if weight == 0 {
                allocation.push(None);
            } else {
                allocation.push(Some(weight));
            }
            index += 1;
        }
        let actuation = ActuationPass::new(allocation, length);
        let budget = Budget::new(sample_size as u64);
        proof { selected_count_none(actuation.effects@, actuation.effects.len() as int); }
        Self { actuation, budget }
    }

    /// Read one support weight, mapping ActuationPass's absent allocation to zero.
    pub fn weight(&self, item: usize) -> (weight: u64)
        requires self.inv(), item < self.actuation.num_seats,
        ensures weight == self.support_weight(item),
    {
        self.actuation.allocation[item].unwrap_or(0)
    }

    /// Executable selected-membership projection.
    pub fn contains_exec(&self, item: usize) -> (selected: bool)
        requires self.inv(),
        ensures selected == self.contains(item),
    {
        if item >= self.actuation.effects.len() {
            false
        } else {
            self.actuation.is_actuated(item)
        }
    }

    /// Couple ActuationPass.Actuate with Budget.TryAllocate(1).
    pub fn sample(&mut self, item: usize)
        requires
            old(self).inv(),
            item < old(self).actuation.num_seats,
            old(self).budget.allocated < old(self).budget.capacity,
            old(self).actuation.allocation@[item as int] is Some,
            old(self).actuation.effects@[item as int] is None,
        ensures
            final(self).inv(),
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).budget.allocated == old(self).budget.allocated + 1,
            final(self).actuation.allocation@ == old(self).actuation.allocation@,
            final(self).actuation.effects@
                == old(self).actuation.effects@.update(
                    item as int,
                    old(self).actuation.allocation@[item as int],
                ),
    {
        let ghost prior_effects = self.actuation.effects@;
        let _accepted = self.budget.try_allocate(1);
        assert(_accepted);
        self.actuation.actuate(item);
        proof {
            selected_count_update(
                prior_effects,
                item as int,
                self.actuation.effects@[item as int],
                prior_effects.len() as int,
            );
        }
    }

    /// Withdraw an unselected support item through ActuationPass.Deallocate.
    pub fn zero(&mut self, item: usize) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            accepted == (item < old(self).actuation.num_seats && !old(self).contains(item)),
            final(self).budget == old(self).budget,
            final(self).actuation.num_seats == old(self).actuation.num_seats,
            final(self).actuation.complete == old(self).actuation.complete,
            final(self).actuation.effects@ == old(self).actuation.effects@,
            accepted ==> final(self).actuation.allocation@
                == if old(self).actuation.allocation@[item as int] is Some {
                    old(self).actuation.allocation@.update(item as int, None)
                } else {
                    old(self).actuation.allocation@
                },
            !accepted ==> final(self).actuation.allocation@ == old(self).actuation.allocation@,
    {
        if item >= self.actuation.num_seats || self.contains_exec(item) {
            return false;
        }
        if self.actuation.is_allocated(item) {
            self.actuation.deallocate(item);
        }
        true
    }

    /// Weighted rejection over caller-supplied proposal and entropy.
    pub fn draw_weighted(&mut self, item: usize, entropy: u64) -> (accepted: bool)
        requires old(self).inv(), item < old(self).actuation.num_seats,
        ensures
            final(self).inv(),
            accepted == old(self).weighted_draw_enabled(item, entropy),
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).budget.reserved == old(self).budget.reserved,
            final(self).budget.pending_eviction == old(self).budget.pending_eviction,
            final(self).actuation.num_seats == old(self).actuation.num_seats,
            final(self).actuation.allocation@ == old(self).actuation.allocation@,
            final(self).actuation.complete == old(self).actuation.complete,
            accepted ==> {
                &&& final(self).budget.allocated == old(self).budget.allocated + 1
                &&& final(self).actuation.effects@
                    == old(self).actuation.effects@.update(
                        item as int,
                        old(self).actuation.allocation@[item as int],
                    )
            },
            !accepted ==> {
                &&& final(self).budget.allocated == old(self).budget.allocated
                &&& final(self).actuation.effects@ == old(self).actuation.effects@
            },
    {
        if self.budget.allocated >= self.budget.capacity {
            return false;
        }
        let weight = self.weight(item);
        if entropy >= weight || self.contains_exec(item) {
            return false;
        }
        self.sample(item);
        true
    }

    /// Uniform-support admission over a caller-supplied proposal.
    pub fn draw_uniform(&mut self, item: usize) -> (accepted: bool)
        requires old(self).inv(), item < old(self).actuation.num_seats,
        ensures
            final(self).inv(),
            accepted == old(self).uniform_draw_enabled(item),
            final(self).budget.capacity == old(self).budget.capacity,
            final(self).budget.reserved == old(self).budget.reserved,
            final(self).budget.pending_eviction == old(self).budget.pending_eviction,
            final(self).actuation.num_seats == old(self).actuation.num_seats,
            final(self).actuation.allocation@ == old(self).actuation.allocation@,
            final(self).actuation.complete == old(self).actuation.complete,
            accepted ==> {
                &&& final(self).budget.allocated == old(self).budget.allocated + 1
                &&& final(self).actuation.effects@
                    == old(self).actuation.effects@.update(
                        item as int,
                        old(self).actuation.allocation@[item as int],
                    )
            },
            !accepted ==> {
                &&& final(self).budget.allocated == old(self).budget.allocated
                &&& final(self).actuation.effects@ == old(self).actuation.effects@
            },
    {
        if self.budget.allocated >= self.budget.capacity {
            return false;
        }
        let weight = self.weight(item);
        if weight == 0 || self.contains_exec(item) {
            return false;
        }
        self.sample(item);
        true
    }
}

}
