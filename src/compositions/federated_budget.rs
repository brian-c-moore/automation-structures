// Executable FederatedBudget contract.
//
// FederatedBudget is a master pool subdivided into named sub-pools: the master
// hands capacity out to sub-pools, and each sub-pool meters its own consumption.
// The TLA+ spec at formal/structures/FederatedBudget/FederatedBudget.tla has three state variables
// — master_allocated, sub_capacities, sub_allocated (the latter two functions
// over SubPoolNames) — and checks four invariants:
//
//   TypeInvariant        == master_allocated ∈ Nat /\ sub_capacities,
//                            sub_allocated ∈ [SubPoolNames -> Nat]
//   MasterCapacityBound  == master_allocated <= MasterCapacity
//   SubPoolCapacityBound     == ∀ name: sub_allocated[name] <= sub_capacities[name]
//   CapacityConservation == master_allocated = SumOver(SubPoolNames, sub_capacities)
//
// TLA+ sums over a bijective enumeration of finite SubPoolNames. The executable
// representation fixes that enumeration as Vec index order and proves the same
// single-element sum delta over Seq. All four predicates are preserved by the
// three state transitions.
//
// SubPoolNames is represented by indices 0..num_pools-1; the two functions are
// equal-length Vecs.
//
// Each method states its exact indexed update and frames every unaffected field;
// invariant preservation alone does not determine which sub-pool changed.

use vstd::prelude::*;

verus! {

// ── Recursive sum spec + lemmas (the SumOver replacement) ───────────────

/// Sum of the first `n` elements (`s[0]` through `s[n-1]`), lifted to int.
pub open spec fn sum_to(s: Seq<u64>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else if n > s.len() as int {
        0
    } else {
        s[n - 1] as int + sum_to(s, n - 1)
    }
}

/// The sum of any prefix is non-negative (every term is a u64).
pub proof fn lemma_sum_nonneg(s: Seq<u64>, n: int)
    requires 0 <= n <= s.len(),
    ensures sum_to(s, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_sum_nonneg(s, n - 1);
    }
}

/// An all-zero prefix sums to zero (used to establish Init's consistency).
pub proof fn lemma_sum_zeros(s: Seq<u64>, n: int)
    requires
        0 <= n <= s.len(),
        forall|j: int| 0 <= j < n ==> s[j] == 0,
    ensures sum_to(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_sum_zeros(s, n - 1);
    }
}

/// Each element is at most the whole-prefix sum (all terms non-negative).
pub proof fn lemma_elem_le_sum(s: Seq<u64>, k: int, n: int)
    requires 0 <= k < n <= s.len(),
    ensures s[k] as int <= sum_to(s, n),
    decreases n,
{
    if n == k + 1 {
        lemma_sum_nonneg(s, k);
    } else {
        lemma_elem_le_sum(s, k, n - 1);
    }
}

/// Updating index `k` does not change the sum of any prefix that stops at or
/// before `k`.
pub proof fn lemma_sum_unaffected(s: Seq<u64>, k: int, nv: u64, m: int)
    requires 0 <= m <= k < s.len(),
    ensures sum_to(s.update(k, nv), m) == sum_to(s, m),
    decreases m,
{
    if m > 0 {
        lemma_sum_unaffected(s, k, nv, m - 1);
    }
}

/// Updating index `k` to `nv` shifts the whole sum by (nv - s[k]). This is the
/// Single-element-update lemma replacing the enumeration argument.
pub proof fn lemma_sum_update(s: Seq<u64>, k: int, nv: u64, n: int)
    requires 0 <= k < n <= s.len(),
    ensures sum_to(s.update(k, nv), n) == sum_to(s, n) - s[k] as int + nv as int,
    decreases n,
{
    if n == k + 1 {
        lemma_sum_unaffected(s, k, nv, k);
    } else {
        lemma_sum_update(s, k, nv, n - 1);
    }
}

/// A master pool federated into `num_pools` sub-pools.
pub struct FederatedBudget {
    pub master_capacity: u64,
    pub master_allocated: u64,
    pub sub_capacities: Vec<u64>,
    pub sub_allocated: Vec<u64>,
}

impl FederatedBudget {
    // ── Specifications ──────────────────────────────────────────────────

    /// SumOver(SubPoolNames, sub_capacities) as a recursive sum.
    pub open spec fn sum_caps(&self) -> int {
        sum_to(self.sub_capacities@, self.sub_capacities@.len() as int)
    }

    /// TLA+ `TypeInvariant`: the two functions share the SubPoolNames domain
    /// (the Nat clauses are carried by u64).
    pub open spec fn type_invariant(&self) -> bool {
        self.sub_capacities.len() == self.sub_allocated.len()
    }

    /// TLA+ `MasterCapacityBound`.
    pub open spec fn master_capacity_bound(&self) -> bool {
        self.master_allocated <= self.master_capacity
    }

    /// TLA+ `SubPoolCapacityBound`.
    pub open spec fn sub_pool_capacity_bound(&self) -> bool {
        forall|i: int|
            0 <= i < self.sub_capacities.len() ==>
                #[trigger] self.sub_allocated@[i] <= self.sub_capacities@[i]
    }

    /// TLA+ `CapacityConservation`.
    pub open spec fn capacity_conservation(&self) -> bool {
        self.master_allocated == self.sum_caps()
    }

    /// Full maintained invariant.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.master_capacity_bound()
        &&& self.sub_pool_capacity_bound()
        &&& self.capacity_conservation()
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Empty federation: master unallocated, every sub-pool at zero.
    pub fn new(master_capacity: u64, num_pools: usize) -> (fb: FederatedBudget)
        ensures
            fb.master_capacity == master_capacity,
            fb.sub_capacities@.len() == num_pools,
            fb.master_allocated == 0,
            fb.inv(),
    {
        let mut sub_capacities: Vec<u64> = Vec::new();
        let mut sub_allocated: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < num_pools
            invariant
                i <= num_pools,
                sub_capacities.len() == i,
                sub_allocated.len() == i,
                forall|j: int| 0 <= j < i ==> sub_capacities@[j] == 0,
                forall|j: int| 0 <= j < i ==> sub_allocated@[j] == 0,
            decreases num_pools - i,
        {
            sub_capacities.push(0);
            sub_allocated.push(0);
            i = i + 1;
        }
        let fb = FederatedBudget { master_capacity, master_allocated: 0, sub_capacities, sub_allocated };
        proof {
            lemma_sum_zeros(fb.sub_capacities@, fb.sub_capacities@.len() as int);
        }
        fb
    }

    // ── AllocateSubPool (TLA+ AllocateSubPool) ──────────────────────────

    /// Hand `amount` of master capacity to sub-pool `name`, growing its
    /// capacity. Succeeds iff the master ceiling allows it (the TLA+ IF guard).
    /// master_allocated and the sub-pool capacity grow in lockstep, so
    /// CapacityConservation is preserved.
    pub fn allocate_sub_pool(&mut self, name: usize, amount: u64) -> (ok: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).master_capacity == old(self).master_capacity,
            final(self).sub_capacities.len() == old(self).sub_capacities.len(),
            ok == (name < old(self).sub_capacities.len()
                && 1 <= amount <= old(self).master_capacity
                && old(self).master_allocated + amount as int <= old(self).master_capacity as int),
            ok ==> {
                &&& final(self).master_allocated == old(self).master_allocated + amount
                &&& final(self).sub_capacities@ ==
                        old(self).sub_capacities@.update(name as int, (old(self).sub_capacities@[name as int] + amount) as u64)
            },
            !ok ==> final(self).master_allocated == old(self).master_allocated
                    && final(self).sub_capacities@ == old(self).sub_capacities@,
            // AllocateSubPool changes capacity delegation, not consumption.
            final(self).sub_allocated@ == old(self).sub_allocated@,
    {
        if name >= self.sub_capacities.len() || amount == 0 || amount > self.master_capacity {
            false
        } else if amount <= self.master_capacity - self.master_allocated {
            // sub_capacities[name] <= sum_caps == master_allocated, so the
            // sub-pool capacity bump cannot overflow either.
            proof {
                lemma_elem_le_sum(self.sub_capacities@, name as int, self.sub_capacities@.len() as int);
            }
            let new_cap = self.sub_capacities[name] + amount;
            let old_cap = self.sub_capacities[name];
            let _ = old_cap;
            self.sub_capacities.set(name, new_cap);
            self.master_allocated = self.master_allocated + amount;
            // Consistency: the sum shifted by exactly +amount.
            proof {
                lemma_sum_update(old(self).sub_capacities@, name as int, new_cap,
                    old(self).sub_capacities@.len() as int);
            }
            true
        } else {
            false
        }
    }

    // ── AllocateFromSubPool (TLA+ AllocateFromSubPool) ──────────────────

    /// Consume `amount` within sub-pool `name`. Succeeds iff it fits under that
    /// sub-pool's capacity (the TLA+ IF guard). Touches only sub_allocated, so
    /// Federation/Consistency are untouched.
    pub fn allocate_from_sub_pool(&mut self, name: usize, amount: u64) -> (ok: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).master_capacity == old(self).master_capacity,
            final(self).master_allocated == old(self).master_allocated,
            final(self).sub_capacities@ == old(self).sub_capacities@,
            ok == (name < old(self).sub_allocated.len()
                && 1 <= amount <= old(self).master_capacity
                && old(self).sub_allocated@[name as int] + amount as int
                    <= old(self).sub_capacities@[name as int] as int),
            // A successful call changes exactly the selected pool's allocation.
            ok ==> final(self).sub_allocated@ == old(self).sub_allocated@.update(
                        name as int,
                        (old(self).sub_allocated@[name as int] + amount) as u64),
            !ok ==> final(self).sub_allocated@ == old(self).sub_allocated@,
        {
        if name >= self.sub_allocated.len() || amount == 0 || amount > self.master_capacity {
            false
        } else if amount <= self.sub_capacities[name] - self.sub_allocated[name] {
            let new_alloc = self.sub_allocated[name] + amount;
            self.sub_allocated.set(name, new_alloc);
            true
        } else {
            false
        }
    }

    // ── ReleaseFromSubPool (TLA+ ReleaseFromSubPool) ────────────────────

    /// Release `amount` of sub-pool `name`'s consumption. Enabling condition:
    /// `amount <= sub_allocated[name]`. Only `sub_allocated` shrinks.
    pub fn release_from_sub_pool(&mut self, name: usize, amount: u64) -> (ok: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).master_capacity == old(self).master_capacity,
            final(self).master_allocated == old(self).master_allocated,
            final(self).sub_capacities@ == old(self).sub_capacities@,
            ok == (name < old(self).sub_allocated.len()
                && 1 <= amount <= old(self).master_capacity
                && amount <= old(self).sub_allocated@[name as int]),
            ok ==> final(self).sub_allocated@ == old(self).sub_allocated@.update(
                name as int, (old(self).sub_allocated@[name as int] - amount) as u64),
            !ok ==> final(self).sub_allocated@ == old(self).sub_allocated@,
    {
        if name >= self.sub_allocated.len() || amount == 0 || amount > self.master_capacity {
            false
        } else if amount <= self.sub_allocated[name] {
            let new_alloc = self.sub_allocated[name] - amount;
            self.sub_allocated.set(name, new_alloc);
            true
        } else {
            false
        }
    }
}

}
