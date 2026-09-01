//! FederatedBudget assembled from one master Budget and one Budget per pool.
//!
//! Delegation allocates the master Budget and reserves the same amount in the selected pool.
//! Consumption commits pool reservation. Release returns pool allocation to reservation through
//! the Budget eviction lifecycle. The composition stores no second capacity or allocation
//! ledger.

use crate::primitives::budget::Budget;
use vstd::prelude::*;

verus! {

/// Capacity delegated by one sub-pool Budget.
pub open spec fn delegated(pool: Budget) -> int {
    pool.allocated as int + pool.reserved as int
}

/// Sum of delegated capacity in the first `n` sub-pools.
pub open spec fn delegated_sum_to(pools: Seq<Budget>, n: int) -> int
    decreases n,
{
    if n <= 0 || n > pools.len() {
        0
    } else {
        delegated(pools[n - 1]) + delegated_sum_to(pools, n - 1)
    }
}

proof fn delegated_sum_zero(pools: Seq<Budget>, n: int)
    requires
        0 <= n <= pools.len(),
        forall|i: int| 0 <= i < pools.len()
            ==> #[trigger] pools[i].allocated == 0 && pools[i].reserved == 0,
    ensures delegated_sum_to(pools, n) == 0,
    decreases n,
{
    if n > 0 {
        delegated_sum_zero(pools, n - 1);
    }
}

proof fn delegated_le_sum(pools: Seq<Budget>, index: int, n: int)
    requires 0 <= index < n <= pools.len(),
    ensures delegated(pools[index]) <= delegated_sum_to(pools, n),
    decreases n,
{
    if index == n - 1 {
        assert(delegated_sum_to(pools, n)
            == delegated(pools[index]) + delegated_sum_to(pools, n - 1));
        assert(delegated_sum_to(pools, n - 1) >= 0) by {
            if n - 1 > 0 {
                delegated_le_sum(pools, 0, n - 1);
            }
        }
    } else {
        delegated_le_sum(pools, index, n - 1);
    }
}

proof fn delegated_sum_update_unaffected(
    pools: Seq<Budget>,
    index: int,
    replacement: Budget,
    n: int,
)
    requires 0 <= n <= index < pools.len(),
    ensures delegated_sum_to(pools.update(index, replacement), n)
        == delegated_sum_to(pools, n),
    decreases n,
{
    if n > 0 {
        delegated_sum_update_unaffected(pools, index, replacement, n - 1);
        assert(pools.update(index, replacement)[n - 1] == pools[n - 1]);
    }
}

proof fn delegated_sum_update(
    pools: Seq<Budget>,
    index: int,
    replacement: Budget,
    n: int,
)
    requires 0 <= index < n <= pools.len(),
    ensures delegated_sum_to(pools.update(index, replacement), n)
        == delegated_sum_to(pools, n) - delegated(pools[index]) + delegated(replacement),
    decreases n,
{
    if n == index + 1 {
        delegated_sum_update_unaffected(pools, index, replacement, index);
        assert(pools.update(index, replacement)[index] == replacement);
    } else {
        delegated_sum_update(pools, index, replacement, n - 1);
        assert(pools.update(index, replacement)[n - 1] == pools[n - 1]);
    }
}

/// A master Budget federated into a fixed number of sub-pool Budgets.
pub struct FederatedBudget {
    /// Owner of the master capacity.
    pub master: Budget,
    /// Owners of delegated sub-pool capacity.
    pub sub_pools: Vec<Budget>,
}

impl FederatedBudget {
    /// Total capacity currently delegated to sub-pools.
    pub open spec fn sum_caps(&self) -> int {
        delegated_sum_to(self.sub_pools@, self.sub_pools.len() as int)
    }

    /// Every held ledger is a Budget owner with the expected fixed capacity.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.master.safety_invariant()
        &&& self.master.reserved == 0
        &&& self.master.pending_eviction == 0
        &&& forall|i: int| 0 <= i < self.sub_pools.len() ==> {
            let pool = #[trigger] self.sub_pools@[i];
            &&& pool.capacity == self.master.capacity
            &&& pool.safety_invariant()
            &&& pool.pending_eviction == 0
        }
    }

    /// The master Budget bounds all delegated capacity.
    pub open spec fn master_capacity_bound(&self) -> bool {
        self.master.allocated <= self.master.capacity
    }

    /// Every sub-pool's consumption remains inside its delegated capacity view.
    pub open spec fn sub_pool_capacity_bound(&self) -> bool {
        forall|i: int| 0 <= i < self.sub_pools.len() ==>
            #[trigger] self.sub_pools@[i].allocated + self.sub_pools@[i].reserved
                <= self.master.capacity
    }

    /// Master allocation is exactly the sum of sub-pool allocation plus reservation.
    pub open spec fn capacity_conservation(&self) -> bool {
        self.master.allocated as int == self.sum_caps()
    }

    /// Full composition invariant.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.master_capacity_bound()
            && self.sub_pool_capacity_bound()
            && self.capacity_conservation()
    }

    /// Construct an empty master and empty Budget per sub-pool.
    pub fn new(master_capacity: u64, num_pools: usize) -> (federated: Self)
        ensures
            federated.master.capacity == master_capacity,
            federated.master.allocated == 0,
            federated.master.reserved == 0,
            federated.master.pending_eviction == 0,
            federated.sub_pools.len() == num_pools,
            forall|index: int| 0 <= index < num_pools ==> {
                let pool = #[trigger] federated.sub_pools@[index];
                &&& pool.capacity == master_capacity
                &&& pool.allocated == 0
                &&& pool.reserved == 0
                &&& pool.pending_eviction == 0
            },
            federated.inv(),
    {
        let master = Budget::new(master_capacity);
        let mut sub_pools: Vec<Budget> = Vec::new();
        let mut index: usize = 0;
        while index < num_pools
            invariant
                index <= num_pools,
                master.capacity == master_capacity,
                master.allocated == 0,
                master.reserved == 0,
                master.pending_eviction == 0,
                master.safety_invariant(),
                sub_pools.len() == index,
                forall|i: int| 0 <= i < sub_pools.len() ==> {
                    let pool = #[trigger] sub_pools@[i];
                    &&& pool.capacity == master_capacity
                    &&& pool.allocated == 0
                    &&& pool.reserved == 0
                    &&& pool.pending_eviction == 0
                    &&& pool.safety_invariant()
                },
            decreases num_pools - index,
        {
            sub_pools.push(Budget::new(master_capacity));
            index += 1;
        }
        proof { delegated_sum_zero(sub_pools@, sub_pools.len() as int); }
        Self { master, sub_pools }
    }

    /// Delegate capacity by allocating the master and reserving the selected pool atomically.
    pub fn allocate_sub_pool(&mut self, name: usize, amount: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).master.capacity == old(self).master.capacity,
            final(self).sub_pools.len() == old(self).sub_pools.len(),
            accepted == (name < old(self).sub_pools.len()
                && amount > 0
                && old(self).master.used() + amount as int <= old(self).master.capacity as int),
            !accepted ==> final(self).master.allocated == old(self).master.allocated
                && final(self).sub_pools@ == old(self).sub_pools@,
            accepted ==> {
                &&& final(self).master.allocated == old(self).master.allocated + amount
                &&& final(self).sub_pools@[name as int].allocated
                    == old(self).sub_pools@[name as int].allocated
                &&& final(self).sub_pools@[name as int].reserved
                    == old(self).sub_pools@[name as int].reserved + amount
                &&& final(self).sub_pools@[name as int].capacity
                    == old(self).sub_pools@[name as int].capacity
                &&& final(self).sub_pools@[name as int].pending_eviction
                    == old(self).sub_pools@[name as int].pending_eviction
                &&& forall|index: int| 0 <= index < old(self).sub_pools.len()
                    && index != name as int ==>
                        #[trigger] final(self).sub_pools@[index]
                            == old(self).sub_pools@[index]
            },
    {
        if name >= self.sub_pools.len() || amount == 0 {
            return false;
        }
        proof {
            delegated_le_sum(self.sub_pools@, name as int, self.sub_pools.len() as int);
        }
        let ghost pool_can_reserve = self.sub_pools@[name as int].used() + amount as int
            <= self.sub_pools@[name as int].capacity as int;
        let master_accepted = self.master.try_allocate(amount);
        if !master_accepted {
            return false;
        }
        let ghost old_pools = self.sub_pools@;
        let mut pool = self.sub_pools[name];
        assert(pool_can_reserve);
        let _pool_accepted = pool.reserve(amount);
        assert(_pool_accepted);
        self.sub_pools.set(name, pool);
        proof {
            delegated_sum_update(old_pools, name as int, pool, old_pools.len() as int);
        }
        true
    }

    /// Consume delegated capacity through the selected pool's CommitReservation action.
    pub fn allocate_from_sub_pool(&mut self, name: usize, amount: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).master == old(self).master,
            final(self).sub_pools.len() == old(self).sub_pools.len(),
            accepted == (name < old(self).sub_pools.len()
                && amount > 0
                && amount <= old(self).sub_pools@[name as int].reserved),
            !accepted ==> final(self).sub_pools@ == old(self).sub_pools@,
            accepted ==> {
                &&& final(self).sub_pools@[name as int].allocated
                    == old(self).sub_pools@[name as int].allocated + amount
                &&& final(self).sub_pools@[name as int].reserved
                    == old(self).sub_pools@[name as int].reserved - amount
                &&& final(self).sub_pools@[name as int].capacity
                    == old(self).sub_pools@[name as int].capacity
                &&& final(self).sub_pools@[name as int].pending_eviction
                    == old(self).sub_pools@[name as int].pending_eviction
                &&& forall|index: int| 0 <= index < old(self).sub_pools.len()
                    && index != name as int ==>
                        #[trigger] final(self).sub_pools@[index]
                            == old(self).sub_pools@[index]
            },
    {
        if name >= self.sub_pools.len() || amount == 0 {
            return false;
        }
        let mut pool = self.sub_pools[name];
        if amount > pool.reserved {
            return false;
        }
        let ghost old_pools = self.sub_pools@;
        pool.commit_reservation(amount);
        self.sub_pools.set(name, pool);
        proof {
            delegated_sum_update(old_pools, name as int, pool, old_pools.len() as int);
        }
        true
    }

    /// Return consumed capacity to reservation through the Budget eviction lifecycle.
    pub fn release_from_sub_pool(&mut self, name: usize, amount: u64) -> (accepted: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).master == old(self).master,
            final(self).sub_pools.len() == old(self).sub_pools.len(),
            accepted == (name < old(self).sub_pools.len()
                && amount > 0
                && amount <= old(self).sub_pools@[name as int].allocated),
            !accepted ==> final(self).sub_pools@ == old(self).sub_pools@,
            accepted ==> {
                &&& final(self).sub_pools@[name as int].allocated
                    == old(self).sub_pools@[name as int].allocated - amount
                &&& final(self).sub_pools@[name as int].reserved
                    == old(self).sub_pools@[name as int].reserved + amount
                &&& final(self).sub_pools@[name as int].capacity
                    == old(self).sub_pools@[name as int].capacity
                &&& final(self).sub_pools@[name as int].pending_eviction
                    == old(self).sub_pools@[name as int].pending_eviction
                &&& forall|index: int| 0 <= index < old(self).sub_pools.len()
                    && index != name as int ==>
                        #[trigger] final(self).sub_pools@[index]
                            == old(self).sub_pools@[index]
            },
    {
        if name >= self.sub_pools.len() || amount == 0 {
            return false;
        }
        let mut pool = self.sub_pools[name];
        if amount > pool.allocated {
            return false;
        }
        let ghost old_pools = self.sub_pools@;
        pool.mark_eviction(amount);
        pool.complete_eviction(amount);
        let _reserved = pool.reserve(amount);
        assert(_reserved);
        self.sub_pools.set(name, pool);
        proof {
            delegated_sum_update(old_pools, name as int, pool, old_pools.len() as int);
        }
        true
    }
}

}
