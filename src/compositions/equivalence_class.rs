// EquivalenceClass assembled from two ResourceRegistry owners and Budget.
//
// The parent registry stores non-identity links, the rank registry stores nonzero ranks, and
// Budget owns the successful-union count and ceiling. Missing parent bindings mean identity;
// missing rank bindings mean zero. These are the defaulted views proved by the TLA+ reduction.

use vstd::prelude::*;

use crate::primitives::budget::Budget;
use crate::primitives::resource_registry::ResourceRegistry;

verus! {

/// Default an absent parent binding to the element itself.
pub open spec fn parent_view(
    registry: &ResourceRegistry<usize, usize>,
    element: usize,
) -> usize {
    if registry.contains_key(element) {
        choose|parent: usize| registry.maps_to(element, parent)
    } else {
        element
    }
}

/// Default an absent rank binding to zero.
pub open spec fn rank_view(
    registry: &ResourceRegistry<usize, u64>,
    element: usize,
) -> u64 {
    if registry.contains_key(element) {
        choose|rank: u64| registry.maps_to(element, rank)
    } else {
        0
    }
}

/// Equal presence and mappings produce the same defaulted rank view.
pub proof fn rank_view_frame(
    before: &ResourceRegistry<usize, u64>,
    after: &ResourceRegistry<usize, u64>,
    element: usize,
)
    requires
        before.unique_mapping(),
        after.unique_mapping(),
        before.contains_key(element) == after.contains_key(element),
        forall|rank: u64|
            #[trigger] before.maps_to(element, rank) == after.maps_to(element, rank),
    ensures rank_view(before, element) == rank_view(after, element),
{
    if before.contains_key(element) {
        before.contains_has_value(element);
        let rank = choose|rank: u64| before.maps_to(element, rank);
        assert(after.maps_to(element, rank));
        let before_choice = choose|value: u64| before.maps_to(element, value);
        let after_choice = choose|value: u64| after.maps_to(element, value);
        before.unique_value(element, before_choice, rank);
        after.unique_value(element, after_choice, rank);
    }
}

/// A union-by-rank partition whose mutable state is owned by reusable structures.
pub struct EquivalenceClass {
    /// Number of elements in the fixed universe.
    pub n: usize,
    /// Registry that owns parent links.
    pub parents: ResourceRegistry<usize, usize>,
    /// Registry that owns union-by-rank values.
    pub ranks: ResourceRegistry<usize, u64>,
    /// Budget that bounds successful unions.
    pub budget: Budget,
}

impl EquivalenceClass {
    /// Return the registered parent of `element` in the partition model.
    pub open spec fn parent_of(&self, element: usize) -> usize {
        parent_view(&self.parents, element)
    }

    /// Return the registered union-by-rank value for `element`.
    pub open spec fn rank_of(&self, element: usize) -> u64 {
        rank_view(&self.ranks, element)
    }

    /// Component invariants plus the rank certificate that makes parent traversal finite.
    pub open spec fn inv(&self) -> bool {
        &&& self.parents.unique_mapping()
        &&& self.ranks.unique_mapping()
        &&& self.budget.safety_invariant()
        &&& self.budget.reserved == 0
        &&& self.budget.pending_eviction == 0
        &&& forall|child: usize, parent: usize|
            #[trigger] self.parents.maps_to(child, parent) ==> {
                &&& child < self.n
                &&& parent < self.n
                &&& child != parent
            }
        &&& forall|element: usize, rank: u64|
            #[trigger] self.ranks.maps_to(element, rank) ==> {
                &&& element < self.n
                &&& 0 < rank
                &&& rank <= self.budget.allocated
            }
        &&& forall|child: usize, parent: usize|
            #[trigger] self.parents.maps_to(child, parent) ==>
                self.rank_of(child) < self.rank_of(parent)
    }

    /// A stored parent binding determines the defaulted parent view.
    pub proof fn parent_mapping_determines_view(&self, element: usize, parent: usize)
        requires
            self.parents.unique_mapping(),
            self.parents.maps_to(element, parent),
        ensures self.parent_of(element) == parent,
    {
        self.parents.maps_to_implies_contains(element, parent);
        let chosen = choose|value: usize| self.parents.maps_to(element, value);
        self.parents.unique_value(element, chosen, parent);
    }

    /// A stored rank binding determines the defaulted rank view.
    pub proof fn rank_mapping_determines_view(&self, element: usize, rank: u64)
        requires
            self.ranks.unique_mapping(),
            self.ranks.maps_to(element, rank),
        ensures self.rank_of(element) == rank,
    {
        self.ranks.maps_to_implies_contains(element, rank);
        let chosen = choose|value: u64| self.ranks.maps_to(element, value);
        self.ranks.unique_value(element, chosen, rank);
    }

    /// Every derived rank is bounded by Budget's successful-union count.
    pub proof fn rank_bounded(&self, element: usize)
        requires self.inv(), element < self.n,
        ensures self.rank_of(element) <= self.budget.allocated,
    {
        if self.ranks.contains_key(element) {
            self.ranks.contains_has_value(element);
            let rank = choose|rank: u64| self.ranks.maps_to(element, rank);
            assert(self.ranks.maps_to(element, rank));
            self.rank_mapping_determines_view(element, rank);
        }
    }

    /// A defaulted root has no stored non-identity parent binding.
    pub proof fn root_has_no_parent(&self, element: usize)
        requires self.inv(), element < self.n, self.parent_of(element) == element,
        ensures !self.parents.contains_key(element),
    {
        if self.parents.contains_key(element) {
            self.parents.contains_has_value(element);
            let parent = choose|parent: usize| self.parents.maps_to(element, parent);
            assert(self.parents.maps_to(element, parent));
            self.parent_mapping_determines_view(element, parent);
            assert(element != parent);
        }
    }

    /// Construct singleton classes from empty registries and an empty Budget allocation.
    pub fn new(n: usize, max_unions: u64) -> (classes: EquivalenceClass)
        ensures
            classes.n == n,
            classes.parents.entries@.len() == 0,
            classes.ranks.entries@.len() == 0,
            classes.budget.capacity == max_unions,
            classes.budget.allocated == 0,
            classes.inv(),
    {
        let parents = ResourceRegistry::new();
        let ranks = ResourceRegistry::new();
        let budget = Budget::new(max_unions);
        EquivalenceClass { n, parents, ranks, budget }
    }

    /// Read the defaulted parent view through ResourceRegistry.
    pub fn parent_value(&self, element: usize) -> (parent: usize)
        requires self.inv(), element < self.n,
        ensures
            parent == self.parent_of(element),
            parent < self.n,
            parent != element ==> self.parents.maps_to(element, parent),
    {
        match self.parents.lookup(element) {
            Some(parent) => {
                proof { self.parent_mapping_determines_view(element, parent); }
                parent
            }
            None => element,
        }
    }

    /// Read the defaulted rank view through ResourceRegistry.
    pub fn rank_value(&self, element: usize) -> (rank: u64)
        requires self.inv(), element < self.n,
        ensures
            rank == self.rank_of(element),
            rank <= self.budget.allocated,
    {
        match self.ranks.lookup(element) {
            Some(rank) => {
                proof { self.rank_mapping_determines_view(element, rank); }
                rank
            }
            None => 0,
        }
    }

    /// Follow strictly increasing rank certificates to a root.
    pub fn find(&self, element: usize) -> (root: usize)
        requires self.inv(), element < self.n,
        ensures root < self.n, self.parent_of(root) == root,
    {
        let mut current = element;
        let mut parent = self.parent_value(current);
        while parent != current
            invariant
                self.inv(),
                current < self.n,
                parent < self.n,
                parent == self.parent_of(current),
                parent != current ==> self.parents.maps_to(current, parent),
            decreases self.budget.allocated - self.rank_of(current),
        {
            proof {
                self.rank_bounded(current);
                self.rank_bounded(parent);
                assert(self.rank_of(current) < self.rank_of(parent));
            }
            current = parent;
            parent = self.parent_value(current);
        }
        current
    }

    /// Attach one lower-rank root to one higher-rank root through ResourceRegistry.Register.
    fn attach_lower(&mut self, lower: usize, higher: usize)
        requires
            old(self).inv(),
            lower < old(self).n,
            higher < old(self).n,
            lower != higher,
            old(self).parent_of(lower) == lower,
            old(self).parent_of(higher) == higher,
            old(self).rank_of(lower) < old(self).rank_of(higher),
        ensures
            final(self).inv(),
            final(self).n == old(self).n,
            final(self).budget == old(self).budget,
            final(self).ranks.entries@ == old(self).ranks.entries@,
    {
        proof { self.root_has_no_parent(lower); }
        self.parents.register(lower, higher);
        assert forall|child: usize, parent: usize|
            #[trigger] self.parents.maps_to(child, parent) implies {
                &&& child < self.n
                &&& parent < self.n
                &&& child != parent
            } by {
            if child == lower {
                self.parents.unique_value(child, parent, higher);
            } else {
                assert(old(self).parents.maps_to(child, parent));
            }
        }
        assert forall|child: usize, parent: usize|
            #[trigger] self.parents.maps_to(child, parent) implies
                self.rank_of(child) < self.rank_of(parent) by {
            if child == lower {
                self.parents.unique_value(child, parent, higher);
            } else {
                assert(old(self).parents.maps_to(child, parent));
            }
        }
    }

    /// Attach equal-rank roots and raise the surviving root's rank.
    fn attach_equal(&mut self, lower: usize, higher: usize, rank: u64)
        requires
            old(self).inv(),
            lower < old(self).n,
            higher < old(self).n,
            lower != higher,
            old(self).parent_of(lower) == lower,
            old(self).parent_of(higher) == higher,
            rank == old(self).rank_of(lower),
            rank == old(self).rank_of(higher),
            rank < old(self).budget.allocated,
        ensures
            final(self).inv(),
            final(self).n == old(self).n,
            final(self).budget == old(self).budget,
    {
        proof {
            self.root_has_no_parent(lower);
            self.root_has_no_parent(higher);
        }
        self.parents.register(lower, higher);
        self.ranks.register(higher, rank + 1);
        assert(self.rank_of(higher) == (rank + 1) as u64) by {
            self.rank_mapping_determines_view(higher, (rank + 1) as u64);
        }
        assert forall|element: usize| element != higher implies
            self.rank_of(element) == old(self).rank_of(element) by {
            rank_view_frame(&old(self).ranks, &self.ranks, element);
        }
        assert forall|child: usize, parent: usize|
            #[trigger] self.parents.maps_to(child, parent) implies {
                &&& child < self.n
                &&& parent < self.n
                &&& child != parent
            } by {
            if child == lower {
                self.parents.unique_value(child, parent, higher);
            } else {
                assert(old(self).parents.maps_to(child, parent));
            }
        }
        assert forall|element: usize, value: u64|
            #[trigger] self.ranks.maps_to(element, value) implies {
                &&& element < self.n
                &&& 0 < value
                &&& value <= self.budget.allocated
            } by {
            if element == higher {
                self.ranks.unique_value(element, value, (rank + 1) as u64);
            } else {
                assert(old(self).ranks.maps_to(element, value));
            }
        }
        assert forall|child: usize, parent: usize|
            #[trigger] self.parents.maps_to(child, parent) implies
                self.rank_of(child) < self.rank_of(parent) by {
            if child == lower {
                self.parents.unique_value(child, parent, higher);
                assert(self.rank_of(lower) == rank);
            } else {
                assert(old(self).parents.maps_to(child, parent));
                assert(child != higher);
                if parent == higher {
                    assert(self.rank_of(child) == old(self).rank_of(child));
                } else {
                    assert(self.rank_of(child) == old(self).rank_of(child));
                    assert(self.rank_of(parent) == old(self).rank_of(parent));
                }
            }
        }
    }

    /// Union two representatives using the registry and Budget actions from the reduction.
    pub fn union(&mut self, left: usize, right: usize) -> (merged: bool)
        requires old(self).inv(), left < old(self).n, right < old(self).n,
        ensures
            final(self).inv(),
            final(self).n == old(self).n,
            final(self).budget.capacity == old(self).budget.capacity,
            merged ==> final(self).budget.allocated == old(self).budget.allocated + 1,
            !merged ==> final(self).budget.allocated == old(self).budget.allocated,
    {
        if self.budget.allocated >= self.budget.capacity {
            return false;
        }
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            return false;
        }
        let left_rank = self.rank_value(left_root);
        let right_rank = self.rank_value(right_root);
        let ghost prior_allocation = self.budget.allocated;
        let _accepted = self.budget.try_allocate(1);
        assert(_accepted);
        assert(self.inv()) by {
            assert forall|element: usize, rank: u64|
                #[trigger] self.ranks.maps_to(element, rank) implies
                    rank <= self.budget.allocated by {
                assert(rank <= prior_allocation);
            }
        }
        if left_rank < right_rank {
            self.attach_lower(left_root, right_root);
        } else if left_rank > right_rank {
            self.attach_lower(right_root, left_root);
        } else {
            assert(left_rank < self.budget.allocated);
            self.attach_equal(right_root, left_root, left_rank);
        }
        true
    }

    /// Whether two elements resolve to the same root.
    pub fn same(&self, left: usize, right: usize) -> (equivalent: bool)
        requires self.inv(), left < self.n, right < self.n,
    {
        self.find(left) == self.find(right)
    }
}

}
