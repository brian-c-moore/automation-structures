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

    /// Whether `path` is a stored-parent path from `start` through `end`.
    pub open spec fn parent_path(
        &self,
        path: Seq<usize>,
        start: usize,
        end: usize,
    ) -> bool {
        &&& path.len() > 0
        &&& path[0] == start
        &&& path[path.len() - 1] == end
        &&& forall|index: int|
            0 <= index < path.len() - 1 ==>
                #[trigger] self.parents.maps_to(path[index], path[index + 1])
    }

    /// Whether stored parent links connect `start` to `end`.
    pub open spec fn reaches(&self, start: usize, end: usize) -> bool {
        exists|path: Seq<usize>| self.parent_path(path, start, end)
    }

    /// Whether `root` is the terminal representative reached from `element`.
    pub open spec fn rooted_at(&self, element: usize, root: usize) -> bool {
        &&& element < self.n
        &&& root < self.n
        &&& self.reaches(element, root)
            &&& self.parent_of(root) == root
    }

    /// Whether two elements have the same terminal representative.
    pub open spec fn same_class(&self, left: usize, right: usize) -> bool {
        exists|root: usize|
            self.rooted_at(left, root) && self.rooted_at(right, root)
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

    proof fn parent_path_edge(
        &self,
        path: Seq<usize>,
        start: usize,
        end: usize,
        index: int,
    )
        requires
            self.parent_path(path, start, end),
            0 <= index < path.len() - 1,
        ensures self.parents.maps_to(path[index], path[index + 1]),
    {
    }

    proof fn parent_path_suffix(
        &self,
        path: Seq<usize>,
        start: usize,
        end: usize,
    )
        requires
            self.parent_path(path, start, end),
            path.len() > 1,
        ensures self.parent_path(path.skip(1), path[1], end),
    {
        let suffix = path.skip(1);
        assert(suffix.len() > 0);
        assert(suffix[0] == path[1]);
        assert(suffix[suffix.len() - 1] == path[path.len() - 1]);
        assert forall|index: int| 0 <= index < suffix.len() - 1 implies
            #[trigger] self.parents.maps_to(suffix[index], suffix[index + 1]) by {
            assert(suffix[index] == path[index + 1]);
            assert(suffix[index + 1] == path[index + 2]);
            self.parent_path_edge(path, start, end, index + 1);
        }
    }

    proof fn terminal_paths_unique(
        &self,
        left_path: Seq<usize>,
        right_path: Seq<usize>,
        start: usize,
        left_root: usize,
        right_root: usize,
    )
        requires
            self.inv(),
            self.parent_path(left_path, start, left_root),
            self.parent_path(right_path, start, right_root),
            start < self.n,
            left_root < self.n,
            right_root < self.n,
            self.parent_of(left_root) == left_root,
            self.parent_of(right_root) == right_root,
        ensures left_root == right_root,
        decreases left_path.len() + right_path.len(),
    {
        assert(left_path.len() > 0);
        assert(right_path.len() > 0);
        assert(left_path[0] == start);
        assert(right_path[0] == start);
        assert(left_path[left_path.len() - 1] == left_root);
        assert(right_path[right_path.len() - 1] == right_root);
        if left_path.len() == 1 {
            assert(left_root == start);
            self.root_has_no_parent(left_root);
            if right_path.len() > 1 {
                self.parent_path_edge(right_path, start, right_root, 0);
                assert(right_path[0] == left_root);
                assert(self.parents.contains_key(left_root)) by {
                    self.parents.maps_to_implies_contains(left_root, right_path[1]);
                }
                assert(false);
            }
            assert(right_root == start);
        } else if right_path.len() == 1 {
            assert(right_root == start);
            self.root_has_no_parent(right_root);
            self.parent_path_edge(left_path, start, left_root, 0);
            assert(left_path[0] == right_root);
            assert(self.parents.contains_key(right_root)) by {
                self.parents.maps_to_implies_contains(right_root, left_path[1]);
            }
            assert(false);
        } else {
            let left_next = left_path[1];
            let right_next = right_path[1];
            self.parent_path_edge(left_path, start, left_root, 0);
            self.parent_path_edge(right_path, start, right_root, 0);
            assert(self.parents.maps_to(start, left_next));
            assert(self.parents.maps_to(start, right_next));
            self.parents.unique_value(start, left_next, right_next);
            assert(left_next < self.n);
            assert(right_next < self.n);
            let left_suffix = left_path.skip(1);
            let right_suffix = right_path.skip(1);
            self.parent_path_suffix(left_path, start, left_root);
            self.parent_path_suffix(right_path, start, right_root);
            self.terminal_paths_unique(
                left_suffix,
                right_suffix,
                left_next,
                left_root,
                right_root,
            );
        }
    }

    /// A parent forest has one terminal representative per element.
    pub proof fn rooted_at_unique(&self, element: usize, left_root: usize, right_root: usize)
        requires
            self.inv(),
            self.rooted_at(element, left_root),
            self.rooted_at(element, right_root),
        ensures left_root == right_root,
    {
        let left_path = choose|path: Seq<usize>| self.parent_path(path, element, left_root);
        let right_path = choose|path: Seq<usize>| self.parent_path(path, element, right_root);
        assert(element < self.n);
        assert(left_root < self.n);
        assert(right_root < self.n);
        self.terminal_paths_unique(
            left_path,
            right_path,
            element,
            left_root,
            right_root,
        );
    }

    /// Construct singleton classes from empty registries and an empty Budget allocation.
    pub fn new(n: usize, max_unions: u64) -> (classes: EquivalenceClass)
        ensures
            classes.n == n,
            classes.parents.entries@.len() == 0,
            classes.ranks.entries@.len() == 0,
            classes.budget.capacity == max_unions,
            classes.budget.allocated == 0,
            classes.budget.reserved == 0,
            classes.budget.pending_eviction == 0,
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
        ensures
            root < self.n,
            self.parent_of(root) == root,
            self.rooted_at(element, root),
    {
        let mut current = element;
        let mut parent = self.parent_value(current);
        let ghost mut path: Seq<usize> = Seq::empty().push(element);
        while parent != current
            invariant
                self.inv(),
                current < self.n,
                parent < self.n,
                parent == self.parent_of(current),
                parent != current ==> self.parents.maps_to(current, parent),
                self.parent_path(path, element, current),
            decreases self.budget.allocated - self.rank_of(current),
        {
            proof {
                self.rank_bounded(current);
                self.rank_bounded(parent);
                assert(self.rank_of(current) < self.rank_of(parent));
                let previous_path = path;
                path = path.push(parent);
                assert forall|index: int|
                    0 <= index < path.len() - 1 implies
                        #[trigger] self.parents.maps_to(path[index], path[index + 1]) by {
                    if index < previous_path.len() - 1 {
                        assert(path[index] == previous_path[index]);
                        assert(path[index + 1] == previous_path[index + 1]);
                    } else {
                        assert(index == previous_path.len() - 1);
                        assert(path[index] == current);
                        assert(path[index + 1] == parent);
                    }
                }
            }
            current = parent;
            parent = self.parent_value(current);
        }
        assert(self.reaches(element, current)) by {
            assert(self.parent_path(path, element, current));
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
            final(self).parents.entries@
                == old(self).parents.entries@.push((lower, higher)),
            final(self).parents.maps_to(lower, higher),
            final(self).parent_of(lower) == higher,
    {
        proof { self.root_has_no_parent(lower); }
        self.parents.register(lower, higher);
        proof { self.parent_mapping_determines_view(lower, higher); }
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
            final(self).parents.entries@
                == old(self).parents.entries@.push((lower, higher)),
            final(self).ranks.entries@
                == crate::primitives::resource_registry::without_key_sequence(
                    old(self).ranks.entries@,
                    higher,
                ).push((higher, (rank + 1) as u64)),
            final(self).parents.maps_to(lower, higher),
            final(self).parent_of(lower) == higher,
            final(self).rank_of(higher) == rank + 1,
    {
        proof {
            self.root_has_no_parent(lower);
            self.root_has_no_parent(higher);
        }
        self.parents.register(lower, higher);
        self.ranks.register(higher, rank + 1);
        proof { self.parent_mapping_determines_view(lower, higher); }
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
            final(self).budget.reserved == old(self).budget.reserved,
            final(self).budget.pending_eviction == old(self).budget.pending_eviction,
            merged == (old(self).budget.allocated < old(self).budget.capacity
                && !old(self).same_class(left, right)),
            merged ==> final(self).budget.allocated == old(self).budget.allocated + 1,
            !merged ==> final(self).budget.allocated == old(self).budget.allocated,
            !merged ==> *final(self) == *old(self),
            merged ==> exists|left_root: usize, right_root: usize| {
                &&& old(self).rooted_at(left, left_root)
                &&& old(self).rooted_at(right, right_root)
                &&& left_root != right_root
                &&& if old(self).rank_of(left_root) < old(self).rank_of(right_root) {
                    &&& final(self).parents.entries@
                        == old(self).parents.entries@.push((left_root, right_root))
                    &&& final(self).ranks.entries@ == old(self).ranks.entries@
                } else if old(self).rank_of(left_root) > old(self).rank_of(right_root) {
                    &&& final(self).parents.entries@
                        == old(self).parents.entries@.push((right_root, left_root))
                    &&& final(self).ranks.entries@ == old(self).ranks.entries@
                } else {
                    &&& final(self).parents.entries@
                        == old(self).parents.entries@.push((right_root, left_root))
                    &&& final(self).ranks.entries@
                        == crate::primitives::resource_registry::without_key_sequence(
                            old(self).ranks.entries@,
                            left_root,
                        ).push((left_root, (old(self).rank_of(left_root) + 1) as u64))
                }
            },
    {
        if self.budget.allocated >= self.budget.capacity {
            return false;
        }
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            assert(self.same_class(left, right)) by {
                assert(self.rooted_at(left, left_root));
                assert(self.rooted_at(right, left_root));
            }
            return false;
        }
        assert(!self.same_class(left, right)) by {
            if self.same_class(left, right) {
                let shared = choose|root: usize|
                    self.rooted_at(left, root) && self.rooted_at(right, root);
                self.rooted_at_unique(left, left_root, shared);
                self.rooted_at_unique(right, right_root, shared);
                assert(false);
            }
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
            assert(self.parents.maps_to(left_root, right_root));
        } else if left_rank > right_rank {
            self.attach_lower(right_root, left_root);
            assert(self.parents.maps_to(right_root, left_root));
        } else {
            assert(left_rank < self.budget.allocated);
            self.attach_equal(right_root, left_root, left_rank);
            assert(self.parents.maps_to(right_root, left_root));
        }
        assert(old(self).rooted_at(left, left_root));
        assert(old(self).rooted_at(right, right_root));
        assert(left_root != right_root);
        true
    }

    /// Whether two elements resolve to the same root.
    pub fn same(&self, left: usize, right: usize) -> (equivalent: bool)
        requires self.inv(), left < self.n, right < self.n,
        ensures
            equivalent == self.same_class(left, right),
            equivalent ==> exists|root: usize|
                root < self.n
                    && self.rooted_at(left, root)
                    && self.rooted_at(right, root),
            !equivalent ==> exists|left_root: usize, right_root: usize|
                left_root < self.n
                    && right_root < self.n
                    && left_root != right_root
                    && self.rooted_at(left, left_root)
                    && self.rooted_at(right, right_root),
    {
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            assert(exists|root: usize|
                root < self.n
                    && self.rooted_at(left, root)
                    && self.rooted_at(right, root)) by {
                assert(self.rooted_at(left, left_root));
                assert(self.rooted_at(right, left_root));
            }
            true
        } else {
            assert(!self.same_class(left, right)) by {
                if self.same_class(left, right) {
                    let shared = choose|root: usize|
                        self.rooted_at(left, root) && self.rooted_at(right, root);
                    self.rooted_at_unique(left, left_root, shared);
                    self.rooted_at_unique(right, right_root, shared);
                    assert(false);
                }
            }
            assert(exists|first: usize, second: usize|
                first < self.n
                    && second < self.n
                    && first != second
                    && self.rooted_at(left, first)
                    && self.rooted_at(right, second)) by {
                assert(self.rooted_at(left, left_root));
                assert(self.rooted_at(right, right_root));
            }
            false
        }
    }
}

}
