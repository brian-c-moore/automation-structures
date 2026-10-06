use automation_structures::primitives::backtracking_traversal::{
    BacktrackingTraversal, TraversalDomain,
};
use automation_structures::primitives::propagation_pass::{PropagationDomain, PropagationPass};
use automation_structures::value_eq::ValueEq;
use vstd::prelude::*;
verus! {
/// Owned byte value with its key and declared allocation charges.
pub type OwnedByteAdmission = (u64,(Vec<u8>,Vec<u64>));
/// Pure owned-byte content used by both native and external versioned Reduction checks.
pub struct AppendBytes { pub maximum: usize }
impl automation_structures::OwnedReductionOperation<Vec<u8>> for AppendBytes {
    type View = Seq<u8>;
    open spec fn observe(&self, value: Vec<u8>) -> Seq<u8> { value@ }
    open spec fn accepts(&self, previous: Vec<u8>, input: Vec<u8>) -> bool {
        previous@.len() + input@.len() <= self.maximum
    }
    open spec fn combined(&self, previous: Vec<u8>, input: Vec<u8>) -> Seq<u8> { previous@ + input@ }
    #[expect(clippy::indexing_slicing, reason = "each pure content-copy loop checks its index against the immutable input length")]
    #[expect(clippy::arithmetic_side_effects, reason = "both content-copy indices advance strictly below their input lengths")]
    fn try_combine(&self, previous: &Vec<u8>, input: &Vec<u8>) -> (combined: Result<Vec<u8>, automation_structures::OwnedReductionError>) {
        use automation_structures::OwnedReductionError;
        let length = match previous.len().checked_add(input.len()) {
            Some(length) => length,
            None => return Err(OwnedReductionError::Domain),
        };
        if length > self.maximum { return Err(OwnedReductionError::Domain); }
        let mut result = Vec::new();
        if result.try_reserve(length).is_err() { return Err(OwnedReductionError::StorageUnavailable); }
        let mut i = 0usize;
        while i < previous.len()
            invariant i <= previous.len(), result@ == previous@.subrange(0, i as int),
                previous@.len() + input@.len() <= self.maximum,
            decreases previous.len() - i,
        {
            result.push(previous[i]); i += 1;
        }
        i = 0;
        while i < input.len()
            invariant i <= input.len(), result@ == previous@ + input@.subrange(0, i as int),
                previous@.len() + input@.len() <= self.maximum,
            decreases input.len() - i,
        {
            result.push(input[i]); i += 1;
        }
        assert(result@ =~= previous@ + input@);
        Ok(result)
    }
}

/// Actual named owner retains a non-Copy ordered result and every preceding version.
pub fn non_copy_reduction_exports_exact_versions() {
    use automation_structures::VersionedReduction;
    let mut initial = Vec::new(); initial.push(7u8);
    if let Ok(mut owner) = VersionedReduction::try_new(initial, 2, AppendBytes { maximum: 3 }) {
        assert(owner.value_spec(0)@ == seq![7u8]);
        let mut first = Vec::new(); first.push(4u8);
        if let Ok(prepared) = owner.prepare(first) {
            let _version = prepared.commit(); assert(_version == 1);
            proof { owner.expose_versions(); }
            assert(owner.input_spec(1) == Some(first));
            proof {
                use automation_structures::OwnedReductionOperation;
                assert(owner.operator_spec().observe(owner.value_spec(1))
                    == owner.operator_spec().combined(owner.value_spec(0), first));
            }
            assert(owner.value_spec(1)@ == seq![7u8, 4u8]);
            let ghost before = owner;
            let mut large = Vec::new(); large.push(1u8); large.push(2u8);
            match owner.prepare(large) {
                Ok(prepared) => { assert(false); let _input = prepared.cancel(); },
                Err((_reason, _returned)) => {
                    assert(_returned == large);
                    assert(_reason == automation_structures::OwnedReductionError::Domain
                        || _reason == automation_structures::OwnedReductionError::StorageUnavailable);
                },
            }
            assert(owner.same_state(before));
            proof { owner.expose_state_frame(&before); }
            let mut next = Vec::new(); next.push(3u8);
            if let Ok(prepared) = owner.prepare(next) {
                let _version = prepared.commit(); assert(_version == 2);
                proof { owner.expose_versions(); }
                assert(owner.value_spec(0)@ == seq![7u8]);
                assert(owner.value_spec(1)@ == seq![7u8, 4u8]);
                assert(owner.value_spec(2)@ == seq![7u8, 4u8, 3u8]);
                let _observed = owner.version(1);
                assert(_observed is Some && _observed->Some_0@ == seq![7u8, 4u8]);
            }
        }
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Bit { pub set: bool }
impl ValueEq for Bit {
    fn value_eq(&self, other: &Self) -> (equal: bool) { self.set == other.set }
}
#[derive(Clone,Copy,Debug)]
pub struct NeighborComplement { pub allowed: usize }
impl PropagationDomain<Bit> for NeighborComplement {
    open spec fn contains(&self, _value: Bit) -> bool { true }
    open spec fn accepts(&self, _edges: Seq<(usize,usize)>, snapshot: Seq<Bit>, node: usize) -> bool {
        snapshot.len() == 2 && node < self.allowed
    }
    open spec fn combined(&self, _edges: Seq<(usize,usize)>, snapshot: Seq<Bit>, node: usize) -> Bit {
        Bit { set: !snapshot[if node == 0 { 1int } else { 0int }].set }
    }
    fn accepts_exec(&self, _edges: &Vec<(usize,usize)>, snapshot: &Vec<Bit>, node: usize) -> (yes: bool) {
        snapshot.len() == 2 && node < self.allowed
    }
    #[expect(clippy::indexing_slicing, reason = "PropagationDomain::combine requires accepts, which establishes the snapshot length is exactly two")]
    fn combine(&self, _edges: &Vec<(usize,usize)>, snapshot: &Vec<Bit>, node: usize) -> (value: Bit) {
        Bit { set: !snapshot[if node == 0 { 1 } else { 0 }].set }
    }
}
#[derive(Clone,Copy,Debug)]
pub struct Toggle { pub choices: u64 }
impl TraversalDomain<Bit> for Toggle {
    type Delta = bool;
    open spec fn branches(&self) -> u64 { self.choices }
    open spec fn valid_aux(&self, _value: Bit) -> bool { true }
    open spec fn valid_delta(&self, delta: bool) -> bool { delta }
    open spec fn mutated(&self, value: Bit, _delta: bool) -> Bit { Bit { set: !value.set } }
    open spec fn undone(&self, value: Bit, _delta: bool) -> Bit { Bit { set: !value.set } }
    fn branch_count(&self) -> (count: u64) { self.choices }
    fn valid_delta_exec(&self, delta: bool) -> (yes: bool) { delta }
    fn mutate(&self, value: Bit, _delta: bool) -> (result: Bit) { Bit { set: !value.set } }
    fn undo(&self, value: Bit, _delta: bool) -> (result: Bit) { Bit { set: !value.set } }
    proof fn inverse(&self, value: Bit, delta: bool) {}
}

pub fn generic_snapshot_is_shared() {
    let mut values=Vec::new(); values.push(Bit{set:false}); values.push(Bit{set:false});
    if let Ok(mut p)=PropagationPass::try_new(2,3,NeighborComplement{allowed:2},Vec::new(),values) {
        p.start_round();
        let _first=p.try_update_node(0); assert(_first);
        let _second=p.try_update_node(1); assert(_second);
        assert(p.values@ == seq![Bit{set:true},Bit{set:true}]);
        let ghost before=p;
        let _repeated=p.try_update_node(0); assert(!_repeated); assert(p == before);
        assert(p.all_updated()); p.end_round(); assert(p.iteration == 1 && p.changed);
    }
}
pub fn generic_domain_refusal_stutters() {
    let mut values=Vec::new(); values.push(Bit{set:false}); values.push(Bit{set:false});
    if let Ok(mut p)=PropagationPass::try_new(2,3,NeighborComplement{allowed:1},Vec::new(),values) {
        p.start_round(); let ghost before=p;
        let _accepted=p.try_update_node(1); assert(!_accepted); assert(p == before);
    }
}
pub fn generic_inverse_restores_original(additional: usize) {
    if let Ok(mut t)=BacktrackingTraversal::try_new(Toggle{choices:2},1,Bit{set:false}) {
        t.descend(2,true); assert(t.aux == Bit{set:true});
        assert(t.is_leaf()); assert(!t.visited_contains(t.path@));
        let ghost before=t;
        let _reserved=t.try_reserve_visits(additional); assert(t.same_state(&before));
        let visit=t.try_visit();
        if visit.is_ok() { assert(t.visited.len() == 1); assert(t.visited@[0]@ == seq![2u64]); }
        else { assert(t.same_state(&before)); }
        t.ascend(); assert(t.aux == Bit{set:false} && t.path.len() == 0 && t.ledger.len() == 0);
    }
}

/// Owned batch contracts cross the package boundary without copying payloads.
pub fn owned_batch_commit_exports_exact_membership_and_dimension_charges(items: Vec<OwnedByteAdmission>) {
    use automation_structures::{TypedAllocation, UnrestrictedAllocation};
    let mut capacities = Vec::new(); capacities.push(4u64); capacities.push(10u64);
    if let Ok(mut allocation) = TypedAllocation::try_new(&capacities, UnrestrictedAllocation) {
        match allocation.prepare_batch(items) {
            Ok(prepared) => {
                prepared.commit();
                assert(allocation.entries_spec() == items@);
                assert(allocation.budgets_spec()[0].1.allocated as int
                    == automation_structures::compositions::allocation_snapshot::typed_charge_to(items@, items@.len() as int, 0));
                assert(allocation.budgets_spec()[1].1.allocated as int
                    == automation_structures::compositions::allocation_snapshot::typed_charge_to(items@, items@.len() as int, 1));
                let _sealed = allocation.seal(); assert(_sealed.entries_spec() == items@);
            },
            Err(_refused) => {
                assert(_refused.items == items);
                assert(allocation.entries_spec().len() == 0);
                assert(allocation.budgets_spec()[0].1.allocated == 0);
                assert(allocation.budgets_spec()[1].1.allocated == 0);
            },
        }
    }
}

/// Batch cancellation returns every original representation and leaves all owners fixed.
pub fn owned_batch_cancellation_returns_original_inputs(items: Vec<OwnedByteAdmission>) {
    use automation_structures::{TypedAllocation, UnrestrictedAllocation};
    let mut capacities = Vec::new(); capacities.push(4u64); capacities.push(10u64);
    let mut allocation = match TypedAllocation::try_new(&capacities, UnrestrictedAllocation) {
        Ok(allocation) => allocation, Err(_) => return,
    };
    if let Ok(prepared) = allocation.prepare_batch(items) {
        let _returned = prepared.cancel(); assert(_returned.items@ == items@);
        assert(allocation.entries_spec().len() == 0);
        assert(allocation.budgets_spec()[0].1.allocated == 0);
        assert(allocation.budgets_spec()[1].1.allocated == 0);
    }
}

/// Typed owned admission exports unchanged refusal and all coupled Budget updates.
pub fn typed_entry_preparation_couples_membership_and_every_budget() {
    use automation_structures::{TypedAllocation, UnrestrictedAllocation};
    let mut capacities = Vec::new(); capacities.push(2u64); capacities.push(2u64); capacities.push(1u64);
    if let Ok(mut allocation) = TypedAllocation::try_new(&capacities, UnrestrictedAllocation) {
        let mut payload = Vec::new(); payload.push(99u64);
        let mut charges = Vec::new(); charges.push(1u64); charges.push(2u64); charges.push(1u64);
        if let Ok(prepared) = allocation.prepare(7u64, payload, charges) {
            prepared.commit();
            let _members = allocation.len(); assert(_members == 1);
            let _first = allocation.budget(0); assert(_first == Some((2u64, 1u64)));
            let _middle = allocation.budget(1); assert(_middle == Some((2u64, 2u64)));
            let _last = allocation.budget(2); assert(_last == Some((1u64, 1u64)));
            assert(!allocation.contains_spec(8u64));
            let ghost entries = allocation.entries_spec(); let ghost budgets = allocation.budgets_spec();
            let mut next_payload = Vec::new(); next_payload.push(4u64);
            let mut next_charges = Vec::new(); next_charges.push(1u64); next_charges.push(1u64); next_charges.push(0u64);
            match allocation.prepare(8u64, next_payload, next_charges) {
                Ok(prepared) => { let _ = prepared.cancel(); assert(false); },
                Err(_refused) => {
                    assert(_refused.reason == Some(automation_structures::TypedAllocationError::Capacity));
                    assert(_refused.dimension == Some(1usize));
                    assert(_refused.key == 8 && _refused.value@ == seq![4u64]);
                },
            }
            assert(allocation.entries_spec() == entries && allocation.budgets_spec() == budgets);
            let sealed = allocation.seal();
            assert(sealed.entries_spec() == entries && sealed.budgets_spec() == budgets);
            let _fixed = sealed.budget(1); assert(_fixed == Some((2u64, 2u64)));
        }
    }
}

/// Borrowed batch entry points export their retained exact fold contracts.
pub fn borrowed_batch_fold_contracts(items: &[u64])
    requires items@.len() <= 1_000_000_000,
        forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
{
    use automation_structures::compositions::reduction::{reduce_max, reduce_sum};
    let _sum = reduce_sum(items);
    let _maximum = reduce_max(items);
    assert(_sum == automation_structures::compositions::reduction::fold_to(
        items@, items@.len() as int, 0, |a: u64, b: u64| (a + b) as u64));
    assert(_maximum == automation_structures::compositions::reduction::fold_to(
        items@, items@.len() as int, 0, |a: u64, b: u64| if a > b { a } else { b }));
}

/// Pure edge-weight policy supplied by a downstream domain.
pub struct MinimumWeight { pub minimum: u64 }
impl automation_structures::primitives::resource_registry::RegistryPredicate<(usize, usize, u64), ()>
    for MinimumWeight {
    open spec fn selected(&self, key: (usize, usize, u64), _value: ()) -> bool {
        key.2 >= self.minimum
    }
    fn test(&self, key: &(usize, usize, u64), _value: &()) -> (selected: bool) {
        key.2 >= self.minimum
    }
}

/// Checked graph contracts expose weighted counts and unchanged borrow observations.
pub fn graph_queries_preserve_the_weighted_owner() {
    use automation_structures::{EdgeDirection, RelationshipGraph};
    let mut graph = RelationshipGraph::new(4, 10);
    let _first = graph.add_edge(0, 2, 7); assert(_first == Ok(true));
    let _second = graph.add_edge(0, 1, 3); assert(_second == Ok(true));
    let _third = graph.add_edge(0, 2, 9); assert(_third == Ok(true));
    assert(graph.bindings() == seq![((0usize,2usize,7u64),()),
        ((0usize,1usize,3u64),()), ((0usize,2usize,9u64),())]);
    let ghost before = graph.bindings();
    let _duplicate = graph.add_edge(0, 2, 7);
    assert(_duplicate == Ok(false)); assert(graph.bindings() == before);
    let _refused = graph.add_edge(4, 2, 1);
    assert(_refused is Err); assert(graph.bindings() == before);
    let policy = MinimumWeight { minimum: 7 };
    let view = graph.frozen_adjacency();
    let _length = view.edge_count(); assert(_length == 3);
    let _authored = view.edge(1); assert(_authored == Some((0usize,1usize,3u64)));
    let _beyond = view.edge(3); assert(_beyond is None);
    let _outgoing = view.filtered_degree(0, EdgeDirection::Outgoing, &policy);
    let _incoming = view.filtered_degree(2, EdgeDirection::Incoming, &policy);
    proof { reveal_with_fuel(automation_structures::compositions::relationship_graph::incident_count, 4); }
    assert(_outgoing == Ok(2usize)); assert(_incoming == Ok(2usize));
    let _unknown = view.filtered_degree(4, EdgeDirection::Outgoing, &policy);
    assert(_unknown == Err(automation_structures::RelationshipGraphError::NodeOutOfRange));
    assert(graph.bindings() == before);
}

/// Whole-row publication and a middle-column refusal hold across the crate boundary.
pub fn reduction_row_commits_every_column_or_none() {
    use automation_structures::{CheckedSignedAdd, ReductionColumns, ReductionRowError};
    let mut operators = Vec::new();
    operators.push(CheckedSignedAdd); operators.push(CheckedSignedAdd); operators.push(CheckedSignedAdd);
    if let Ok(mut columns) = ReductionColumns::try_new(&operators, 3) {
        assert(columns.columns_spec()[0].1.result_spec() == 0);
        assert(columns.columns_spec()[1].1.result_spec() == 0);
        assert(columns.columns_spec()[0].1.operator_spec() == CheckedSignedAdd);
        assert(columns.columns_spec()[1].1.operator_spec() == CheckedSignedAdd);
        let mut first = Vec::new(); first.push(7i64); first.push(i64::MAX); first.push(-4i64);
        if let Ok(row) = columns.prepare_row(&first) {
            row.commit();
            assert(columns.columns_spec()[0].1.result_spec() == 7);
            assert(columns.columns_spec()[1].1.result_spec() == i64::MAX);
            assert(columns.columns_spec()[2].1.result_spec() == -4);
            let _count = columns.column_processed(2); assert(_count == Some(1usize));
            let ghost before = columns.columns_spec();
            let mut refused = Vec::new(); refused.push(1i64); refused.push(1i64); refused.push(1i64);
            match columns.prepare_row(&refused) {
                Ok(row) => { assert(false); row.cancel(); },
                Err(ReductionRowError::Column { column: _column, reason: _reason }) => {
                    assert(_column == 1);
                    assert(_reason == automation_structures::RecordRefusal::Domain);
                },
                Err(ReductionRowError::StorageUnavailable) => {},
                Err(_) => { assert(false); },
            }
            assert(columns.columns_spec() == before);
            let _first = columns.column_result(0); assert(_first == Some(7i64));
            let _third = columns.column_result(2); assert(_third == Some(-4i64));
        }
    }
}
}
