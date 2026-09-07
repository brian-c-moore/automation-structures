//! External Verus consumer used by the cross-crate proof API gate.

use automation_structures::Buffer;
use automation_structures::connectives::{counter, ordering_pass};
use automation_structures::primitives::{budget, resource_registry};
use vstd::prelude::*;

verus! {

/// The external consumer receives the actual ordered permutation, with its contract.
pub fn finite_ordering_is_constructible()
    -> (result: Result<Vec<usize>, automation_structures::connectives::ordering_pass::ArrangementError>)
    ensures result is Ok ==> result.unwrap()@ == seq![1usize, 0usize, 2usize],
{
    use automation_structures::connectives::ordering_pass::{try_arrange_indices, SignedRowOrder};
    use automation_structures::primitives::audit_sink::NullableSigned::Value;
    let mut values = Vec::new(); values.push(Value(2)); values.push(Value(3)); values.push(Value(1));
    let order = SignedRowOrder { values: &values, descending: true, nulls_first: false };
    let result = try_arrange_indices(3, &order);
    if let Ok(ref positions) = result {
        assert(positions@[0] < 3 && positions@[1] < 3 && positions@[2] < 3);
        assert(positions@[0] != positions@[1] && positions@[0] != positions@[2] && positions@[1] != positions@[2]);
        assert(positions@ == seq![1usize, 0usize, 2usize]);
    }
    result
}



/// An external client borrows the actual retained AuditSink and mutates only that owner.
pub fn indexed_summary_owner_is_borrowable() -> (result: Option<i64>)
    ensures result is Some ==> result.unwrap() == 7,
{
    use automation_structures::primitives::audit_sink::{AuditSink, CheckedSignedAdd};
    let mut registry = resource_registry::ResourceRegistry::new_indexed();
    let mut bytes = Vec::new(); bytes.push(17u8);
    let fold = AuditSink::with_summary(2, CheckedSignedAdd);
    let inserted = registry.try_register_key(resource_registry::ByteKey::from_bytes(bytes), fold);
    if inserted.is_err() { return None; }
    let mut probe = Vec::new(); probe.push(17u8);
    {
        let borrowed = registry.lookup_query_mut(&probe.as_slice());
        match borrowed {
            Some(value) => {
                assert(value.chain_valid());
                let accepted = value.record_typed(7i64);
                assert(accepted);
            }
            None => { assert(false); }
        }
    }
    match registry.lookup_query(&probe.as_slice()) {
        Some(value) => { let carry = value.carry(); assert(carry == 7); Some(carry) }
        None => { assert(false); None }
    }
}



/// The external proof consumer can retain a typed nullable summary without a copied reducer.
pub fn nullable_summary_is_constructible() -> (fold:
    automation_structures::primitives::audit_sink::AuditSink<
        automation_structures::primitives::audit_sink::CheckedSignedSumCount,
        automation_structures::primitives::audit_sink::SummaryHistory<
            automation_structures::primitives::audit_sink::NullableSigned,
            automation_structures::primitives::audit_sink::SignedSumCount>>)
    ensures fold.chain_valid(), fold.history_spec().len() == 3,
        fold.last_hash.sum == -4i64, fold.last_hash.count == 2u64,
{
    use automation_structures::primitives::audit_sink::{AuditSink, CheckedSignedSumCount, NullableSigned};
    let mut fold = AuditSink::with_summary(3, CheckedSignedSumCount);
    let first = fold.record_typed(NullableSigned::Value(7));
    assert(first);
    let second = fold.record_typed(NullableSigned::Missing);
    assert(second);
    let third = fold.record_typed(NullableSigned::Value(-11));
    assert(third);
    let refused = fold.record_typed(NullableSigned::Value(1));
    assert(!refused);
    fold
}



/// Connective and primitive relations remain usable across the crate boundary.
pub proof fn structure_relations_are_importable()
    ensures
        counter::nonnegative(0),
        ordering_pass::strictly_before(0, 1),
        budget::budget_safety(1, 0, 0, 0),
        resource_registry::unique_keys(Seq::<u64>::empty()),
{
}

/// Equal encoded contents from distinct allocations share one canonical registry identity.
pub fn byte_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<resource_registry::ByteKey, u64>)
    ensures registry.unique_identities(), registry.entries@.len() == 1,
        registry.maps_identity(seq![1u8, 0u8, 2u8], 22),
{
    let mut registry = resource_registry::ResourceRegistry::new();
    let mut bytes = Vec::new();
    bytes.push(1u8); bytes.push(0u8); bytes.push(2u8);
    registry.register_key(resource_registry::ByteKey::from_bytes(bytes), 11u64);
    let mut replacement = Vec::new();
    replacement.push(1u8); replacement.push(0u8); replacement.push(2u8);
    let key = resource_registry::ByteKey::from_bytes(replacement);
    assert(resource_registry::KeyIdentity::identity(&key) == seq![1u8, 0u8, 2u8]);
    proof { resource_registry::without_identity_to_remove_unique(registry.entries@, key, 1, 0); }
    registry.register_key(key, 22u64);
    assert(registry.maps_key(key, 22u64));
    assert(registry.maps_identity(seq![1u8, 0u8, 2u8], 22u64));
    let mut query_bytes = Vec::new();
    query_bytes.push(1u8); query_bytes.push(0u8); query_bytes.push(2u8);
    let query = query_bytes.as_slice();
    match registry.lookup_query(&query) {
        Some(value) => { assert(*value == 22); }
        None => { assert(false); }
    }
    registry
}

/// A key whose ownership cannot be copied into a rebuilt registry.
pub struct OwnedRegistryKey {
    /// Exact scalar identity for this move-only witness, not a hash of a domain key.
    pub code: u64,
}

impl resource_registry::RegistryKey for OwnedRegistryKey {
    fn value_eq(&self, other: &Self) -> (equal: bool)
        ensures equal == (*self == *other),
    {
        self.code == other.code
    }
}

/// Owned entries and borrowed observations preserve the same unique-key contract.
pub fn owned_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<OwnedRegistryKey, Vec<u64>>)
    ensures
        registry.unique_mapping(),
        registry.entries@.len() == 1,
        registry.contains_key(OwnedRegistryKey { code: 7 }),
{
    let mut registry = resource_registry::ResourceRegistry::new();
    let mut first = Vec::new();
    first.push(11u64);
    registry.register(OwnedRegistryKey { code: 7 }, first);
    let observed = registry.lookup_ref(&OwnedRegistryKey { code: 7 });
    match observed {
        Some(value) => { assert(value@ == seq![11u64]); }
        None => { assert(false); }
    }
    let mut replacement = Vec::new();
    replacement.push(22u64);
    proof {
        resource_registry::without_key_to_remove_unique(
            registry.entries@, OwnedRegistryKey { code: 7 }, 1, 0);
    }
    registry.register(OwnedRegistryKey { code: 7 }, replacement);
    assert(registry.entries@.len() == 1);
    registry.register(OwnedRegistryKey { code: 8 }, Vec::new());
    assert(registry.entries@.len() == 2);
    proof {
        resource_registry::without_key_to_remove_unique(
            registry.entries@, OwnedRegistryKey { code: 8 }, 2, 1);
    }
    registry.deregister(OwnedRegistryKey { code: 8 });
    let observed = registry.lookup_ref(&OwnedRegistryKey { code: 7 });
    match observed {
        Some(value) => { assert(value@ == seq![22u64]); }
        None => { assert(false); }
    }
    registry
}

/// A downstream proof crate can instantiate the registry with a composition key.
pub fn typed_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<(usize, usize, u64), ()>)
    ensures registry.entries@.len() == 0,
{
    resource_registry::ResourceRegistry::new()
}

/// A downstream proof crate can construct and update the checked Buffer facade.
pub fn checked_buffer_is_constructible() -> (buffer: Buffer<u64>)
    ensures buffer.well_formed(), buffer.distinct(),
{
    let mut buffer = Buffer::new(2);
    let accepted = buffer.push_unique(7);
    assert(accepted);
    buffer
}

/// Preallocation and FIFO ownership compose across the published carrier boundary.
pub fn reserved_carrier_fifo(value: u64)
    -> (result: Result<Option<u64>, std::collections::TryReserveError>)
    ensures result is Ok ==> result->Ok_0 == Some(value),
{
    let mut buffer = automation_structures::connectives::buffer::Buffer::try_new(1)?;
    let _accepted = buffer.push(value);
    assert(_accepted is Ok);
    Ok(buffer.pop())
}

/// The checked facade exposes the same fallible construction without a second owner.
pub fn reserved_checked_buffer()
    -> (result: Result<Buffer<u64>, std::collections::TryReserveError>)
    ensures
        result is Ok ==> result->Ok_0.well_formed(),
        result is Ok ==> result->Ok_0.retained() == seq![7u64],
{
    let mut buffer = Buffer::try_new(1)?;
    let accepted = buffer.push_unique(7);
    assert(accepted);
    Ok(buffer)
}

}

verus! {
/// Reservation preserves an owned mapping on both outcomes before graph/node admission.
pub fn linear_registry_reservation_frames_owned_bindings(additional: usize) {
    use automation_structures::primitives::resource_registry::ResourceRegistry;
    let mut owner = ResourceRegistry::<u64, Vec<u8>>::new();
    let mut payload = Vec::new(); payload.push(3u8); payload.push(1u8);
    owner.register(7, payload);
    let ghost before = owner.entries@;
    let reserved = owner.try_reserve_entries(additional);
    assert(owner.entries@ == before);
    assert(owner.unique_identities());
    assert(owner.entries@[0].0 == 7);
    assert(owner.entries@[0].1@ == seq![3u8, 1u8]);
    if let Ok(()) = reserved {
        owner.register(2, Vec::<u8>::new());
        assert(owner.entries@.len() == 2);
        assert(owner.entries@[0] == before[0]);
    }
}
}

verus! {
/// A reserved selection instance has the same canonical score domain and tie behavior.
pub fn fallible_selection_is_constructible() {
    use automation_structures::primitives::competitive_selection::CompetitiveSelectionHard;
    if let Ok(mut owner) = CompetitiveSelectionHard::try_new(2) {
        assert(owner.scores@ == seq![0u64, 0u64]);
        owner.update_score(1, 1);
        assert(owner.scores@ == seq![0u64,1u64]);
        owner.evaluate();
        proof {
            assert(owner.winner_optimality());
            if let Some(winner) = owner.allocation {
                assert(winner < 2);
                assert(owner.scores@[1] <= owner.scores@[winner as int]);
                if winner == 0 { assert(false); }
            }
        }
        assert(owner.allocation == Some(1usize));
    }
}
/// State allocation cannot alter the dependency relation or admit a blocked start.
pub fn fallible_step_graph_is_constructible() {
    use automation_structures::modalities::step_graph::StepGraph;
    let mut edges = Vec::new(); edges.push((0usize, 1usize));
    if let Ok(mut owner) = StepGraph::try_new(2, edges) {
        assert(owner.edges@ == seq![(0usize,1usize)]);
        assert(StepGraph::has_predecessor_in(owner.edges@,1)) by {
            assert(owner.edges@[0].1 == 1);
        }
        assert(owner.nstate@[1] == automation_structures::StepState::NotReady);
        let blocked = owner.start_running(1); assert(!blocked);
        let started = owner.start_running(0); assert(started);
        let completed = owner.complete_node(0); assert(completed);
        let ready = owner.become_ready(1); assert(ready);
    }
}
/// Effect reservation preserves the actual assignments; actuation still records the selected resource.
pub fn fallible_actuation_is_constructible() {
    use automation_structures::primitives::actuation_pass::ActuationPass;
    let mut assignments = Vec::new(); assignments.push(Some(7u64));
    if let Ok(mut owner) = ActuationPass::try_new(assignments, 1) {
        assert(owner.effects@ == seq![Option::<u64>::None]);
        owner.actuate(0); assert(owner.effects@ == seq![Some(7u64)]);
        owner.finish(); assert(owner.complete);
    }
}
}


verus! {
/// Reserved scalar history still records exactly the completed sequence.
pub fn reserved_sequence_is_constructible() {
    use automation_structures::modalities::sequential::Sequential;
    if let Ok(mut s) = Sequential::try_new(1, 10, 0) {
        let begun = s.begin_step(); assert(begun);
        let done = s.complete_step(7); assert(done);
        assert(s.history@ == seq![7u64]);
    }
}
/// A reserved fork cannot cross its barrier before completion.
pub fn reserved_fork_is_constructible() {
    use automation_structures::modalities::fork_join::ForkJoin;
    if let Ok(mut s) = ForkJoin::try_new(1, 10, 0) {
        let early = s.barrier(); assert(!early);
        let start = s.start_worker(0); assert(start);
        let done = s.complete_worker(0,7); assert(done);
        let joined = s.barrier(); assert(joined);
        let output = s.produce_output(); assert(output);
        assert(s.output_snapshot@ == seq![7u64]);
    }
}
/// Reservation cannot add an audit record or change its carried result.
pub fn reserved_audit_frames_chain(additional: usize) {
    use automation_structures::primitives::audit_sink::AuditSink;
    let mut s = AuditSink::new(3);
    let accepted = s.record(7); assert(accepted);
    let ghost before = s;
    let _result = s.try_reserve_records(additional);
    assert(s.history_spec() == before.history_spec());
    assert(s.last_hash == before.last_hash && s.operator == before.operator
        && s.max_log_len == before.max_log_len);
}
/// A clock observation neither grants work nor changes the window anchor.
pub fn observed_clock_frames_rate_ledger() {
    use automation_structures::compositions::rate_limit::RateLimit;
    let mut r = RateLimit::new(2,5,100);
    let accepted = r.advance_clock_to(27); assert(accepted);
    assert(r.clock == 27 && r.window_start == 0 && r.budget.allocated == 0);
    let ghost before = r;
    let backwards = r.advance_clock_to(26); assert(!backwards); assert(r == before);
}
}

mod domains;
