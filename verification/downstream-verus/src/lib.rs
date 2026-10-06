//! External Verus consumer used by the cross-crate proof API gate.

use automation_structures::Buffer;
use automation_structures::primitives::resource_registry;
use vstd::prelude::*;

verus! {

/// Dynamic admission retains exact original custody; a visit exports stable level order.
pub fn dynamic_candidate_profile_exports_admission_and_visit<C, T>(
    owner: &mut automation_structures::CandidateTraversal<C, T>, value: T,
)
    requires old(owner).inv(),
{
    let ghost context = owner.context_spec();
    let ghost originals = owner.candidates_spec();
    match owner.admit(None, value, u64::MAX, 0) {
        Ok(id) => {
            assert(owner.inv() && owner.candidates_spec() == originals.push((id.index_spec(), value)));
            assert(!owner.visited_spec(id.index_spec()));
            let _ = id;
        },
        Err((_, returned)) => { assert(returned == value && owner.candidates_spec() == originals); let _ = returned; },
    }
    let ghost before = *owner;
    match owner.step() {
        Ok(Some(id)) => { assert(owner.visited_spec(id.index_spec())); assert(owner.pending_spec() == before.pending_spec() - 1); let _ = id; },
        Ok(None) => { assert(owner.pending_spec() == 0); },
        Err(_) => { assert(*owner == before); },
    }
    assert(owner.context_spec() == context);
}

/// Consuming completion proves the real frontier empty and retains all typed candidates.
pub fn dynamic_candidate_profile_exports_completion<C, T>(owner: automation_structures::CandidateTraversal<C, T>)
    requires owner.inv(),
{
    match owner.finish() {
        Ok(done) => {
            assert(done.inv());
            proof { done.expose_complete(); }
            assert(done.profile_spec().frontier_spec().len() == 0);
            assert(done.profile_spec().candidates_spec() == owner.candidates_spec());
            let _ = done;
        },
        Err(original) => { assert(original == owner); let _ = original; },
    }
}

/// Fallible construction retains the existing star's exact initialization contract.
pub fn admitted_traversal_storage() {
    if let Ok(engine) = automation_structures::compositions::traversal_engine::TraversalEngine::try_new(4, 0, 8) {
        assert(engine.inv() && engine.queue.values@ == seq![0usize]);
        assert(engine.accepted.accumulated@.len() == 0 && engine.budget.allocated == 0);
        let _ = engine;
    }
}

/// The existing forest actions preserve both directions of reachable edge correspondence.
pub fn admitted_hierarchy_storage_has_complete_parent_edges() {
    if let Ok(mut hierarchy) = automation_structures::primitives::quality_hierarchy::QualityHierarchy::try_new(4, u64::MAX) {
            hierarchy.set_node_properties(0, u64::MAX, 0);
            hierarchy.set_node_properties(1, 2, 0);
            hierarchy.set_node_properties(2, 1, 0);
            hierarchy.add_child(0, 1);
            hierarchy.add_child(1, 2);
            assert(hierarchy.parent_has_edge());
            assert(hierarchy.parent@[1] == 0 && hierarchy.parent@[2] == 1);
            proof { hierarchy.expose_parent_edge(1); hierarchy.expose_parent_edge(2); }
            assert(hierarchy.edge_exists(0, 1) && hierarchy.edge_exists(1, 2));
            assert(hierarchy.parent@[3] == 4 && hierarchy.cost@[2] == 0);
    }
}

/// A canonical step preserves the frozen context and exports its exact progress.
pub fn finite_rooted_profile_exports_nonbinding_step_and_completion(
    profile: &mut automation_structures::RootedTraversal,
)
    requires old(profile).inv(),
{
    let ghost context = profile.hierarchy_spec();
    let ghost before = profile.considered_spec();
    let node = profile.step();
    assert(profile.hierarchy_spec() == context && profile.inv());
    if let Some(node) = node {
        assert(profile.considered_spec() == before + 1);
        assert(profile.discovered_spec(node));
        let _ = node;
    } else {
        assert(profile.frontier_spec().len() == 0);
        assert(profile.considered_spec() == context.num_nodes);
    }
}

/// Completion consumes the canonical profile and refuses every unfinished frontier.
pub fn finite_rooted_profile_exports_seal(profile: automation_structures::RootedTraversal)
    requires profile.inv(),
{
    match profile.finish() {
        Ok(done) => {
            proof {
                done.expose_complete();
                assert forall|node: usize| node < profile.hierarchy_spec().num_nodes implies
                    #[trigger] done.profile_spec().discovered_spec(node) by {};
            }
            let _ = done;
        },
        Err(original) => { assert(original == profile && profile.frontier_spec().len() > 0); let _ = original; },
    }
}

/// Immutable signed domain content for the shared named projected fold.
pub struct SignedInputs { pub values: Vec<i64> }
impl automation_structures::ReductionProjection<automation_structures::CheckedSignedAdd> for SignedInputs {
    open spec fn domain_len(&self) -> nat { self.values@.len() }
    open spec fn item_spec(&self, position: int) -> i64 { self.values@[position] }
    fn len(&self) -> (length: usize) { self.values.len() }
    #[expect(clippy::indexing_slicing, reason = "ReductionProjection requires position inside this immutable domain before item is called")]
    fn item(&self, position: usize) -> (item: i64) { self.values[position] }
}

/// External construction proves ordered completion and the exact first-refused prefix.
pub fn named_projected_reduction_is_constructible() {
    use automation_structures::{CheckedSignedAdd, IncrementalReduction};
    reveal_with_fuel(automation_structures::compositions::reduction::projected_fold_to, 4);
    reveal_with_fuel(automation_structures::compositions::reduction::projected_prefix_admitted, 4);
    let mut values = Vec::new(); values.push(7i64); values.push(-4i64);
    let source = SignedInputs { values };
    match IncrementalReduction::try_from_projection(&source, CheckedSignedAdd) {
        Ok(_fold) => { assert(_fold.processed_spec() == 2 && _fold.result_spec() == 3i64); },
        Err(_) => { assert(false); },
    }
    let mut values = Vec::new(); values.push(i64::MAX); values.push(1i64); values.push(-1i64);
    let source = SignedInputs { values };
    match IncrementalReduction::try_from_projection(&source, CheckedSignedAdd) {
        Err((_reason, _fold)) => {
            assert(_reason == automation_structures::RecordRefusal::Domain);
            assert(_fold.processed_spec() == 1 && _fold.result_spec() == i64::MAX);
        },
        Ok(_) => { assert(false); },
    }
}

/// Pure size content for the external Buffer query control.
pub struct EncodedSize;
impl automation_structures::BufferSizeProjection<usize> for EncodedSize {
    open spec fn size_spec(&self, value: usize) -> usize { value }
    fn size(&self, value: &usize) -> (size: usize) { *value }
}

/// The exported owner query proves exact totals and overflow without changing FIFO state.
pub fn buffer_projected_size_is_constructible() -> (buffer: Buffer<usize>)
    ensures buffer.well_formed(), buffer.retained() == seq![usize::MAX, 0usize, 1usize],
{
    reveal_with_fuel(automation_structures::connectives::buffer::projected_size_to, 4);
    let mut buffer = Buffer::new(3);
    let _empty = buffer.projected_size(&EncodedSize);
    assert(_empty == Ok(0usize));
    let _pushed = buffer.push(usize::MAX); assert(_pushed is Ok);
    let _pushed = buffer.push(0usize); assert(_pushed is Ok);
    let _exact = buffer.projected_size(&EncodedSize);
    assert(_exact == Ok(usize::MAX));
    let _pushed = buffer.push(1usize); assert(_pushed is Ok);
    let ghost before = buffer;
    let _overflow = buffer.projected_size(&EncodedSize);
    assert(_overflow == Err(automation_structures::BufferSizeError::Overflow));
    assert(buffer == before);
    buffer
}

/// Named preparations bind the unchanged owner, exact commit and typed refusal across crates.
pub fn named_prepared_reduction_is_constructible() -> (fold:
    automation_structures::IncrementalReduction<automation_structures::CheckedSignedAdd>)
    ensures fold.inv(), fold.processed_spec() == 2, fold.result_spec() == 3i64,
{
    use automation_structures::{CheckedSignedAdd, IncrementalReduction};
    let mut fold = IncrementalReduction::new(2, CheckedSignedAdd);
    match fold.prepare(7i64) {
        Ok(prepared) => { let _item = prepared.cancel(); assert(_item == 7); },
        Err(_) => { assert(false); },
    }
    assert(fold.processed_spec() == 0 && fold.result_spec() == 0);
    match fold.prepare(7i64) {
        Ok(prepared) => { let _result = prepared.commit(); assert(_result == (1usize, 7i64)); },
        Err(_) => { assert(false); },
    }
    match fold.prepare(-4i64) {
        Ok(prepared) => { let _result = prepared.commit(); assert(_result == (2usize, 3i64)); },
        Err(_) => { assert(false); },
    }
    let ghost before = fold;
    match fold.prepare(9i64) {
        Err((_reason, _item)) => { assert(_reason == automation_structures::RecordRefusal::Capacity && _item == 9); },
        Ok(prepared) => { let _ = prepared.cancel(); assert(false); },
    }
    assert(fold == before);
    fold
}

/// The external consumer receives the actual ordered permutation, with its contract.
pub fn immutable_arrangement_exports_both_directions() {
    use automation_structures::connectives::ordering_pass::{IndexArrangement, SignedRowOrder};
    use automation_structures::NullableSigned::Value;
    let mut values = Vec::new(); values.push(Value(2)); values.push(Value(3)); values.push(Value(2));
    let order = SignedRowOrder { values: &values, descending: true, nulls_first: false };
    if let Ok(arranged) = IndexArrangement::try_new(3, &order) {
        assert(arranged.inv());
        let ghost positions = arranged.positions_spec();
        assert(positions[0] < 3 && positions[1] < 3 && positions[2] < 3);
        assert(positions[0] != positions[1] && positions[0] != positions[2] && positions[1] != positions[2]);
        assert(positions == seq![1usize, 0usize, 2usize]);
        assert(arranged.inverse_spec()[0] == 1 && arranged.inverse_spec()[1] == 0
            && arranged.inverse_spec()[2] == 2);
        let _rank = arranged.rank_of(0); assert(_rank == Some(1usize));
        let _original = arranged.original_at(0); assert(_original == Some(1usize));
        let _foreign = arranged.rank_of(3); assert(_foreign == None);
    }
}

/// Complete minimum membership is usable by an external consumer without selecting K.
pub fn complete_minimum_selection_is_constructible<C: automation_structures::PositionOrder>(order: C) {
    if let Ok(owner) = automation_structures::CompetitiveSelectionMinimum::try_new(order) {
        proof { owner.expose_minima(); owner.expose_arrangement(); }
        assert forall|item: usize| owner.selected_spec().contains(item) <==>
            (item < order.domain_len() && forall|other: usize| other < order.domain_len()
                ==> #[trigger] order.key_le(item, other)) by {}
        let _selected = owner.selected();
        assert(_selected@ == owner.selected_spec());
    }
}

/// The external consumer receives the actual ordered permutation, with its contract.
///
/// # Errors
/// Returns the arrangement's domain or storage refusal.
pub fn finite_ordering_is_constructible()
    -> (result: Result<Vec<usize>, automation_structures::connectives::ordering_pass::ArrangementError>)
    ensures result is Ok ==> result.unwrap()@ == seq![1usize, 0usize, 2usize],
{
    use automation_structures::connectives::ordering_pass::{try_arrange_indices, SignedRowOrder};
    use automation_structures::primitives::audit_sink::NullableSigned::Value;
    let mut values = Vec::new(); values.push(Value(2)); values.push(Value(3)); values.push(Value(1));
    let order = SignedRowOrder { values: &values, descending: true, nulls_first: false };
    let result = try_arrange_indices(3, &order);
    if let Ok(ref _positions) = result {
        assert(_positions@[0] < 3 && _positions@[1] < 3 && _positions@[2] < 3);
        assert(_positions@[0] != _positions@[1] && _positions@[0] != _positions@[2] && _positions@[1] != _positions@[2]);
        assert(_positions@ == seq![1usize, 0usize, 2usize]);
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
                let _accepted = value.record_typed(7i64);
                assert(_accepted);
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
    let _first = fold.record_typed(NullableSigned::Value(7));
    assert(_first);
    let _second = fold.record_typed(NullableSigned::Missing);
    assert(_second);
    let _third = fold.record_typed(NullableSigned::Value(-11));
    assert(_third);
    let _refused = fold.record_typed(NullableSigned::Value(1));
    assert(!_refused);
    fold
}



/// Connective and primitive relations remain usable across the crate boundary.
pub proof fn structure_relations_are_importable()
    ensures
        automation_structures::connectives::counter::nonnegative(0),
        automation_structures::connectives::ordering_pass::strictly_before(0, 1),
        automation_structures::primitives::budget::budget_safety(1, 0, 0, 0),
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
        Some(_value) => { assert(*_value == 22); }
        None => { assert(false); }
    }
    registry
}

/// An external caller takes an original non-Copy value through the identity owner.
pub fn registry_take_frames_owned_bindings() {
    let mut owner = resource_registry::ResourceRegistry::<u64, Vec<u8>>::new();
    let mut first = Vec::new(); first.push(7u8);
    let mut second = Vec::new(); second.push(2u8);
    owner.register_key(7, first); owner.register_key(2, second);
    let _removed = owner.take_query(&7u64);
    assert(_removed == Some((7u64, first)));
    assert(owner.maps_key(2, second) && !owner.contains_key_identity(7));
    assert(owner.entries@.len() == 1);
    let ghost before = owner.entries@;
    let _absent = owner.take_query(&7u64);
    assert(_absent is None && owner.entries@ == before);
}

/// Typed latest-value and registration/notification contracts cross the package boundary.
pub fn summary_signal_is_constructible() {
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 1, 2);
    assert(signal.inv() && signal.value_spec() == 7 && signal.history_spec().len() == 0);
    if let Ok(token) = signal.register() {
        assert(token.scope_spec() == 41 && token.generation_spec() == 1);
        let _changed = signal.set_value(9u64);
        match _changed {
            Ok(true) => { assert(signal.value_spec() == 9 && signal.history_spec().len() == 1); },
            _ => { assert(false); },
        }
        proof { signal.expose_listener_state(token); }
        let _pending = signal.pending(token); assert(_pending == Ok(true));
        let _observed = signal.notify(token);
        assert(_observed is Ok);
        assert(_observed->Ok_0.value == 9 && _observed->Ok_0.head == 1 && _observed->Ok_0.changed);
        assert(signal.caught_up_spec(token));
        proof { signal.expose_listener_state(token); }
        let _repeated = signal.notify(token);
        assert(_repeated is Ok && !_repeated->Ok_0.changed);
        let _removed = signal.remove(token);
        assert(_removed is Ok && !signal.registered_spec(token));
        let _stale = signal.pending(token);
        assert(_stale == Err(automation_structures::SignalProfileError::UnknownListener));
        if let Ok(_next) = signal.register() {
            assert(_next.generation_spec() == 2);
            assert(signal.registered_spec(_next));
        }
    }
}

/// Original non-Copy payload custody, admission, FIFO, and closure cross the public boundary.
pub fn typed_stream_preserves_owned_fifo_contracts() {
    if let Ok(mut stream) = automation_structures::TypedStream::try_new(73, 2, 5) {
        let _empty = stream.receive();
        assert(_empty == Err(automation_structures::TypedStreamError::Empty));
        let mut first = Vec::new(); first.push(7u8);
        let mut second = Vec::new(); second.push(9u8);
        proof { stream.expose_admission(2); }
        let _first = stream.publish(first, 2);
        assert(_first == Ok(0u64));
        proof { stream.expose_admission(3); }
        let _second = stream.publish(second, 3);
        assert(_second == Ok(1u64));
        let _charged = stream.retained_bytes();
        assert(_charged == 5);
        let _closed = stream.close_input();
        assert(_closed && stream.closed_spec());
        let _received = stream.receive();
        assert(_received is Ok && _received->Ok_0.sequence == 0
            && _received->Ok_0.value == first && _received->Ok_0.encoded_bytes == 2);
        let _received = stream.receive();
        assert(_received is Ok && _received->Ok_0.sequence == 1
            && _received->Ok_0.value == second && _received->Ok_0.encoded_bytes == 3);
        let _drained = stream.is_drained(); assert(_drained);
        let _terminal = stream.receive();
        assert(_terminal == Err(automation_structures::TypedStreamError::Closed));
    }
}

/// Shared original custody, retained charges and stale refusals cross the public boundary.
pub fn typed_fanout_preserves_shared_original_and_refusal_contracts() {
    use automation_structures::{FanoutBranch, TypedFanout};
    if let Ok(mut stream) = TypedFanout::try_new(74, 1, 3) {
        let mut original = Vec::new(); original.push(7u8);
        match stream.publish(original, 3) {
            Err(_refusal) => { assert(_refusal.value == original && stream.entries_spec().len() == 0); },
            Ok(_sequence) => {
                proof { stream.expose_custody(); }
                assert(_sequence == 0 && stream.entries_spec().len() == 1);
                assert(stream.queue_spec(FanoutBranch::Left) == seq![0u64]);
                assert(stream.queue_spec(FanoutBranch::Right) == seq![0u64]);
                let _charge = stream.retained_bytes(); assert(_charge == 3);
                let _left = stream.observe(FanoutBranch::Left);
                assert(_left is Ok && *_left->Ok_0.value == original);
                if let Ok(left) = _left {
                    let token = left.token;
                    let _consumed = stream.consume(token); assert(_consumed is Ok);
                    proof { stream.expose_custody(); }
                    assert(stream.consumed_spec(FanoutBranch::Left) == 1);
                    assert(stream.consumed_spec(FanoutBranch::Right) == 0);
                    assert(stream.queue_spec(FanoutBranch::Left).len() == 0);
                    assert(stream.entries_spec().len() == 1 && stream.references_spec(0) == 1);
                    let _charge = stream.retained_bytes(); assert(_charge == 3);
                    let ghost after_left = stream;
                    let _stale = stream.consume(token);
                    assert(_stale == Err(automation_structures::TypedFanoutError::StaleObservation) && stream == after_left);
                    let _right = stream.observe(FanoutBranch::Right);
                    assert(_right is Ok && *_right->Ok_0.value == original);
                    if let Ok(right) = _right {
                        let token = right.token;
                        let _closed = stream.close_input(); assert(_closed);
                        proof { stream.expose_custody(); }
                        assert(stream.consumed_spec(FanoutBranch::Left) == 1);
                        assert(stream.consumed_spec(FanoutBranch::Right) == 0);
                        assert(stream.entries_spec().len() == 1 && stream.references_spec(0) == 1);
                        let _consumed = stream.consume(token); assert(_consumed is Ok);
                        proof { stream.expose_custody(); }
                        assert(stream.consumed_spec(FanoutBranch::Right) == 1);
                        let _length = stream.retained_len(); assert(_length == 0);
                        let _charge = stream.retained_bytes(); assert(_charge == 0);
                        let _drained = stream.is_drained(); assert(_drained);
                        let _terminal = stream.observe(FanoutBranch::Left);
                        assert(_terminal == Err(automation_structures::TypedFanoutError::Closed));
                    }
                }
            },
        }
    }
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
        Some(_value) => { assert(_value@ == seq![11u64]); }
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
        Some(_value) => { assert(_value@ == seq![22u64]); }
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
    let _accepted = buffer.push_unique(7);
    assert(_accepted);
    buffer
}

/// Preallocation and FIFO ownership compose across the published carrier boundary.
///
/// # Errors
/// Returns the Buffer storage reservation failure.
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
///
/// # Errors
/// Returns the Buffer storage reservation failure.
pub fn reserved_checked_buffer()
    -> (result: Result<Buffer<u64>, std::collections::TryReserveError>)
    ensures
        result is Ok ==> result->Ok_0.well_formed(),
        result is Ok ==> result->Ok_0.retained() == seq![7u64],
{
    let mut buffer = Buffer::try_new(1)?;
    let _accepted = buffer.push_unique(7);
    assert(_accepted);
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
        let _blocked = owner.start_running(1); assert(!_blocked);
        let _started = owner.start_running(0); assert(_started);
        let _completed = owner.complete_node(0); assert(_completed);
        let _ready = owner.become_ready(1); assert(_ready);
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
        let _begun = s.begin_step(); assert(_begun);
        let _done = s.complete_step(7); assert(_done);
        assert(s.history@ == seq![7u64]);
    }
}
/// A reserved fork cannot cross its barrier before completion.
pub fn reserved_fork_is_constructible() {
    use automation_structures::modalities::fork_join::ForkJoin;
    if let Ok(mut s) = ForkJoin::try_new(1, 10, 0) {
        let _early = s.barrier(); assert(!_early);
        let _start = s.start_worker(0); assert(_start);
        let _done = s.complete_worker(0,7); assert(_done);
        let _joined = s.barrier(); assert(_joined);
        let _output = s.produce_output(); assert(_output);
        assert(s.output_snapshot@ == seq![7u64]);
    }
}
/// Reservation cannot add an audit record or change its carried result.
pub fn reserved_audit_frames_chain(additional: usize) {
    use automation_structures::primitives::audit_sink::AuditSink;
    let mut s = AuditSink::new(3);
    let _accepted = s.record(7); assert(_accepted);
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
    let _accepted = r.advance_clock_to(27); assert(_accepted);
    assert(r.clock == 27 && r.window_start == 0 && r.budget.allocated == 0);
    let ghost before = r;
    let _backwards = r.advance_clock_to(26); assert(!_backwards); assert(r == before);
}
}

/// Shared pure domain adapters and their external proof witnesses.
pub mod domains;

verus! {
/// The quota-free profile exports exact batch custody and sealed membership.
pub fn unbudgeted_allocation_exports_exact_batch<K: automation_structures::KeyIdentity, V,
    P: automation_structures::AllocationDomain<K,V>>(domain: P, items: Vec<(K,(V,Vec<u64>))>) {
    let mut owner = automation_structures::TypedAllocation::unbudgeted(domain);
    assert(owner.entries_spec().len() == 0 && owner.budgets_spec().len() == 0);
    match owner.prepare_batch(items) {
        Ok(prepared) => {
            assert(prepared.items_spec() == items@);
            prepared.commit();
            assert(owner.entries_spec() =~= items@);
            assert(owner.budgets_spec().len() == 0);
            let sealed = owner.seal();
            assert(sealed.entries_spec() == items@ && sealed.budgets_spec().len() == 0);
            let _length = sealed.len(); assert(_length == items@.len());
            let _outside = sealed.budget(0); assert(_outside is None);
        },
        Err(_refused) => {
            assert(_refused.items == items);
            assert(owner.entries_spec().len() == 0 && owner.budgets_spec().len() == 0);
        },
    }
}
}

verus! {
/// The public owning profile preserves every input on refusal and exports both joint views.
///
/// # Errors
/// Returns graph/domain inputs unchanged on topology, handle or storage refusal.
pub fn owning_adjacency_is_constructible<H: Copy + automation_structures::value_eq::ValueEq,
    D: automation_structures::EdgeHandleDomain<H>,
    P: resource_registry::RegistryPredicate<automation_structures::compositions::relationship_graph::EdgeKey, ()>>(
    graph: automation_structures::RelationshipGraph, domain: D, predicate: P,
) -> (result: automation_structures::MaterializationResult<H, D, P>)
    ensures
        result is Ok ==> result->Ok_0.inv()
            && result->Ok_0.edges_spec() == graph.bindings()
            && result->Ok_0.node_universe() == graph.node_universe()
            && result->Ok_0.handle_domain_spec() == domain
            && result->Ok_0.predicate_spec() == predicate,
        result matches Err((_, returned, returned_domain, returned_predicate)) ==>
            returned.bindings() == graph.bindings()
            && returned.node_universe() == graph.node_universe()
            && returned.weight_ceiling() == graph.weight_ceiling()
            && returned_domain == domain && returned_predicate == predicate,
{
    let result = graph.materialize(domain, predicate);
    if let Ok(view) = &result {
        proof {
            view.expose_adjacency(automation_structures::EdgeDirection::Outgoing);
            view.expose_adjacency(automation_structures::EdgeDirection::Incoming);
            assert(automation_structures::connectives::ordering_pass::inverse_permutation(view.positions_spec(automation_structures::EdgeDirection::Outgoing),
                view.inverse_spec(automation_structures::EdgeDirection::Outgoing)));
            assert(automation_structures::connectives::ordering_pass::inverse_permutation(view.positions_spec(automation_structures::EdgeDirection::Incoming),
                view.inverse_spec(automation_structures::EdgeDirection::Incoming)));
        }
        let _outside = view.incident(view.num_nodes(), automation_structures::EdgeDirection::Outgoing);
        assert(_outside is None);
    }
    result
}

/// Exact exported boundaries characterize selected incidence, not just array lengths.
pub proof fn owning_adjacency_span_membership<H: Copy + automation_structures::value_eq::ValueEq,
    D: automation_structures::EdgeHandleDomain<H>,
    P: resource_registry::RegistryPredicate<automation_structures::compositions::relationship_graph::EdgeKey, ()>>(
    view: &automation_structures::MaterializedAdjacency<H, D, P>,
    node: usize, rank: int, direction: automation_structures::EdgeDirection,
)
    requires view.inv(), node < view.node_universe(), 0 <= rank < view.edges_spec().len(),
    ensures
        (view.offsets_spec(direction)[node as int] <= rank
            && rank < view.offsets_spec(direction)[node as int + 1]) <==>
        (view.predicate_spec().selected(view.edges_spec()[view.positions_spec(direction)[rank] as int].0, ())
            && automation_structures::compositions::relationship_graph::incidence_endpoint(
                view.edges_spec()[view.positions_spec(direction)[rank] as int].0, direction) == node),
{
    view.expose_adjacency(direction);
    assert(automation_structures::compositions::relationship_graph::incidence_boundary(
        view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
        node as int, view.offsets_spec(direction)[node as int]));
    assert(automation_structures::compositions::relationship_graph::incidence_boundary(
        view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
        node as int + 1, view.offsets_spec(direction)[node as int + 1]));
    assert((rank < view.offsets_spec(direction)[node as int]) <==>
        automation_structures::compositions::relationship_graph::incidence_before(
            view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
            node as int, rank));
    assert((rank < view.offsets_spec(direction)[node as int + 1]) <==>
        automation_structures::compositions::relationship_graph::incidence_before(
            view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
            node as int + 1, rank));
}

/// Exact representation equality rejects foreign handles even when their ordinal decodes.
pub fn owning_adjacency_foreign_handle<H: Copy + automation_structures::value_eq::ValueEq,
    D: automation_structures::EdgeHandleDomain<H>,
    P: resource_registry::RegistryPredicate<automation_structures::compositions::relationship_graph::EdgeKey, ()>>(
    view: &automation_structures::MaterializedAdjacency<H, D, P>, handle: H,
)
    requires view.inv(), forall|i: int| 0 <= i < view.original_handles_spec().len() ==>
        #[trigger] view.original_handles_spec()[i] != handle,
{
    proof {
        view.expose_handle_resolution(handle);
        if let Some(original) = view.handle_domain_spec().ordinal_spec(handle) {
            if original < view.original_handles_spec().len() {
                assert(view.original_handles_spec()[original as int] != handle);
            }
        }
        assert(view.resolve_spec(handle) is None);
    }
    let _edge = view.edge(&handle); assert(_edge is None);
    let _outgoing = view.rank_of(&handle, automation_structures::EdgeDirection::Outgoing);
    let _incoming = view.rank_of(&handle, automation_structures::EdgeDirection::Incoming);
    assert(_outgoing is None && _incoming is None);
}
}
