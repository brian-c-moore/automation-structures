// Executable ResourceRegistry correspondence for the TLA+ carrier.
//
// KeyIdentity instantiates the logical Keys domain from retained representations. ByteKey
// uses exact byte contents; ValueEq keys retain their original contracts through delegates.
// unique_identities governs the generic actions. The exact-key facade retains unique_mapping
// and its original observers, proved equivalent by identity_entries_are_exact. Both use the
// same entry vector, query search, positional removal, and append action.
//
// ResourceRegistry is a unique key->value mapping. The TLA+ spec models `entries`
// as a SET of <<key,value>> pairs and checks:
//
//   TypeInvariant == entries ⊆ Keys × Values
//   UniqueMapping == ∀ k : Cardinality({ v : <<k,v>> ∈ entries }) <= 1
//
// with two actions:
//
//   Register(k,v)  == entries' = { e ∈ entries : e[1] /= k } ∪ { <<k,v>> }   (upsert)
//   Deregister(k)  == (∃ v : <<k,v>> ∈ entries) ∧ entries' = { e ∈ entries : e[1] /= k }
//
// `entries` is represented as a duplicate-key-free Vec<(K,V)>. `register` is
// the upsert (drop any pair for k, then append <<k,v>>); `deregister`
// removes the pair for a present key. UniqueMapping is an `ensures` on both.
//
// VALUE FRAMING. Both actions frame the other keys by presence (`contains_key`)
// and by value (`maps_to`). Presence-only framing would permit a different value
// at an unchanged key. The two frames together determine the post-state: for k,
// uniqueness plus
// `maps_to(k,v)` leaves <<k,v>> as the only pair with that key; for every other
// key, the pair set is preserved in both directions.
//
// Representation:
//   - entries: Vec<(K,V)> of (key, value) pairs (the TLA+ set of <<k,v>>).
//   - UniqueMapping == no two distinct entries share a key (the cardinality<=1
//     constraint, since two pairs with the same key are the only way the
//     cardinality of {v : <<k,v>>} exceeds 1).
//   - `remove_key` realises the key filter by calling the positional Deregister
//     action. A proof equates its in-place removal to `without_key_sequence`;
//     entries move without requiring Copy or rebuilding the backing vector.

use crate::compositions::reduction::ReductionProjection;
use vstd::prelude::*;

mod registry_storage_seal {
    use vstd::prelude::*;
    verus! {
        pub trait Sealed {}
        pub trait Layout<K, V> {}
        pub trait Search<K, V, Q> {}
    }
}

// Rust data adapters for the library's exact byte equality, hashing and borrowed probe.
// They contain no registry transition or retained state.
impl PartialEq for ByteKey {
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}
impl Eq for ByteKey {}
impl std::hash::Hash for ByteKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}
impl std::borrow::Borrow<[u8]> for ByteKey {
    fn borrow(&self) -> &[u8] {
        self.as_bytes()
    }
}

pub use crate::value_eq::ValueEq as RegistryKey;

verus! {

/// has_key over the first `n` entries: some pair among entries[0..n] has key `k`.
pub open spec fn has_key<K, V>(entries: Seq<(K, V)>, n: int, k: K) -> bool {
    exists|i: int| 0 <= i < n && entries[i].0 == k
}

/// Extending the considered prefix by one entry.
pub proof fn lemma_has_key_extend<K, V>(entries: Seq<(K, V)>, n: int, k: K)
    requires 0 <= n < entries.len(),
    ensures
        has_key(entries, n + 1, k) == (has_key(entries, n, k) || entries[n].0 == k),
{
    if has_key(entries, n + 1, k) {
        let i = choose|i: int| 0 <= i < n + 1 && entries[i].0 == k;
        assert(i < n || i == n);
    }
    if has_key(entries, n, k) {
        let i = choose|i: int| 0 <= i < n && entries[i].0 == k;
        assert(0 <= i < n + 1 && entries[i].0 == k);
    }
    if entries[n].0 == k {
        assert(0 <= n < n + 1 && entries[n].0 == k);
    }
}

/// Pushing (a,b) makes has_key at kk hold iff it already held or kk == a.
pub proof fn lemma_push_has_key<K, V>(entries: Seq<(K, V)>, a: K, b: V, kk: K)
    ensures
        has_key(entries.push((a, b)), entries.len() as int + 1, kk)
            == (has_key(entries, entries.len() as int, kk) || kk == a),
{
    let pushed = entries.push((a, b));
    if has_key(entries, entries.len() as int, kk) {
        let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == kk;
        assert(pushed[i] == entries[i]);
    }
    if kk == a {
        assert(pushed[entries.len() as int].0 == kk);
    }
    if has_key(pushed, entries.len() as int + 1, kk) {
        let i = choose|i: int| 0 <= i < entries.len() as int + 1 && pushed[i].0 == kk;
        if i < entries.len() {
            assert(entries[i] == pushed[i]);
        }
    }
}

/// has_pair over the first `n` entries: some pair among entries[0..n] IS <<k,v>>.
/// The value-level counterpart of `has_key`, which records presence only:
/// framing with `has_key` alone says the key survives but says nothing about
/// what it is bound to.
pub open spec fn has_pair<K, V>(entries: Seq<(K, V)>, n: int, k: K, v: V) -> bool {
    exists|i: int| 0 <= i < n && entries[i].0 == k && entries[i].1 == v
}

/// Reusable logical form of ResourceRegistry's unique-key obligation.
pub open spec fn unique_mapping_entries<K, V>(entries: Seq<(K, V)>) -> bool {
    forall|i: int, j: int|
        (0 <= i < entries.len() && 0 <= j < entries.len() && i != j)
            ==> #[trigger] entries[i].0 != #[trigger] entries[j].0
}

/// Reusable key-only form of ResourceRegistry uniqueness.
pub open spec fn unique_keys<K>(keys: Seq<K>) -> bool {
    forall|i: int, j: int|
        (0 <= i < keys.len() && 0 <= j < keys.len() && i != j)
            ==> #[trigger] keys[i] != #[trigger] keys[j]
}

/// Whether one key occurs in a key-only ResourceRegistry projection.
pub open spec fn contains_key_value<K>(keys: Seq<K>, key: K) -> bool {
    exists|i: int| 0 <= i < keys.len() && #[trigger] keys[i] == key
}

/// Pushing one key preserves every prior membership and adds exactly that key.
pub proof fn contains_key_value_push<K>(keys: Seq<K>, added: K, key: K)
    ensures
        contains_key_value(keys.push(added), key)
            == (contains_key_value(keys, key) || key == added),
{
    let pushed = keys.push(added);
    if contains_key_value(keys, key) {
        let index = choose|index: int| 0 <= index < keys.len() && keys[index] == key;
        assert(pushed[index] == keys[index]);
    }
    if key == added {
        assert(pushed[keys.len() as int] == key);
    }
    if contains_key_value(pushed, key) {
        let index = choose|index: int| 0 <= index < pushed.len() && pushed[index] == key;
        if index < keys.len() {
            assert(keys[index] == pushed[index]);
        } else {
            assert(index == keys.len());
        }
    }
}

/// Removing one entry from a unique key sequence removes exactly that key.
pub proof fn contains_key_value_remove_unique<K>(keys: Seq<K>, removed: int, key: K)
    requires
        unique_keys(keys),
        0 <= removed < keys.len(),
    ensures
        contains_key_value(keys.remove(removed), key)
            == (contains_key_value(keys, key) && key != keys[removed]),
{
    keys.remove_ensures(removed);
    let reduced = keys.remove(removed);
    if contains_key_value(reduced, key) {
        let index = choose|index: int| 0 <= index < reduced.len() && reduced[index] == key;
        let old_index = if index < removed { index } else { index + 1 };
        assert(0 <= old_index < keys.len());
        assert(old_index != removed);
        assert(reduced[index] == keys[old_index]);
        assert(contains_key_value(keys, key));
        if key == keys[removed] {
            assert(keys[old_index] == keys[removed]);
            assert(false);
        }
    }
    if contains_key_value(keys, key) && key != keys[removed] {
        let old_index = choose|index: int| 0 <= index < keys.len() && keys[index] == key;
        assert(old_index != removed);
        let index = if old_index < removed { old_index } else { old_index - 1 };
        assert(0 <= index < reduced.len());
        assert(reduced[index] == keys[old_index]);
    }
}

/// Removing one entry from a unique-key registry removes exactly that key's binding.
pub proof fn has_pair_remove_unique<K, V>(
    entries: Seq<(K, V)>,
    removed: int,
    key: K,
    value: V,
)
    requires
        unique_mapping_entries(entries),
        0 <= removed < entries.len(),
    ensures
        has_pair(entries.remove(removed), (entries.len() - 1) as int, key, value)
            == (has_pair(entries, entries.len() as int, key, value)
                && key != entries[removed].0),
{
    entries.remove_ensures(removed);
    let reduced = entries.remove(removed);
    if has_pair(reduced, reduced.len() as int, key, value) {
        let index = choose|index: int|
            0 <= index < reduced.len()
                && reduced[index].0 == key
                && reduced[index].1 == value;
        let old_index = if index < removed { index } else { index + 1 };
        assert(0 <= old_index < entries.len());
        assert(old_index != removed);
        assert(reduced[index] == entries[old_index]);
        assert(has_pair(entries, entries.len() as int, key, value));
        if key == entries[removed].0 {
            assert(entries[old_index].0 == entries[removed].0);
            assert(false);
        }
    }
    if has_pair(entries, entries.len() as int, key, value) && key != entries[removed].0 {
        let old_index = choose|index: int|
            0 <= index < entries.len()
                && entries[index].0 == key
                && entries[index].1 == value;
        assert(old_index != removed);
        let index = if old_index < removed { old_index } else { old_index - 1 };
        assert(0 <= index < reduced.len());
        assert(reduced[index] == entries[old_index]);
    }
}

/// Extending the considered prefix by one entry (pair-level `lemma_has_key_extend`).
pub proof fn lemma_has_pair_extend<K, V>(entries: Seq<(K, V)>, n: int, k: K, v: V)
    requires 0 <= n < entries.len(),
    ensures
        has_pair(entries, n + 1, k, v)
            == (has_pair(entries, n, k, v) || (entries[n].0 == k && entries[n].1 == v)),
{
    if has_pair(entries, n + 1, k, v) {
        let i = choose|i: int| 0 <= i < n + 1 && entries[i].0 == k && entries[i].1 == v;
        assert(i < n || i == n);
    }
    if has_pair(entries, n, k, v) {
        let i = choose|i: int| 0 <= i < n && entries[i].0 == k && entries[i].1 == v;
        assert(0 <= i < n + 1 && entries[i].0 == k && entries[i].1 == v);
    }
    if entries[n].0 == k && entries[n].1 == v {
        assert(0 <= n < n + 1 && entries[n].0 == k && entries[n].1 == v);
    }
}

/// Pushing (a,b) makes has_pair at (kk,vv) hold iff it already held or (kk,vv) = (a,b).
pub proof fn lemma_push_has_pair<K, V>(entries: Seq<(K, V)>, a: K, b: V, kk: K, vv: V)
    ensures
        has_pair(entries.push((a, b)), entries.len() as int + 1, kk, vv)
            == (has_pair(entries, entries.len() as int, kk, vv) || (kk == a && vv == b)),
{
    let pushed = entries.push((a, b));
    if has_pair(entries, entries.len() as int, kk, vv) {
        let i = choose|i: int|
            0 <= i < entries.len() && entries[i].0 == kk && entries[i].1 == vv;
        assert(pushed[i] == entries[i]);
    }
    if kk == a && vv == b {
        assert(pushed[entries.len() as int].0 == kk && pushed[entries.len() as int].1 == vv);
    }
    if has_pair(pushed, entries.len() as int + 1, kk, vv) {
        let i = choose|i: int|
            0 <= i < entries.len() as int + 1 && pushed[i].0 == kk && pushed[i].1 == vv;
        if i < entries.len() {
            assert(entries[i] == pushed[i]);
        }
    }
}

/// Deterministic order-preserving removal of `key` from the first `n` entries.
pub open spec fn without_key_to<K, V>(entries: Seq<(K, V)>, key: K, n: int)
    -> Seq<(K, V)>
    decreases n,
{
    if n <= 0 || n > entries.len() {
        Seq::empty()
    } else {
        let prefix = without_key_to(entries, key, n - 1);
        if entries[n - 1].0 == key {
            prefix
        } else {
            prefix.push(entries[n - 1])
        }
    }
}

/// Deterministic order-preserving removal of every binding for `key`.
pub open spec fn without_key_sequence<K, V>(entries: Seq<(K, V)>, key: K)
    -> Seq<(K, V)>
{
    without_key_to(entries, key, entries.len() as int)
}

/// An absent key leaves the considered prefix unchanged.
pub proof fn without_key_to_absent<K, V>(entries: Seq<(K, V)>, key: K, n: int)
    requires 0 <= n <= entries.len(), !has_key(entries, n, key),
    ensures without_key_to(entries, key, n) == entries.subrange(0, n),
    decreases n,
{
    if n > 0 {
        without_key_to_absent(entries, key, n - 1);
        assert(entries[n - 1].0 != key);
        assert(entries.subrange(0, n - 1).push(entries[n - 1])
            =~= entries.subrange(0, n));
    } else {
        assert(entries.subrange(0, n) =~= Seq::empty());
    }
}

/// In a unique registry, the key filter is exactly one positional removal.
pub proof fn without_key_to_remove_unique<K, V>(
    entries: Seq<(K, V)>, key: K, n: int, removed: int,
)
    requires
        unique_mapping_entries(entries),
        0 <= n <= entries.len(),
        0 <= removed < entries.len(),
        entries[removed].0 == key,
    ensures
        without_key_to(entries, key, n) ==
            if removed < n { entries.subrange(0, n).remove(removed) }
            else { entries.subrange(0, n) },
    decreases n,
{
    if n > 0 {
        without_key_to_remove_unique(entries, key, n - 1, removed);
        if removed == n - 1 {
            entries.subrange(0, n).remove_ensures(removed);
            assert(entries.subrange(0, n).remove(removed) =~= entries.subrange(0, n - 1));
        } else {
            assert(entries[n - 1].0 != key);
            if removed < n - 1 {
                entries.subrange(0, n).remove_ensures(removed);
                entries.subrange(0, n - 1).remove_ensures(removed);
                assert(entries.subrange(0, n - 1).remove(removed).push(entries[n - 1])
                    =~= entries.subrange(0, n).remove(removed));
            } else {
                assert(entries.subrange(0, n - 1).push(entries[n - 1])
                    =~= entries.subrange(0, n));
            }
        }
    } else {
        assert(entries.subrange(0, n) =~= Seq::empty());
    }
}

/// Immutable interpretation of a retained key in the registry's logical key domain.
/// This is a data adapter; it stores no registry state or index.
pub trait KeyIdentity: Sized {
    /// The key domain used by the unique-mapping contract.
    type Identity;
    /// Project the retained representation into its exact logical identity.
    spec fn identity(&self) -> Self::Identity;
    /// Compare retained representations by that identity.
    fn key_equal(&self, other: &Self) -> (equal: bool)
        ensures equal == (self.identity() == other.identity());
}

impl<K: RegistryKey> KeyIdentity for K {
    type Identity = K;
    open spec fn identity(&self) -> K { *self }
    fn key_equal(&self, other: &Self) -> (equal: bool) {
        self.value_eq(other)
    }
}

/// A borrowed query interpreted in the same key domain as the retained key.
pub trait RegistryQuery<K: KeyIdentity>: Sized {
    /// Logical identity of the query; it is not retained by the registry.
    spec fn query_identity(&self) -> K::Identity;
    /// Compare the query with one retained key without allocating another key.
    fn matches_key(&self, key: &K) -> (equal: bool)
        ensures equal == (self.query_identity() == key.identity());
}

impl<K: KeyIdentity> RegistryQuery<K> for K {
    open spec fn query_identity(&self) -> K::Identity { self.identity() }
    fn matches_key(&self, key: &K) -> (equal: bool) { self.key_equal(key) }
}

/// Standard-library premise: byte-slice PartialEq compares exact contents and length.
/// The pinned vstd lacks this specialization. Rust supplies the implementation; this
/// declaration binds that external data leaf and is not a proof of the standard library.
#[verifier::external_body]
fn byte_slices_equal(left: &[u8], right: &[u8]) -> (equal: bool)
    ensures equal == (left@ == right@),
{
    <[u8] as PartialEq<[u8]>>::eq(left, right)
}

/// Immutable owned bytes with byte-content identity, independent of allocation identity.
/// Schema, null policy and encoding correctness remain the admitting caller's contract.
pub struct ByteKey {
    bytes: Vec<u8>,
}

impl KeyIdentity for ByteKey {
    type Identity = Seq<u8>;
    closed spec fn identity(&self) -> Seq<u8> { self.bytes@ }
    fn key_equal(&self, other: &Self) -> (equal: bool) {
        byte_slices_equal(self.bytes.as_slice(), other.bytes.as_slice())
    }
}

impl ByteKey {
    /// Move already-encoded bytes into a key without copying their backing allocation.
    pub fn from_bytes(bytes: Vec<u8>) -> (key: Self)
        ensures key.identity() == bytes@,
    {
        Self { bytes }
    }

    /// Borrow the exact encoded bytes retained by this key.
    pub fn as_bytes(&self) -> (bytes: &[u8])
        ensures bytes@ == self.identity(),
    {
        self.bytes.as_slice()
    }
}

impl RegistryQuery<ByteKey> for &[u8] {
    open spec fn query_identity(&self) -> Seq<u8> { (*self)@ }
    fn matches_key(&self, key: &ByteKey) -> (equal: bool) {
        byte_slices_equal(self, key.bytes.as_slice())
    }
}

/// The logical partial function is a projection of the one retained entry vector.
pub open spec fn identity_entries<K: KeyIdentity, V>(entries: Seq<(K, V)>)
    -> Seq<(K::Identity, V)>
{
    Seq::new(entries.len(), |i: int| (entries[i].0.identity(), entries[i].1))
}

/// Identity projection commutes with append.
pub proof fn identity_entry_at<K: KeyIdentity, V>(entries: Seq<(K, V)>, index: int)
    requires 0 <= index < entries.len(),
    ensures
        identity_entries(entries).len() == entries.len(),
        identity_entries(entries)[index] == (entries[index].0.identity(), entries[index].1),
{
}

/// Identity projection commutes with append.
pub proof fn identity_entries_push<K: KeyIdentity, V>(entries: Seq<(K, V)>, k: K, v: V)
    ensures identity_entries(entries.push((k, v))) == identity_entries(entries).push((k.identity(), v)),
{
    assert(identity_entries(entries.push((k, v))) =~= identity_entries(entries).push((k.identity(), v)));
}

/// Distinct physical positions in a unique registry have distinct logical identities.
pub proof fn identity_keys_distinct<K: KeyIdentity, V>(entries: Seq<(K, V)>, left: int, right: int)
    requires unique_mapping_entries(identity_entries(entries)),
        0 <= left < entries.len(), 0 <= right < entries.len(), left != right,
    ensures entries[left].0.identity() != entries[right].0.identity(),
{
    identity_entry_at(entries, left);
    identity_entry_at(entries, right);
    assert(identity_entries(entries)[left].0 != identity_entries(entries)[right].0);
}

/// Identity projection commutes with positional removal.
pub proof fn identity_entries_remove<K: KeyIdentity, V>(entries: Seq<(K, V)>, index: int)
    requires 0 <= index < entries.len(),
    ensures identity_entries(entries.remove(index)) == identity_entries(entries).remove(index),
{
    entries.remove_ensures(index);
    identity_entries(entries).remove_ensures(index);
    assert(identity_entries(entries.remove(index)) =~= identity_entries(entries).remove(index));
}

/// Exact representation-preserving filter by logical key identity.
pub open spec fn without_identity_to<K: KeyIdentity, V>(entries: Seq<(K, V)>, key: K, n: int)
    -> Seq<(K, V)>
    decreases n,
{
    if n <= 0 || n > entries.len() { Seq::empty() }
    else {
        let prefix = without_identity_to(entries, key, n - 1);
        if entries[n - 1].0.identity() == key.identity() { prefix }
        else { prefix.push(entries[n - 1]) }
    }
}

/// Remove all bindings of one logical identity, preserving surviving representations and order.
pub open spec fn without_identity_sequence<K: KeyIdentity, V>(entries: Seq<(K, V)>, key: K)
    -> Seq<(K, V)>
{
    without_identity_to(entries, key, entries.len() as int)
}

/// Existing ValueEq keys retain their original exact sequence contract.
pub proof fn identity_entries_are_exact<K: RegistryKey, V>(entries: Seq<(K, V)>)
    ensures identity_entries(entries) == entries,
{
    assert(identity_entries(entries) =~= entries);
}

/// Existing ValueEq keys retain their original exact sequence contract.
pub proof fn identity_filter_is_exact<K: RegistryKey, V>(entries: Seq<(K, V)>, key: K, n: int)
    requires 0 <= n <= entries.len(),
    ensures without_identity_to(entries, key, n) == without_key_to(entries, key, n),
    decreases n,
{
    if n > 0 { identity_filter_is_exact(entries, key, n - 1); }
}

/// An absent key leaves the considered prefix unchanged.
pub proof fn without_identity_to_absent<K: KeyIdentity, V>(entries: Seq<(K, V)>, key: K, n: int)
    requires 0 <= n <= entries.len(), !has_key(identity_entries(entries), n, key.identity()),
    ensures without_identity_to(entries, key, n) == entries.subrange(0, n),
    decreases n,
{
    if n > 0 {
        without_identity_to_absent(entries, key, n - 1);
        identity_entry_at(entries, n - 1);
        assert(entries[n - 1].0.identity() != key.identity());
        assert(entries.subrange(0, n - 1).push(entries[n - 1])
            =~= entries.subrange(0, n));
    } else {
        assert(entries.subrange(0, n) =~= Seq::empty());
    }
}

/// In a unique registry, the key filter is exactly one positional removal.
pub proof fn without_identity_to_remove_unique<K: KeyIdentity, V>(
    entries: Seq<(K, V)>, key: K, n: int, removed: int,
)
    requires
        unique_mapping_entries(identity_entries(entries)),
        0 <= n <= entries.len(),
        0 <= removed < entries.len(),
        entries[removed].0.identity() == key.identity(),
    ensures
        without_identity_to(entries, key, n) ==
            if removed < n { entries.subrange(0, n).remove(removed) }
            else { entries.subrange(0, n) },
    decreases n,
{
    if n > 0 {
        without_identity_to_remove_unique(entries, key, n - 1, removed);
        identity_entry_at(entries, removed);
        reveal(unique_mapping_entries);
        if removed == n - 1 {
            entries.subrange(0, n).remove_ensures(removed);
            assert(entries.subrange(0, n).remove(removed) =~= entries.subrange(0, n - 1));
        } else {
            identity_keys_distinct(entries, n - 1, removed);
            assert(entries[n - 1].0.identity() != key.identity());
            if removed < n - 1 {
                entries.subrange(0, n).remove_ensures(removed);
                entries.subrange(0, n - 1).remove_ensures(removed);
                assert(entries.subrange(0, n - 1).remove(removed).push(entries[n - 1])
                    =~= entries.subrange(0, n).remove(removed));
            } else {
                assert(entries.subrange(0, n - 1).push(entries[n - 1])
                    =~= entries.subrange(0, n));
            }
        }
    } else {
        assert(entries.subrange(0, n) =~= Seq::empty());
    }
}


/// Sealed compile-time selection of a physical entry representation.
pub trait RegistryLayout<K, V>: registry_storage_seal::Layout<K, V> {
    /// The one entry container; no second runtime field is introduced.
    type Entries: View<V = Seq<(K, V)>>;
}
/// Published Vec representation; this type adds no runtime state.
pub struct LinearStorage;
/// Indexed byte-key representation; this type adds no runtime state.
pub struct IndexedStorage;
impl registry_storage_seal::Sealed for LinearStorage {}
impl registry_storage_seal::Sealed for IndexedStorage {}
impl<K, V> registry_storage_seal::Layout<K, V> for LinearStorage {}
impl<V> registry_storage_seal::Layout<ByteKey, V> for IndexedStorage {}
impl<K, V> RegistryLayout<K, V> for LinearStorage {
    type Entries = Vec<(K, V)>;
}
impl<V> RegistryLayout<ByteKey, V> for IndexedStorage {
    type Entries = IndexedEntries<V>;
}

/// Sealed physical entry representation of the one ResourceRegistry owner.
pub trait RegistryStorage<K: KeyIdentity, V>: registry_storage_seal::Sealed + View<V = Seq<(K, V)>> {
    /// Number of retained bindings in deterministic order.
    fn len(&self) -> (n: usize) ensures n == self@.len();
    /// Whether the retained entry sequence is empty.
    fn is_empty(&self) -> (empty: bool)
        ensures empty == (self@.len() == 0),
    { self.len() == 0 }
    /// Fallible physical reservation, with every logical binding preserved.
    fn try_reserve_additional(&mut self, additional: usize) -> (reserved: bool)
        ensures final(self)@ == old(self)@;
    /// Borrow one exact retained key.
    fn key_at(&self, i: usize) -> (key: Option<&K>)
        ensures key is Some <==> i < self@.len(),
            key matches Some(key) ==> *key == self@[i as int].0;
    /// Borrow one exact retained value.
    fn value_at(&self, i: usize) -> (value: Option<&V>)
        ensures value is Some <==> i < self@.len(),
            value matches Some(value) ==> *value == self@[i as int].1;
    /// Borrow only the retained value; key and every other binding remain fixed.
    fn value_mut_at(&mut self, i: usize) -> (value: Option<&mut V>)
        ensures value is Some <==> i < old(self)@.len(),
            match value {
                Some(value) => *value == old(self)@[i as int].1
                    && final(self)@ == old(self)@.update(i as int, (old(self)@[i as int].0, *final(value))),
                None => final(self)@ == old(self)@,
            };
    /// Append an absent binding. The Registry owns the preceding admission/removal.
    fn push(&mut self, pair: (K, V))
        requires !has_key(identity_entries(old(self)@), old(self)@.len() as int, pair.0.identity()),
        ensures final(self)@ == old(self)@.push(pair);
    /// Order-preserving removal of one position.
    fn remove(&mut self, i: usize) -> (pair: Option<(K, V)>)
        ensures pair is Some <==> i < old(self)@.len(),
            i < old(self)@.len() ==> pair == Some(old(self)@[i as int])
                && final(self)@ == old(self)@.remove(i as int),
            i >= old(self)@.len() ==> final(self)@ == old(self)@;
}

/// Sealed search capability; each probe is tied to the stored key's exact identity.
pub trait RegistrySearch<K: KeyIdentity, V, Q: RegistryQuery<K>>:
    RegistryStorage<K, V> + registry_storage_seal::Search<K, V, Q> {
    /// Locate an equal key; the query is not retained.
    fn find_position(&self, query: &Q) -> (position: Option<usize>)
        ensures
            position matches Some(i) ==> i < self@.len()
                && self@[i as int].0.identity() == query.query_identity(),
            position is None ==> !has_key(identity_entries(self@), self@.len() as int, query.query_identity());
}

impl<K, V> registry_storage_seal::Sealed for Vec<(K, V)> {}
impl<K, V, Q> registry_storage_seal::Search<K, V, Q> for Vec<(K, V)> {}
impl<K: KeyIdentity, V> RegistryStorage<K, V> for Vec<(K, V)> {
    fn len(&self) -> (n: usize) { self.len() }
    fn try_reserve_additional(&mut self, additional: usize) -> (reserved: bool) {
        self.try_reserve(additional).is_ok()
    }
    #[expect(clippy::indexing_slicing, reason = "the physical storage guard checks i < self.len() before borrowing the retained key")]
    fn key_at(&self, i: usize) -> (key: Option<&K>) {
        if i < self.len() { Some(&self[i].0) } else { None }
    }
    #[expect(clippy::indexing_slicing, reason = "the physical storage guard checks i < self.len() before borrowing the retained value")]
    fn value_at(&self, i: usize) -> (value: Option<&V>) {
        if i < self.len() { Some(&self[i].1) } else { None }
    }
    #[expect(clippy::indexing_slicing, reason = "the physical storage guard checks i < self.len() before borrowing the retained value mutably")]
    fn value_mut_at(&mut self, i: usize) -> (value: Option<&mut V>) {
        if i < self.len() { Some(&mut self[i].1) } else { None }
    }
    fn push(&mut self, pair: (K, V)) { self.push(pair); }
    fn remove(&mut self, i: usize) -> (pair: Option<(K, V)>) {
        if i < self.len() { Some(self.remove(i)) } else { None }
    }
}

impl<K: KeyIdentity, V, Q: RegistryQuery<K>> RegistrySearch<K, V, Q> for Vec<(K, V)> {
    #[expect(clippy::indexing_slicing, reason = "the search loop guards i < the unchanged physical storage length")]
    #[expect(clippy::arithmetic_side_effects, reason = "the search cursor advances only while strictly below the unchanged storage length")]
    fn find_position(&self, query: &Q) -> (position: Option<usize>) {
        let len = self.len();
        let mut i: usize = 0;
        while i < len
            invariant i <= len, len == self.len(),
                forall|t: int| 0 <= t < i ==> self@[t].0.identity() != query.query_identity(),
            decreases len - i,
        {
            if query.matches_key(&self[i].0) { return Some(i); }
            i = i + 1;
        }
        None
    }
}

/// IndexMap is the external indexed-storage algorithm, not another Registry owner.
/// Its ordered logical entry view is bound by the concrete library-call premises below.
#[verifier::external_body]
#[verifier::reject_recursive_types(V)]
pub struct IndexedEntries<V> {
    map: indexmap::IndexMap<ByteKey, V>,
}
impl<V> registry_storage_seal::Sealed for IndexedEntries<V> {}
impl<V> registry_storage_seal::Search<ByteKey, V, ByteKey> for IndexedEntries<V> {}
impl<V> registry_storage_seal::Search<ByteKey, V, &[u8]> for IndexedEntries<V> {}
impl<V> View for IndexedEntries<V> {
    type V = Seq<(ByteKey, V)>;
    uninterp spec fn view(&self) -> Self::V;
}

impl<V> IndexedEntries<V> {
    /// Physical library capacity observation, separate from the logical mapping.
    pub uninterp spec fn capacity_spec(&self) -> nat;
    /// Library premise: capacity covers retained entries and fits usize.
    #[verifier::external_body]
    pub fn capacity(&self) -> (n: usize)
        ensures n == self.capacity_spec(), self@.len() <= n,
    { self.map.capacity() }
    /// Library premise: reservation preserves entries; refusal may retain extra capacity.
    #[verifier::external_body]
    fn try_reserve(&mut self, additional: usize) -> (accepted: bool)
        ensures final(self)@ == old(self)@,
            accepted ==> final(self).capacity_spec() >= old(self)@.len() + additional,
    { self.map.try_reserve(additional).is_ok() }
    /// Library premise: a new IndexMap has no retained entries.
    #[verifier::external_body]
    fn empty() -> (entries: Self)
        ensures entries@.len() == 0,
    { Self { map: indexmap::IndexMap::new() } }
}

impl<V> RegistryStorage<ByteKey, V> for IndexedEntries<V> {
    #[verifier::external_body]
    fn len(&self) -> (n: usize) { self.map.len() }
    fn try_reserve_additional(&mut self, additional: usize) -> (reserved: bool) {
        self.try_reserve(additional)
    }
    #[verifier::external_body]
    fn key_at(&self, i: usize) -> (key: Option<&ByteKey>) {
        self.map.get_index(i).map(|(key, _)| key)
    }
    #[verifier::external_body]
    fn value_at(&self, i: usize) -> (value: Option<&V>) {
        self.map.get_index(i).map(|(_, value)| value)
    }
    #[verifier::external_body]
    fn value_mut_at(&mut self, i: usize) -> (value: Option<&mut V>) {
        self.map.get_index_mut(i).map(|(_, value)| value)
    }
    #[verifier::external_body]
    fn push(&mut self, pair: (ByteKey, V)) { self.map.insert(pair.0, pair.1); }
    #[verifier::external_body]
    fn remove(&mut self, i: usize) -> (pair: Option<(ByteKey, V)>) {
        self.map.shift_remove_index(i)
    }
}

impl<V> RegistrySearch<ByteKey, V, ByteKey> for IndexedEntries<V> {
    #[verifier::external_body]
    fn find_position(&self, query: &ByteKey) -> (position: Option<usize>) {
        self.map.get_index_of(query)
    }
}
impl<V> RegistrySearch<ByteKey, V, &[u8]> for IndexedEntries<V> {
    #[verifier::external_body]
    fn find_position(&self, query: &&[u8]) -> (position: Option<usize>) {
        self.map.get_index_of(*query)
    }
}

impl<V> ResourceRegistry<ByteKey, V, IndexedStorage> {
    /// Construct the indexed byte-key representation of the existing Registry.
    pub fn new_indexed() -> (r: Self)
        ensures r.entries@.len() == 0, r.unique_identities(),
    { Self { entries: IndexedEntries::empty() } }

    /// Preflight entry storage while preserving the logical mapping.
    pub fn try_reserve_entries(&mut self, additional: usize) -> (accepted: bool)
        ensures final(self).entries@ == old(self).entries@,
            accepted ==> final(self).entries.capacity_spec() >= old(self).entries@.len() + additional,
    { self.entries.try_reserve(additional) }

    /// Reserve before invoking the shared Register transition.
    ///
    /// # Errors
    /// Returns the unconsumed key/value if storage reservation fails; bindings are unchanged.
    pub fn try_register_key(&mut self, key: ByteKey, value: V) -> (result: Result<(), (ByteKey, V)>)
        requires old(self).unique_identities(),
        ensures final(self).unique_identities(),
            result is Err ==> result.unwrap_err() == (key, value)
                && final(self).entries@ == old(self).entries@,
            result is Ok ==> final(self).entries@ == without_identity_sequence(old(self).entries@, key).push((key, value))
                && final(self).maps_key(key, value),
    {
        let additional = match self.find_key(&key) { Some(_) => 0, None => 1 };
        if !self.try_reserve_entries(additional) { return Err((key, value)); }
        self.register_key(key, value);
        Ok(())
    }
}

impl<K: KeyIdentity, V> ResourceRegistry<K, V> {
    /// Construct the original Vec representation, preserving the published default.
    pub fn new() -> (r: Self)
        ensures r.entries@.len() == 0, r.unique_identities(), unique_mapping_entries(r.entries@),
    { Self { entries: Vec::new() } }

    /// Preflight the default representation's storage without changing any binding.
    ///
    /// Physical capacity and allocation behavior rely on the standard allocator,
    /// as with Buffer's fallible constructor. The logical mapping is always fixed.
    ///
    /// # Errors
    /// Returns the standard allocation error when entry storage cannot be reserved.
    pub fn try_reserve_entries(&mut self, additional: usize)
        -> (result: Result<(), std::collections::TryReserveError>)
        ensures final(self).entries@ == old(self).entries@,
    {
        self.entries.try_reserve(additional)
    }
}

impl<K: KeyIdentity, V, S: RegistryLayout<K, V>> ResourceRegistry<K, V, S>
    where S::Entries: RegistrySearch<K, V, K>,
{
    /// Borrow the actual retained owner at a known position without replacing it.
    pub fn value_mut_at(&mut self, i: usize) -> (value: Option<&mut V>)
        requires old(self).unique_identities(),
        ensures value is Some <==> i < old(self).entries@.len(),
            match value {
                Some(value) => *value == old(self).entries@[i as int].1
                    && final(self).entries@ == old(self).entries@.update(i as int,
                        (old(self).entries@[i as int].0, *final(value))),
                None => final(self).entries@ == old(self).entries@,
            },
            final(self).unique_identities(),
    {
        let ghost entries = self.entries@;
        if i >= self.entries.len() { return None; }
        assert forall|updated: V| #[trigger] unique_mapping_entries(identity_entries(
            entries.update(i as int, (entries[i as int].0, updated)))) by {
            let changed = entries.update(i as int, (entries[i as int].0, updated));
            assert forall|a: int, b: int| 0 <= a < changed.len() && 0 <= b < changed.len() && a != b
                implies #[trigger] changed[a].0.identity() != #[trigger] changed[b].0.identity() by {
                identity_keys_distinct(entries, a, b);
            }
        }
        self.entries.value_mut_at(i)
    }

    /// Locate a borrowed key and borrow its retained owner, preserving other entries.
    pub fn lookup_query_mut<Q: RegistryQuery<K>>(&mut self, query: &Q) -> (value: Option<&mut V>)
        where S::Entries: RegistrySearch<K, V, Q>,
        requires old(self).unique_identities(),
        ensures final(self).unique_identities(),
            final(self).entries@.len() == old(self).entries@.len(),
            value is None ==> !old(self).contains_identity(query.query_identity())
                && final(self).entries@ == old(self).entries@,
            value is Some ==> old(self).maps_identity(query.query_identity(), *value.unwrap())
                && final(self).maps_identity(query.query_identity(), *final(value.unwrap())),
            forall|i: int| 0 <= i < old(self).entries@.len() ==>
                #[trigger] final(self).entries@[i].0 == old(self).entries@[i].0,
            forall|i: int| 0 <= i < old(self).entries@.len()
                && old(self).entries@[i].0.identity() != query.query_identity() ==>
                    #[trigger] final(self).entries@[i] == old(self).entries@[i],
    {
        match self.find_key(query) {
            Some(i) => {
                proof {
                    let entries = self.entries@;
                    identity_entry_at(entries, i as int);
                    assert(self.maps_identity(query.query_identity(), entries[i as int].1));
                    assert forall|updated: V| #[trigger] has_pair(identity_entries(entries.update(i as int,
                        (entries[i as int].0, updated))), entries.len() as int, query.query_identity(), updated) by {
                        identity_entry_at(entries.update(i as int, (entries[i as int].0, updated)), i as int);
                    }
                }
                self.value_mut_at(i)
            }
            None => None,
        }
    }
}

/// A unique-key registry: a set of (key, value) pairs with no repeated key.
pub struct ResourceRegistry<K, V, S: RegistryLayout<K, V> = LinearStorage> {
    /// Unique-key entries in deterministic storage order.
    pub entries: S::Entries,
}

/// Refusal of unique insertion; existing upsert is a separate operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum RegistryInsertError {
    /// The exact logical key already has a retained binding.
    DuplicateKey,
    /// The physical representation could not reserve another entry.
    StorageUnavailable,
}

/// Pure domain content for a Registry-owned Boolean query.
pub trait RegistryPredicate<K, V> {
    /// Mathematical selection of one retained key/value pair.
    spec fn selected(&self, key: K, value: V) -> bool;
    /// Evaluate that selection without retaining automation state.
    fn test(&self, key: &K, value: &V) -> (selected: bool)
        ensures selected == self.selected(*key, *value);
}

/// Mathematical selected count of an immutable retained prefix.
pub open spec fn selected_count<K, V, P: RegistryPredicate<K, V>>(
    entries: Seq<(K, V)>, length: int, predicate: P,
) -> int
    decreases length,
{
    if length <= 0 || length > entries.len() { 0 }
    else { selected_count(entries, length - 1, predicate)
        + if predicate.selected(entries[length - 1].0, entries[length - 1].1) { 1int } else { 0int } }
}

// Borrowed domain content only; the named Reduction retains all traversal state.
struct RegistryMatchProjection<'a, K, V, S: RegistryLayout<K, V>, P: RegistryPredicate<K, V>> {
    registry: &'a ResourceRegistry<K, V, S>,
    predicate: &'a P,
}

impl<'a, K: KeyIdentity, V, S: RegistryLayout<K, V>, P: RegistryPredicate<K, V>>
    ReductionProjection<crate::primitives::audit_sink::AdditiveChain>
    for RegistryMatchProjection<'a, K, V, S, P>
    where S::Entries: RegistryStorage<K, V>,
{
    closed spec fn domain_len(&self) -> nat { self.registry.entries@.len() }
    closed spec fn item_spec(&self, position: int) -> u64 {
        if self.predicate.selected(self.registry.entries@[position].0,
            self.registry.entries@[position].1) { 1 } else { 0 }
    }
    fn len(&self) -> (length: usize) { self.registry.entries.len() }
    fn item(&self, position: usize) -> (item: u64) {
        let key = match self.registry.entries.key_at(position) {
            Some(key) => key, None => { proof { assert(false); } return 0; },
        };
        let value = match self.registry.entries.value_at(position) {
            Some(value) => value, None => { proof { assert(false); } return 0; },
        };
        if self.predicate.test(key, value) { 1 } else { 0 }
    }
}

impl<'a, K: KeyIdentity, V, S: RegistryLayout<K, V>, P: RegistryPredicate<K, V>>
    RegistryMatchProjection<'a, K, V, S, P>
    where S::Entries: RegistryStorage<K, V>,
{
    proof fn prefix_correct(&self, end: int)
        requires 0 <= end <= self.registry.entries@.len(),
            self.registry.entries@.len() <= u64::MAX,
        ensures
            0 <= selected_count(self.registry.entries@, end, *self.predicate) <= end,
            crate::compositions::reduction::projected_fold_to(*self,
                crate::primitives::audit_sink::AdditiveChain, end) as int
                == selected_count(self.registry.entries@, end, *self.predicate),
            crate::compositions::reduction::projected_prefix_admitted(*self,
                crate::primitives::audit_sink::AdditiveChain, end),
        decreases end,
    {
        if end > 0 { self.prefix_correct(end - 1); }
    }
}

impl<K: KeyIdentity, V, S: RegistryLayout<K, V>> ResourceRegistry<K, V, S>
    where S::Entries: RegistrySearch<K, V, K>,
{
    /// Insert an absent key through the existing Register action after reservation.
    ///
    /// # Errors
    /// Duplicate or allocation refusal returns the exact unconsumed key/value.
    /// Every logical binding is unchanged. The allocator may retain spare capacity.
    pub fn try_insert_unique(&mut self, key: K, value: V)
        -> (result: Result<usize, (RegistryInsertError, K, V)>)
        requires old(self).unique_identities(),
        ensures final(self).unique_identities(),
            result is Err ==> final(self).entries@ == old(self).entries@
                && result.unwrap_err().1 == key && result.unwrap_err().2 == value,
            result matches Err((RegistryInsertError::DuplicateKey, _, _))
                <==> old(self).contains_key_identity(key),
            result matches Ok(position) ==> position == old(self).entries@.len()
                && final(self).entries@ == old(self).entries@.push((key, value))
                && final(self).maps_key(key, value),
    {
        if let Some(position) = self.find_key(&key) {
            let _ = position;
            proof {
                identity_entry_at(self.entries@, position as int);
                assert(identity_entries(self.entries@)[position as int].0 == key.identity());
                assert(self.contains_key_identity(key));
            }
            return Err((RegistryInsertError::DuplicateKey, key, value));
        }
        if !self.entries.try_reserve_additional(1) {
            return Err((RegistryInsertError::StorageUnavailable, key, value));
        }
        let position = self.entries.len();
        self.register_key(key, value);
        Ok(position)
    }

    /// Count selected entries through the named Reduction, under this immutable borrow.
    /// AuditSink owns both traversal position and carried result; no aggregate is cached.
    #[expect(clippy::cast_possible_truncation, reason = "the exact boolean Reduction result is bounded by the Registry's usize entry length")]
    pub fn count_matching<P: RegistryPredicate<K, V>>(&self, predicate: &P) -> (count: usize)
        ensures count as int == selected_count(self.entries@, self.entries@.len() as int, *predicate),
            count <= self.entries@.len(),
    {
        use crate::compositions::reduction::IncrementalReduction;
        use crate::primitives::audit_sink::AdditiveChain;
        let length = self.entries.len();
        let mut reduction = IncrementalReduction::new(length, AdditiveChain);
        let source = RegistryMatchProjection { registry: self, predicate };
        let _folded = reduction.try_fold_projection(&source);
        proof {
            source.prefix_correct(reduction.processed_spec() as int);
            if _folded is Err {
                assert(source.item_spec(reduction.processed_spec() as int) <= 1u64);
                assert(false);
            }
            source.prefix_correct(length as int);
        }
        reduction.result() as usize
    }

    /// Whether at least one retained entry satisfies the domain predicate.
    pub fn any_matching<P: RegistryPredicate<K, V>>(&self, predicate: &P) -> (any: bool)
        ensures any == (selected_count(self.entries@, self.entries@.len() as int, *predicate) > 0),
    { self.count_matching(predicate) > 0 }

    /// Whether every retained entry satisfies the predicate; true for an empty Registry.
    pub fn all_matching<P: RegistryPredicate<K, V>>(&self, predicate: &P) -> (all: bool)
        ensures all == (selected_count(self.entries@, self.entries@.len() as int, *predicate)
            == self.entries@.len()),
    { self.count_matching(predicate) == self.entries.len() }

    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ `UniqueMapping`: no two distinct entries share a key.
    pub open spec fn unique_identities(&self) -> bool {
        unique_mapping_entries(identity_entries(self.entries@))
    }

    /// `k ∈ keys(entries)` (∃ v : <<k,v>> ∈ entries).
    #[verifier::inline]
    pub open spec fn contains_key_identity(&self, k: K) -> bool {
        self.contains_identity(k.identity())
    }

    /// `<<k,v>> ∈ entries`.
    #[verifier::inline]
    pub open spec fn maps_key(&self, k: K, v: V) -> bool {
        self.maps_identity(k.identity(), v)
    }

    /// Observe membership in the logical key domain without constructing a retained key.
    pub open spec fn contains_identity(&self, identity: K::Identity) -> bool {
        has_key(identity_entries(self.entries@), self.entries@.len() as int, identity)
    }

    /// Observe the exact value bound to a logical identity.
    pub open spec fn maps_identity(&self, identity: K::Identity, value: V) -> bool {
        has_pair(identity_entries(self.entries@), self.entries@.len() as int, identity, value)
    }

    /// A unique key cannot map to two different values.
    pub proof fn unique_identity_value(&self, k: K, left: V, right: V)
        requires
            self.unique_identities(),
            self.maps_key(k, left),
            self.maps_key(k, right),
        ensures left == right,
    {
        let left_index = choose|index: int|
            0 <= index < self.entries@.len()
                && self.entries@[index].0.identity() == k.identity()
                && self.entries@[index].1 == left;
        let right_index = choose|index: int|
            0 <= index < self.entries@.len()
                && self.entries@[index].0.identity() == k.identity()
                && self.entries@[index].1 == right;
        if left_index != right_index {
            assert(self.entries@[left_index].0.identity() != self.entries@[right_index].0.identity());
        }
        assert(left_index == right_index);
    }

    /// Every exact key-value witness also establishes key presence.
    pub proof fn maps_key_implies_contains(&self, k: K, v: V)
        requires self.maps_key(k, v),
        ensures self.contains_key_identity(k),
    {
        let index = choose|index: int|
            0 <= index < self.entries@.len()
                && self.entries@[index].0.identity() == k.identity()
                && self.entries@[index].1 == v;
        assert(0 <= index < self.entries@.len() && self.entries@[index].0.identity() == k.identity());
    }

    /// Every present key has a value witness in the registry.
    pub proof fn identity_has_value(&self, k: K)
        requires self.contains_key_identity(k),
        ensures exists|v: V| self.maps_key(k, v),
    {
        let index = choose|index: int|
            0 <= index < self.entries@.len() && self.entries@[index].0.identity() == k.identity();
        identity_entry_at(self.entries@, index);
        let value = self.entries@[index].1;
        assert(self.maps_key(k, value));
    }

    /// Locate either a retained-key query or a borrowed representation using one search.
    fn find_key<Q: RegistryQuery<K>>(&self, query: &Q) -> (position: Option<usize>)
        where S::Entries: RegistrySearch<K, V, Q>,
        ensures
            position matches Some(i) ==> i < self.entries@.len()
                && self.entries@[i as int].0.identity() == query.query_identity(),
            position is None ==> !self.contains_identity(query.query_identity()),
    { self.entries.find_position(query) }

    /// Borrow the actual retained value using an allocation-free query representation.
    pub fn lookup_query<'a, Q: RegistryQuery<K>>(&'a self, query: &Q) -> (res: Option<&'a V>)
        where S::Entries: RegistrySearch<K, V, Q>,
        requires self.unique_identities(),
        ensures
            res matches Some(v) ==> self.maps_identity(query.query_identity(), *v),
            res is None ==> !self.contains_identity(query.query_identity()),
    {
        match self.find_key(query) {
            Some(i) => {
                proof { identity_entry_at(self.entries@, i as int); }
                self.entries.value_at(i)
            }
            None => None,
        }
    }

    /// Take an owned binding through the same identity search and Deregister action.
    /// Absent queries preserve every entry; no payload cloning or allocation occurs.
    pub fn take_query<Q: RegistryQuery<K>>(&mut self, query: &Q) -> (removed: Option<(K, V)>)
        where S::Entries: RegistrySearch<K, V, Q>,
        requires old(self).unique_identities(),
        ensures final(self).unique_identities(),
            (removed is None) == !old(self).contains_identity(query.query_identity()),
            removed is None ==> final(self).entries@ == old(self).entries@,
            removed matches Some((key, value)) ==> key.identity() == query.query_identity()
                && old(self).maps_identity(query.query_identity(), value)
                && !final(self).contains_identity(query.query_identity())
                && final(self).entries@.len() + 1 == old(self).entries@.len()
                && final(self).entries@ == without_identity_sequence(old(self).entries@, key),
            forall|key: K, value: V| key.identity() != query.query_identity() ==>
                (#[trigger] final(self).maps_key(key, value) == old(self).maps_key(key, value)),
    {
        match self.find_key(query) {
            Some(index) => {
                let ghost before = *self;
                let ghost entry = self.entries@[index as int];
                proof {
                    identity_entry_at(self.entries@, index as int);
                    assert(before.maps_identity(query.query_identity(), entry.1));
                }
                let removed = self.deregister_identity_at(index);
                assert(removed == Some(entry));
                proof {
                    without_identity_to_remove_unique(before.entries@, entry.0,
                        before.entries@.len() as int, index as int);
                }
                assert(!self.contains_identity(query.query_identity())) by {
                    if self.contains_identity(query.query_identity()) {
                        let remaining = choose|remaining: int| 0 <= remaining < self.entries@.len()
                            && self.entries@[remaining].0.identity() == query.query_identity();
                        identity_entry_at(self.entries@, remaining);
                        let retained = self.entries@[remaining];
                        assert(self.maps_key(retained.0, retained.1));
                        assert(retained.0.identity() == entry.0.identity());
                        assert(false);
                    }
                }
                removed
            },
            None => None,
        }
    }

    /// Borrow the value for a retained-key representation through the same query path.
    pub fn lookup_key_ref<'a>(&'a self, k: &K) -> (res: Option<&'a V>)
        requires self.unique_identities(),
        ensures
            res matches Some(v) ==> self.maps_key(*k, *v),
            res is None ==> !self.contains_key_identity(*k),
    {
        self.lookup_query(k)
    }

    /// Compatibility projection for callers that need a copied value.
    #[expect(clippy::manual_map, reason = "the explicit match is supported by the Verus boundary")]
    pub fn lookup_key(&self, k: K) -> (res: Option<V>)
        where V: Copy,
        requires self.unique_identities(),
        ensures
            res matches Some(v) ==> self.maps_key(k, v),
            res is None ==> !self.contains_key_identity(k),
    {
        match self.lookup_key_ref(&k) {
            Some(v) => Some(*v),
            None => None,
        }
    }

    /// Execute the key filter through positional Deregister, retaining storage.
    fn remove_identity_key(&mut self, k: &K)
        requires old(self).unique_identities(),
        ensures
            final(self).unique_identities(),
            !final(self).contains_key_identity(*k),
            final(self).entries@ == without_identity_sequence(old(self).entries@, *k),
            forall|kk: K| kk.identity() != k.identity() ==>
                (#[trigger] final(self).contains_key_identity(kk) == old(self).contains_key_identity(kk)),
            forall|kk: K, vv: V| kk.identity() != k.identity() ==>
                (#[trigger] final(self).maps_key(kk, vv) == old(self).maps_key(kk, vv)),
            !old(self).contains_key_identity(*k) ==> final(self).entries@ == old(self).entries@,
    {
        let ghost before = self.entries@;
        if let Some(index) = self.find_key(k) {
            proof { identity_entry_at(self.entries@, index as int); }
            assert(self.contains_key_identity(*k));
                proof { without_identity_to_remove_unique(before, *k, before.len() as int, index as int); }
                let _removed = self.deregister_identity_at(index);
                assert forall|kk: K| kk.identity() != k.identity() implies
                    (#[trigger] self.contains_key_identity(kk) == old(self).contains_key_identity(kk)) by {
                    if self.contains_key_identity(kk) {
                        self.identity_has_value(kk);
                        let value = choose|value: V| self.maps_key(kk, value);
                        old(self).maps_key_implies_contains(kk, value);
                    }
                    if old(self).contains_key_identity(kk) {
                        old(self).identity_has_value(kk);
                        let value = choose|value: V| old(self).maps_key(kk, value);
                        self.maps_key_implies_contains(kk, value);
                    }
                }
                assert(!self.contains_key_identity(*k)) by {
                    if self.contains_key_identity(*k) {
                        self.identity_has_value(*k);
                    }
                }
        } else {
            proof { without_identity_to_absent(before, *k, before.len() as int); }
        }
    }

    // ── Register (TLA+ Register) ────────────────────────────────────────

    /// Upsert `k |-> v`: drop any existing pair for `k`, then append <<k,v>>.
    /// Realises the TLA+ `Register(k,v)`; re-establishes UniqueMapping and
    /// establishes `maps_key(k,v)`, preserving every other key's presence.
    pub fn register_key(&mut self, k: K, v: V)
        requires old(self).unique_identities(),
        ensures
            final(self).unique_identities(),
            final(self).maps_key(k, v),
            final(self).entries@
                == without_identity_sequence(old(self).entries@, k).push((k, v)),
            // every other key's presence is unchanged
            forall|kk: K|
                kk.identity() != k.identity() ==>
                    (#[trigger] final(self).contains_key_identity(kk) == old(self).contains_key_identity(kk)),
            // Every other key's value is unchanged. Presence alone would
            // admit a body that silently re-binds k' to a different value while
            // leaving k' present; the `Register` action determines the
            // post-state, so the contract has to frame values, not just keys.
            forall|kk: K, vv: V|
                kk.identity() != k.identity() ==>
                    (#[trigger] final(self).maps_key(kk, vv) == old(self).maps_key(kk, vv)),
            !old(self).contains_key_identity(k)
                ==> final(self).entries@ == old(self).entries@.push((k, v)),
    {
        let ghost old_entries = self.entries@;
        let ghost was_absent = !self.contains_key_identity(k);
        self.remove_identity_key(&k);
        let ghost fb = self.entries@;
        assert(unique_mapping_entries(identity_entries(fb)));
        assert forall|i: int| 0 <= i < fb.len() implies #[trigger] fb[i].0.identity() != k.identity() by {
            identity_entry_at(fb, i);
        }
        assert forall|kk: K| kk.identity() != k.identity() implies
            (#[trigger] has_key(identity_entries(fb), fb.len() as int, kk.identity())
                == has_key(identity_entries(old_entries), old_entries.len() as int, kk.identity())) by {
            assert(self.contains_key_identity(kk) == old(self).contains_key_identity(kk));
        }
        assert forall|kk: K, vv: V| kk.identity() != k.identity() implies
            (#[trigger] has_pair(identity_entries(fb), fb.len() as int, kk.identity(), vv)
                == has_pair(identity_entries(old_entries), old_entries.len() as int, kk.identity(), vv)) by {
            assert(self.maps_key(kk, vv) == old(self).maps_key(kk, vv));
        }
        proof {
            if was_absent {
                assert(fb == old_entries);
            }
        }
        proof { identity_entries_push(fb, k, v); }
        self.entries.push((k, v));
        // UniqueMapping: filtered is unique-key and has no key k; appending
        // <<k,v>> (a fresh key) keeps keys distinct.
        assert forall|i: int, j: int|
            (0 <= i < self.entries@.len() && 0 <= j < self.entries@.len() && i != j)
            implies #[trigger] self.entries@[i].0.identity() != #[trigger] self.entries@[j].0.identity() by {
            if i < fb.len() && j < fb.len() {
                // Both survivors retain distinct logical identities.
                reveal(unique_mapping_entries);
                identity_entry_at(fb, i);
                identity_entry_at(fb, j);
            } else if j == fb.len() && i < fb.len() {
                assert(self.entries@[i] == fb[i]);
                assert(fb[i].0.identity() != k.identity());          // remove_key: no key k
            } else if i == fb.len() && j < fb.len() {
                assert(self.entries@[j] == fb[j]);
                assert(fb[j].0.identity() != k.identity());
            }
        }
        assert(self.maps_key(k, v)) by {
            identity_entry_at(self.entries@, fb.len() as int);
            assert(self.entries@[fb.len() as int].0.identity() == k.identity() && self.entries@[fb.len() as int].1 == v);
        }
        // frame: presence of any kk /= k is the filtered presence, which equals
        // the original presence (projection), and the appended <<k,v>> only adds k.
        assert forall|kk: K| kk.identity() != k.identity() implies
            (#[trigger] self.contains_key_identity(kk) == old(self).contains_key_identity(kk)) by {
            lemma_push_has_key(identity_entries(fb), k.identity(), v, kk.identity());
        }
        // value frame: same argument one level down. `remove_key` preserved every
        // pair whose key is not k, and the appended pair has key k.
        assert forall|kk: K, vv: V| kk.identity() != k.identity() implies
            (#[trigger] self.maps_key(kk, vv) == old(self).maps_key(kk, vv)) by {
            lemma_push_has_pair(identity_entries(fb), k.identity(), v, kk.identity(), vv);
        }
    }

    // ── Deregister (TLA+ Deregister) ────────────────────────────────────

    /// Remove the binding at a known registry position.
    ///
    /// This is the positional form of `Deregister`: callers that discover a key while scanning
    /// the registry can remove that binding without rebuilding or replacing registry
    /// storage outside this owner.
    pub fn deregister_identity_at(&mut self, index: usize) -> (removed: Option<(K, V)>)
        requires
            old(self).unique_identities(),
            index < old(self).entries@.len(),
        ensures
            removed == Some(old(self).entries@[index as int]),
            final(self).entries@ == old(self).entries@.remove(index as int),
            final(self).entries@.len() + 1 == old(self).entries@.len(),
            final(self).unique_identities(),
            forall|key: K, value: V|
                #[trigger] final(self).maps_key(key, value)
                    == (old(self).maps_key(key, value) && key.identity() != old(self).entries@[index as int].0.identity()),
    {
        let ghost before = self.entries@;
        proof { identity_entries_remove(before, index as int); }
        let removed = self.entries.remove(index);
        assert(self.entries@ == before.remove(index as int));
        assert(self.unique_identities()) by {
            assert forall|left: int, right: int|
                0 <= left < self.entries@.len()
                    && 0 <= right < self.entries@.len()
                    && left != right
                implies #[trigger] self.entries@[left].0.identity() != #[trigger] self.entries@[right].0.identity() by {
                before.remove_ensures(index as int);
                let old_left = if left < index { left } else { left + 1 };
                let old_right = if right < index { right } else { right + 1 };
                assert(0 <= old_left < before.len());
                assert(0 <= old_right < before.len());
                assert(old_left != old_right);
                identity_keys_distinct(before, old_left, old_right);
                reveal(unique_mapping_entries);
                identity_entry_at(before, old_left);
                identity_entry_at(before, old_right);
                assert(self.entries@[left] == before[old_left]);
                assert(self.entries@[right] == before[old_right]);
            }
        }
        assert forall|key: K, value: V|
            #[trigger] self.maps_key(key, value)
                == (old(self).maps_key(key, value) && key.identity() != old(self).entries@[index as int].0.identity()) by {
            has_pair_remove_unique(identity_entries(before), index as int, key.identity(), value);
        }
        removed
    }

    /// Remove the pair for `k`. Realises the TLA+ `Deregister(k)` (guard:
    /// `k` is present). Re-establishes UniqueMapping; `k` is afterwards absent.
    pub fn deregister_key(&mut self, k: K)
        requires
            old(self).unique_identities(),
            old(self).contains_key_identity(k),
        ensures
            final(self).unique_identities(),
            !final(self).contains_key_identity(k),
            final(self).entries@ == without_identity_sequence(old(self).entries@, k),
            // every other key's presence is unchanged
            forall|kk: K|
                kk.identity() != k.identity() ==>
                    (#[trigger] final(self).contains_key_identity(kk) == old(self).contains_key_identity(kk)),
            // Every other key's value is unchanged (see `register`).
            forall|kk: K, vv: V|
                kk.identity() != k.identity() ==>
                    (#[trigger] final(self).maps_key(kk, vv) == old(self).maps_key(kk, vv)),
    {
        self.remove_identity_key(&k);
    }
}


impl<K: RegistryKey, V> ResourceRegistry<K, V> {

    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ `UniqueMapping`: no two distinct entries share a key.
    pub open spec fn unique_mapping(&self) -> bool {
        unique_mapping_entries(self.entries@)
    }

    /// `k ∈ keys(entries)` (∃ v : <<k,v>> ∈ entries).
    pub open spec fn contains_key(&self, k: K) -> bool {
        has_key(self.entries@, self.entries@.len() as int, k)
    }

    /// `<<k,v>> ∈ entries`.
    pub open spec fn maps_to(&self, k: K, v: V) -> bool {
        has_pair(self.entries@, self.entries@.len() as int, k, v)
    }

    /// A unique key cannot map to two different values.
    pub proof fn unique_value(&self, k: K, left: V, right: V)
        requires
            self.unique_mapping(),
            self.maps_to(k, left),
            self.maps_to(k, right),
        ensures left == right,
    {
        let left_index = choose|index: int|
            0 <= index < self.entries@.len()
                && self.entries@[index].0 == k
                && self.entries@[index].1 == left;
        let right_index = choose|index: int|
            0 <= index < self.entries@.len()
                && self.entries@[index].0 == k
                && self.entries@[index].1 == right;
        if left_index != right_index {
            assert(self.entries@[left_index].0 != self.entries@[right_index].0);
        }
        assert(left_index == right_index);
    }

    /// Every exact key-value witness also establishes key presence.
    pub proof fn maps_to_implies_contains(&self, k: K, v: V)
        requires self.maps_to(k, v),
        ensures self.contains_key(k),
    {
        let index = choose|index: int|
            0 <= index < self.entries@.len()
                && self.entries@[index].0 == k
                && self.entries@[index].1 == v;
        assert(0 <= index < self.entries@.len() && self.entries@[index].0 == k);
    }

    /// Every present key has a value witness in the registry.
    pub proof fn contains_has_value(&self, k: K)
        requires self.contains_key(k),
        ensures exists|v: V| self.maps_to(k, v),
    {
        let index = choose|index: int|
            0 <= index < self.entries@.len() && self.entries@[index].0 == k;
        let value = self.entries@[index].1;
        assert(self.maps_to(k, value));
    }


    /// Borrow through the identity query path with the original exact-key contract.
    pub fn lookup_ref<'a>(&'a self, k: &K) -> (res: Option<&'a V>)
        requires self.unique_mapping(),
        ensures
            res matches Some(v) ==> self.maps_to(*k, *v),
            res is None ==> !self.contains_key(*k),
    {
        proof { identity_entries_are_exact(self.entries@); }
        self.lookup_key_ref(k)
    }

    /// Copy an exact-key lookup result when its retained value is Copy.
    #[expect(clippy::manual_map, reason = "the explicit match is supported by the Verus boundary")]
    pub fn lookup(&self, k: K) -> (res: Option<V>)
        where V: Copy,
        requires self.unique_mapping(),
        ensures
            res matches Some(v) ==> self.maps_to(k, v),
            res is None ==> !self.contains_key(k),
    {
        match self.lookup_ref(&k) { Some(value) => Some(*value), None => None }
    }

    /// Upsert an exact ValueEq key, preserving the original sequence contract.
    pub fn register(&mut self, k: K, v: V)
        requires old(self).unique_mapping(),
        ensures
            final(self).unique_mapping(),
            final(self).maps_to(k, v),
            final(self).entries@
                == without_key_sequence(old(self).entries@, k).push((k, v)),
            // every other key's presence is unchanged
            forall|kk: K|
                kk != k ==>
                    (#[trigger] final(self).contains_key(kk) == old(self).contains_key(kk)),
            // Every other key's value is unchanged. Presence alone would
            // admit a body that silently re-binds k' to a different value while
            // leaving k' present; the `Register` action determines the
            // post-state, so the contract has to frame values, not just keys.
            forall|kk: K, vv: V|
                kk != k ==>
                    (#[trigger] final(self).maps_to(kk, vv) == old(self).maps_to(kk, vv)),
            !old(self).contains_key(k)
                ==> final(self).entries@ == old(self).entries@.push((k, v)),
    {
        proof {
            identity_entries_are_exact(self.entries@);
            identity_filter_is_exact(self.entries@, k, self.entries@.len() as int);
        }
        self.register_key(k, v);
        proof { identity_entries_are_exact(self.entries@); }
        assert forall|kk: K| kk != k implies
            (#[trigger] self.contains_key(kk) == old(self).contains_key(kk)) by {
            assert(self.contains_key_identity(kk) == old(self).contains_key_identity(kk));
        }
        assert forall|kk: K, vv: V| kk != k implies
            (#[trigger] self.maps_to(kk, vv) == old(self).maps_to(kk, vv)) by {
            assert(self.maps_key(kk, vv) == old(self).maps_key(kk, vv));
        }
    }

    /// Remove an exact ValueEq key through the same canonical identity action.
    pub fn deregister(&mut self, k: K)
        requires
            old(self).unique_mapping(),
            old(self).contains_key(k),
        ensures
            final(self).unique_mapping(),
            !final(self).contains_key(k),
            final(self).entries@ == without_key_sequence(old(self).entries@, k),
            // every other key's presence is unchanged
            forall|kk: K|
                kk != k ==>
                    (#[trigger] final(self).contains_key(kk) == old(self).contains_key(kk)),
            // Every other key's value is unchanged (see `register`).
            forall|kk: K, vv: V|
                kk != k ==>
                    (#[trigger] final(self).maps_to(kk, vv) == old(self).maps_to(kk, vv)),
    {
        proof {
            identity_entries_are_exact(self.entries@);
            identity_filter_is_exact(self.entries@, k, self.entries@.len() as int);
        }
        self.deregister_key(k);
        proof { identity_entries_are_exact(self.entries@); }
        assert forall|kk: K| kk != k implies
            (#[trigger] self.contains_key(kk) == old(self).contains_key(kk)) by {
            assert(self.contains_key_identity(kk) == old(self).contains_key_identity(kk));
        }
        assert forall|kk: K, vv: V| kk != k implies
            (#[trigger] self.maps_to(kk, vv) == old(self).maps_to(kk, vv)) by {
            assert(self.maps_key(kk, vv) == old(self).maps_key(kk, vv));
        }
    }

    /// Preserve the exact-key positional removal contract on the same owner action.
    pub fn deregister_at(&mut self, index: usize) -> (removed: Option<(K, V)>)
        requires
            old(self).unique_mapping(),
            index < old(self).entries@.len(),
        ensures
            removed == Some(old(self).entries@[index as int]),
            final(self).entries@ == old(self).entries@.remove(index as int),
            final(self).entries@.len() + 1 == old(self).entries@.len(),
            final(self).unique_mapping(),
            forall|key: K, value: V|
                #[trigger] final(self).maps_to(key, value)
                    == (old(self).maps_to(key, value) && key != old(self).entries@[index as int].0),
    {
        proof { identity_entries_are_exact(self.entries@); }
        let removed = self.deregister_identity_at(index);
        proof { identity_entries_are_exact(self.entries@); }
        assert forall|key: K, value: V|
            #[trigger] self.maps_to(key, value) == (old(self).maps_to(key, value) && key != old(self).entries@[index as int].0) by {
            assert(self.maps_key(key, value) == (old(self).maps_key(key, value)
                && key.identity() != old(self).entries@[index as int].0.identity()));
        }
        removed
    }
}

}
