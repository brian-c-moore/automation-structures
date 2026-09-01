// Executable ResourceRegistry correspondence for the TLA+ carrier.
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
//   - The `without_key` helper realises the set-builder { e : e[1] /= k }. It
//     carries the projection equivalence (a key kk /= k survives iff it was
//     present), from which uniqueness preservation follows given the input was
//     unique.

use vstd::prelude::*;

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

/// A unique-key registry: a set of (key, value) pairs with no repeated key.
pub struct ResourceRegistry<K, V> {
    /// Unique-key entries in deterministic storage order.
    pub entries: Vec<(K, V)>,
}

impl<K: RegistryKey + Copy, V: Copy> ResourceRegistry<K, V> {
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

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Empty registry. Realises the TLA+ `Init` (entries = {}); UniqueMapping
    /// holds vacuously.
    pub fn new() -> (r: ResourceRegistry<K, V>)
        ensures
            r.entries@.len() == 0,
            r.unique_mapping(),
    {
        ResourceRegistry { entries: Vec::new() }
    }

    // ── without_key (the set-builder { e ∈ entries : e[1] /= k }) ────────

    /// Every entry whose key is not `k`. Given a unique-key input, the output is
    /// unique-key, contains no key `k`, and preserves the presence of every other
    /// key (the projection equivalence).
    fn without_key(entries: &Vec<(K, V)>, k: K) -> (out: Vec<(K, V)>)
        requires
            forall|i: int, j: int|
                (0 <= i < entries@.len() && 0 <= j < entries@.len() && i != j)
                    ==> #[trigger] entries@[i].0 != #[trigger] entries@[j].0,
        ensures
            out@ == without_key_sequence(entries@, k),
            // no key k remains
            forall|i: int| 0 <= i < out@.len() ==> out@[i].0 != k,
            // unique keys preserved
            forall|i: int, j: int|
                (0 <= i < out@.len() && 0 <= j < out@.len() && i != j)
                    ==> #[trigger] out@[i].0 != #[trigger] out@[j].0,
            // projection: a key kk /= k survives iff it was present
            forall|kk: K|
                kk != k ==>
                    (#[trigger] has_key(out@, out@.len() as int, kk)
                        == has_key(entries@, entries@.len() as int, kk)),
            // value projection: a PAIR whose key is not k survives iff it was
            // present. The copy loop preserves values, and the contract says so.
            forall|kk: K, vv: V|
                kk != k ==>
                    (#[trigger] has_pair(out@, out@.len() as int, kk, vv)
                        == has_pair(entries@, entries@.len() as int, kk, vv)),
            !has_key(entries@, entries@.len() as int, k) ==> out@ == entries@,
    {
        let mut out: Vec<(K, V)> = Vec::new();
        let mut i: usize = 0;
        while i < entries.len()
            invariant
                i <= entries.len(),
                out@ == without_key_to(entries@, k, i as int),
                forall|a: int, b: int|
                    (0 <= a < entries@.len() && 0 <= b < entries@.len() && a != b)
                        ==> #[trigger] entries@[a].0 != #[trigger] entries@[b].0,
                forall|a: int| 0 <= a < out@.len() ==> out@[a].0 != k,
                forall|a: int, b: int|
                    (0 <= a < out@.len() && 0 <= b < out@.len() && a != b)
                        ==> #[trigger] out@[a].0 != #[trigger] out@[b].0,
                forall|kk: K|
                    kk != k ==>
                        (#[trigger] has_key(out@, out@.len() as int, kk)
                            == has_key(entries@, i as int, kk)),
                forall|kk: K, vv: V|
                    kk != k ==>
                        (#[trigger] has_pair(out@, out@.len() as int, kk, vv)
                            == has_pair(entries@, i as int, kk, vv)),
                !has_key(entries@, entries@.len() as int, k)
                    ==> out@ == entries@.subrange(0, i as int),
            decreases entries.len() - i,
        {
            let e = entries[i];
            let ghost ob = out@;
            if !e.0.value_eq(&k) {
                // e.0 is not yet in out: out's keys are exactly entries[0..i]'s
                // keys (minus k), and entries is unique-key, so entries[i].0 does
                // not occur in entries[0..i], hence not in out.
                assert(!has_key(entries@, i as int, e.0)) by {
                    if has_key(entries@, i as int, e.0) {
                        let t = choose|t: int| 0 <= t < i as int && entries@[t].0 == e.0;
                        assert(entries@[t].0 != entries@[i as int].0);  // uniqueness, t != i
                    }
                }
                assert(!has_key(ob, ob.len() as int, e.0));  // projection at kk = e.0
                out.push(e);
                // uniqueness preserved: the pushed key was absent from out
                assert forall|a: int, b: int|
                    (0 <= a < out@.len() && 0 <= b < out@.len() && a != b)
                    implies #[trigger] out@[a].0 != #[trigger] out@[b].0 by {
                    if a < ob.len() && b < ob.len() {
                        // both old
                    } else if b == ob.len() && a < ob.len() {
                        assert(out@[a] == ob[a]);
                        assert(has_key(ob, ob.len() as int, ob[a].0));
                    } else if a == ob.len() && b < ob.len() {
                        assert(out@[b] == ob[b]);
                        assert(has_key(ob, ob.len() as int, ob[b].0));
                    }
                }
            }
            assert(out@ == without_key_to(entries@, k, i as int + 1));
            // projection update for every kk /= k
            assert forall|kk: K| kk != k implies
                (#[trigger] has_key(out@, out@.len() as int, kk)
                    == has_key(entries@, (i + 1) as int, kk)) by {
                lemma_has_key_extend(entries@, i as int, kk);
                if e.0 != k {
                    lemma_push_has_key(ob, e.0, e.1, kk);
                }
            }
            // value-projection update for every (kk /= k, vv). When the entry is
            // dropped (e.0 == k) `out` is unchanged and the new prefix entry's key
            // is k, so neither side moves; when it is copied, both sides gain the
            // same pair.
            assert forall|kk: K, vv: V| kk != k implies
                (#[trigger] has_pair(out@, out@.len() as int, kk, vv)
                    == has_pair(entries@, (i + 1) as int, kk, vv)) by {
                lemma_has_pair_extend(entries@, i as int, kk, vv);
                if e.0 != k {
                    lemma_push_has_pair(ob, e.0, e.1, kk, vv);
                }
            }
            proof {
                if !has_key(entries@, entries@.len() as int, k) {
                    assert(e.0 != k) by {
                        if e.0 == k {
                            assert(has_key(entries@, entries@.len() as int, k));
                        }
                    }
                    assert(out@ == entries@.subrange(0, (i + 1) as int));
                }
            }
            i = i + 1;
        }
        proof {
            if !has_key(entries@, entries@.len() as int, k) {
                assert(entries@.subrange(0, entries@.len() as int) =~= entries@);
            }
        }
        out
    }

    // ── lookup ──────────────────────────────────────────────────────────

    /// Look up the value bound to `k`, or None if `k` is unmapped. Under
    /// UniqueMapping the answer is unambiguous.
    pub fn lookup(&self, k: K) -> (res: Option<V>)
        requires self.unique_mapping(),
        ensures
            res matches Option::Some(v) ==> self.maps_to(k, v),
            res is None ==> !self.contains_key(k),
    {
        let len = self.entries.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.entries.len(),
                forall|t: int| 0 <= t < i ==> self.entries@[t].0 != k,
            decreases len - i,
        {
            if self.entries[i].0.value_eq(&k) {
                assert(self.entries@[i as int].0 == k && self.entries@[i as int].1 == self.entries@[i as int].1);
                return Some(self.entries[i].1);
            }
            i = i + 1;
        }
        assert(!self.contains_key(k));
        None
    }

    // ── Register (TLA+ Register) ────────────────────────────────────────

    /// Upsert `k |-> v`: drop any existing pair for `k`, then append <<k,v>>.
    /// Realises the TLA+ `Register(k,v)`; re-establishes UniqueMapping and
    /// establishes `maps_to(k,v)`, preserving every other key's presence.
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
        let ghost old_entries = self.entries@;
        let ghost was_absent = !self.contains_key(k);
        let filtered = Self::without_key(&self.entries, k);
        let ghost fb = filtered@;
        proof {
            if was_absent {
                assert(fb == old_entries);
            }
        }
        self.entries = filtered;
        self.entries.push((k, v));
        // UniqueMapping: filtered is unique-key and has no key k; appending
        // <<k,v>> (a fresh key) keeps keys distinct.
        assert forall|i: int, j: int|
            (0 <= i < self.entries@.len() && 0 <= j < self.entries@.len() && i != j)
            implies #[trigger] self.entries@[i].0 != #[trigger] self.entries@[j].0 by {
            if i < fb.len() && j < fb.len() {
                // both filtered: filtered uniqueness
            } else if j == fb.len() && i < fb.len() {
                assert(self.entries@[i] == fb[i]);
                assert(fb[i].0 != k);          // without_key: no key k
            } else if i == fb.len() && j < fb.len() {
                assert(self.entries@[j] == fb[j]);
                assert(fb[j].0 != k);
            }
        }
        assert(self.maps_to(k, v)) by {
            assert(self.entries@[fb.len() as int].0 == k && self.entries@[fb.len() as int].1 == v);
        }
        // frame: presence of any kk /= k is the filtered presence, which equals
        // the original presence (projection), and the appended <<k,v>> only adds k.
        assert forall|kk: K| kk != k implies
            (#[trigger] self.contains_key(kk) == old(self).contains_key(kk)) by {
            lemma_push_has_key(fb, k, v, kk);
        }
        // value frame: same argument one level down. `without_key` preserved every
        // pair whose key is not k, and the appended pair has key k.
        assert forall|kk: K, vv: V| kk != k implies
            (#[trigger] self.maps_to(kk, vv) == old(self).maps_to(kk, vv)) by {
            lemma_push_has_pair(fb, k, v, kk, vv);
        }
    }

    // ── Deregister (TLA+ Deregister) ────────────────────────────────────

    /// Remove the binding at a known registry position.
    ///
    /// This is the positional form of `Deregister`: callers that discover a key while scanning
    /// the registry can remove that binding without rebuilding or replacing registry
    /// storage outside this owner.
    pub fn deregister_at(&mut self, index: usize) -> (removed: (K, V))
        requires
            old(self).unique_mapping(),
            index < old(self).entries.len(),
        ensures
            removed == old(self).entries@[index as int],
            final(self).entries@ == old(self).entries@.remove(index as int),
            final(self).entries@.len() + 1 == old(self).entries@.len(),
            final(self).unique_mapping(),
            forall|key: K, value: V|
                #[trigger] final(self).maps_to(key, value)
                    == (old(self).maps_to(key, value) && key != removed.0),
    {
        let ghost before = self.entries@;
        let removed = self.entries.remove(index);
        assert(self.entries@ == before.remove(index as int));
        assert(self.unique_mapping()) by {
            assert forall|left: int, right: int|
                0 <= left < self.entries@.len()
                    && 0 <= right < self.entries@.len()
                    && left != right
                implies #[trigger] self.entries@[left].0 != #[trigger] self.entries@[right].0 by {
                before.remove_ensures(index as int);
                let old_left = if left < index { left } else { left + 1 };
                let old_right = if right < index { right } else { right + 1 };
                assert(0 <= old_left < before.len());
                assert(0 <= old_right < before.len());
                assert(old_left != old_right);
                assert(self.entries@[left] == before[old_left]);
                assert(self.entries@[right] == before[old_right]);
            }
        }
        assert forall|key: K, value: V|
            #[trigger] self.maps_to(key, value)
                == (old(self).maps_to(key, value) && key != removed.0) by {
            has_pair_remove_unique(before, index as int, key, value);
        }
        removed
    }

    /// Remove the pair for `k`. Realises the TLA+ `Deregister(k)` (guard:
    /// `k` is present). Re-establishes UniqueMapping; `k` is afterwards absent.
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
        let filtered = Self::without_key(&self.entries, k);
        let ghost fb = filtered@;
        self.entries = filtered;
        assert forall|kk: K, vv: V| kk != k implies
            (#[trigger] self.maps_to(kk, vv) == old(self).maps_to(kk, vv)) by {
            assert(has_pair(fb, fb.len() as int, kk, vv)
                == has_pair(old(self).entries@, old(self).entries@.len() as int, kk, vv));
        }
        assert(!self.contains_key(k)) by {
            // without_key ensures no entry has key k
            if self.contains_key(k) {
                let i = choose|i: int| 0 <= i < self.entries@.len() && self.entries@[i].0 == k;
                assert(self.entries@[i].0 != k);
            }
        }
    }
}

}
