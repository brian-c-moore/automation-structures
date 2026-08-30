// Executable carrier for AuditSink.tla and its cryptographic-assumption
// boundary. Each record stores its operation, predecessor hash, and content-
// binding hash. The maintained state predicates are:
//
//   TypeInvariant     == last_hash ∈ Nat /\ Len(log) <= MaxLogLen
//   ChainIntegrity    == ∀ i ∈ 2..Len(log): log[i].prev_hash = log[i-1].hash
//   HashConsistency   == IF Len(log) > 0 THEN last_hash = log[Len(log)].hash
//                                          ELSE last_hash = 0
//   HashBindsContent  == ∀ i: log[i].hash = Hash(log[i].prev_hash, log[i].operation)
//
// `record` implements the length-guarded Record action, appends
// `[op, last_hash, Hash(last_hash, op)]`, and advances `last_hash`.
// HashConsistency supplies the predecessor-hash fact needed to preserve
// ChainIntegrity. Exact prefix preservation is an action postcondition because
// the state predicates alone do not imply append framing.
//
// The executable hash is `(prev*3 + op + 1) % 100`, with operands reduced
// before arithmetic. It binds content but is not collision-resistant.
// Cryptographic tamper evidence therefore still relies on the external
// `HashCR` premise used by AuditSink_Proof; this carrier establishes only the
// concrete chain predicates and non-colliding alteration checks.

use vstd::prelude::*;

verus! {

/// One audit record: the operation, the hash it chains onto, and its own hash.
pub struct AuditEntry {
    pub operation: u64,
    pub prev_hash: u64,
    pub hash: u64,
}

/// An append-only hash-chained log with a running `last_hash`.
pub struct AuditSink {
    pub max_log_len: usize,
    pub log: Vec<AuditEntry>,
    pub last_hash: u64,
}

impl AuditSink {
    // ── Hash (TLA+ Hash) ────────────────────────────────────────────────

    /// Chain hash: (prev*3 + op%100 + 1) % 100. Spec form (int).
    pub open spec fn hash_spec(prev: u64, op: u64) -> int {
        ((prev as int) * 3 + ((op as int) % 100) + 1) % 100
    }

    /// Executable bounded realization of the model hash. Reducing `prev` before
    /// multiplication is modularly equivalent and makes recomputation safe even
    /// when validating externally stored or tampered records.
    pub fn hash_exec(prev: u64, op: u64) -> (h: u64)
        ensures
            h as int == Self::hash_spec(prev, op),
            h < 100,
    {
        ((prev % 100) * 3 + (op % 100) + 1) % 100
    }

    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ `TypeInvariant` (the structural clause; last_hash ∈ Nat is u64).
    pub open spec fn type_invariant(&self) -> bool {
        self.log.len() <= self.max_log_len
    }

    /// TLA+ `ChainIntegrity` (0-indexed: each record's prev_hash equals the
    /// previous record's hash).
    pub open spec fn chain_integrity(&self) -> bool {
        forall|i: int|
            #![trigger self.log@[i]]
            1 <= i < self.log.len() ==> self.log@[i].prev_hash == self.log@[i - 1].hash
    }

    /// TLA+ `HashConsistency`.
    pub open spec fn hash_consistency(&self) -> bool {
        if self.log.len() > 0 {
            self.last_hash == self.log@[self.log.len() - 1].hash
        } else {
            self.last_hash == 0
        }
    }

    /// TLA+ `HashBindsContent`: each record's stored hash equals Hash of its own
    /// (prev_hash, operation) -- the hash binds content, not just position.
    pub open spec fn hash_binds_content(&self) -> bool {
        forall|i: int|
            #![trigger self.log@[i]]
            0 <= i < self.log.len()
                ==> self.log@[i].hash as int
                        == Self::hash_spec(self.log@[i].prev_hash, self.log@[i].operation)
    }

    /// Derived range bound (Hash always returns < 100); supports overflow-free
    /// recompute. Not one of the checked TLA+ invariants.
    pub open spec fn last_hash_bounded(&self) -> bool {
        self.last_hash < 100
    }

    /// Reachable-chain genesis: the first record is chained from Init's zero.
    pub open spec fn genesis_consistency(&self) -> bool {
        self.log.len() > 0 ==> self.log@[0].prev_hash == 0
    }

    /// Full maintained invariant.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.chain_integrity()
        &&& self.hash_consistency()
        &&& self.hash_binds_content()
        &&& self.last_hash_bounded()
        &&& self.genesis_consistency()
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Empty log, last_hash 0. Realises the TLA+ `Init` predicate.
    pub fn new(max_log_len: usize) -> (s: AuditSink)
        ensures
            s.max_log_len == max_log_len,
            s.log@.len() == 0,
            s.last_hash == 0,
            s.inv(),
    {
        AuditSink { max_log_len, log: Vec::new(), last_hash: 0 }
    }

    // ── Record (TLA+ Record) ────────────────────────────────────────────

    /// Append a record for operation `op`. The TLA+ guard Len(log) < MaxLogLen
    /// is modelled as a bool-returning try; on success the new record chains
    /// onto last_hash and last_hash advances to the new hash.
    pub fn record(&mut self, op: u64) -> (ok: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).max_log_len == old(self).max_log_len,
            ok == (old(self).log.len() < old(self).max_log_len),
            ok ==> {
                &&& final(self).log@.len() == old(self).log@.len() + 1
                &&& final(self).last_hash as int == Self::hash_spec(old(self).last_hash, op)
                &&& final(self).log@[old(self).log@.len() as int].operation == op
                &&& final(self).log@[old(self).log@.len() as int].prev_hash == old(self).last_hash
                // Append framing: without this the contract of an
                // append-only log does not say the log is append-only: the length
                // and the new record are constrained, the existing records are not.
                &&& forall|i: int|
                        #![trigger final(self).log@[i]]
                        0 <= i < old(self).log@.len() ==> final(self).log@[i] == old(self).log@[i]
            },
            !ok ==> final(self).log@ == old(self).log@ && final(self).last_hash == old(self).last_hash,
    {
        if self.log.len() < self.max_log_len {
            let new_hash = Self::hash_exec(self.last_hash, op);
            let entry = AuditEntry { operation: op, prev_hash: self.last_hash, hash: new_hash };
            // The new record chains onto the previous one: its prev_hash is the
            // old last_hash, which by HashConsistency is the previous record's
            // hash. So appending it preserves ChainIntegrity.
            assert(self.log@.len() > 0 ==> self.last_hash == self.log@[self.log@.len() - 1].hash);
            self.log.push(entry);
            self.last_hash = new_hash;
            assert(self.chain_integrity()) by {
                assert forall|i: int| #![trigger self.log@[i]]
                    1 <= i < self.log.len() implies self.log@[i].prev_hash == self.log@[i - 1].hash by {
                    if i < self.log.len() - 1 {
                        // unchanged prefix entry
                    }
                }
            }
            assert(self.hash_binds_content()) by {
                assert forall|i: int| #![trigger self.log@[i]]
                    0 <= i < self.log.len() implies self.log@[i].hash as int
                        == Self::hash_spec(self.log@[i].prev_hash, self.log@[i].operation) by {
                    if i < self.log.len() - 1 {
                        // unchanged prefix entry: held by old(self).hash_binds_content()
                    }
                    // i == len-1: the new entry; new_hash == hash_spec(prev_hash, op)
                    // by hash_exec's ensures.
                }
            }
            assert(self.genesis_consistency());
            true
        } else {
            false
        }
    }

    /// Recompute the complete concrete chain from the zero genesis. This
    /// detects any record/link alteration that no longer matches
    /// the stored chain. Cryptographic resistance to a deliberately constructed
    /// collision remains the external `HashCR` premise of the TLAPS theorem.
    pub fn validate(&self) -> (ok: bool)
        ensures ok == self.inv(),
    {
        if self.log.len() > self.max_log_len {
            return false;
        }

        let len = self.log.len();
        let mut i: usize = 0;
        let mut expected_prev: u64 = 0;
        while i < len
            invariant
                i <= len,
                len == self.log.len(),
                self.log.len() <= self.max_log_len,
                expected_prev < 100,
                i == 0 ==> expected_prev == 0,
                i > 0 ==> expected_prev == self.log@[i as int - 1].hash,
                forall|k: int| 0 <= k < i ==> #[trigger] self.log@[k].hash as int
                    == Self::hash_spec(self.log@[k].prev_hash, self.log@[k].operation),
                forall|k: int| 1 <= k < i ==> #[trigger] self.log@[k].prev_hash
                    == self.log@[k - 1].hash,
                i > 0 ==> self.log@[0].prev_hash == 0,
            decreases len - i,
        {
            if self.log[i].prev_hash != expected_prev {
                return false;
            }
            let expected_hash = Self::hash_exec(self.log[i].prev_hash, self.log[i].operation);
            if self.log[i].hash != expected_hash {
                return false;
            }
            expected_prev = self.log[i].hash;
            i = i + 1;
        }

        if self.last_hash != expected_prev {
            return false;
        }
        true
    }
}

}
