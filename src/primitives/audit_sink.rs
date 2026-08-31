// Shared append-only chain owner for AuditSink and its named compositions.
//
// The chain operation is a verified parameter. BoundedHash is the public audit-hash instance;
// AdditiveChain is the ReductionStream instance proved by ReductionStreamFromAuditSink.tla.

use vstd::prelude::*;

verus! {

/// Operation used to extend an AuditSink chain.
pub trait ChainOperation: Copy {
    /// Whether the executable operation is defined for this input pair.
    spec fn enabled(&self, previous: u64, operation: u64) -> bool;

    /// Mathematical result of extending the chain.
    spec fn combine_spec(&self, previous: u64, operation: u64) -> u64;

    /// Executable form of `enabled`.
    fn enabled_exec(&self, previous: u64, operation: u64) -> (enabled: bool)
        ensures enabled == self.enabled(previous, operation);

    /// Extend the chain.
    fn combine(&self, previous: u64, operation: u64) -> (result: u64)
        requires self.enabled(previous, operation),
        ensures result == self.combine_spec(previous, operation);
}

/// The bounded content-binding operation used by the public audit sink.
#[derive(Clone, Copy)]
pub struct BoundedHash;

impl ChainOperation for BoundedHash {
    open spec fn enabled(&self, _previous: u64, _operation: u64) -> bool {
        true
    }

    open spec fn combine_spec(&self, previous: u64, operation: u64) -> u64 {
        AuditSink::<BoundedHash>::hash_spec(previous, operation) as u64
    }

    fn enabled_exec(&self, _previous: u64, _operation: u64) -> (enabled: bool) {
        true
    }

    fn combine(&self, previous: u64, operation: u64) -> (result: u64) {
        AuditSink::<BoundedHash>::hash_exec(previous, operation)
    }
}

/// Exact additive chain operation used by ReductionStream.
#[derive(Clone, Copy)]
pub struct AdditiveChain;

impl ChainOperation for AdditiveChain {
    open spec fn enabled(&self, previous: u64, operation: u64) -> bool {
        previous as int + operation as int <= u64::MAX as int
    }

    open spec fn combine_spec(&self, previous: u64, operation: u64) -> u64 {
        (previous + operation) as u64
    }

    fn enabled_exec(&self, previous: u64, operation: u64) -> (enabled: bool) {
        operation <= u64::MAX - previous
    }

    fn combine(&self, previous: u64, operation: u64) -> (result: u64) {
        previous + operation
    }
}

/// One audit record: the operation, predecessor chain value, and resulting chain value.
pub struct AuditEntry {
    /// Operation committed by this entry.
    pub operation: u64,
    /// Chain value immediately before the operation.
    pub prev_hash: u64,
    /// Chain value produced by the operation.
    pub hash: u64,
}

/// An append-only chained log. The operation parameter defaults to the public bounded hash.
pub struct AuditSink<O: ChainOperation = BoundedHash> {
    /// Chain operation instance.
    pub operator: O,
    /// Maximum retained entry count.
    pub max_log_len: usize,
    /// Append-only audit entries.
    pub log: Vec<AuditEntry>,
    /// Chain value after the latest entry, or zero for an empty log.
    pub last_hash: u64,
}

impl AuditSink<BoundedHash> {
    /// Chain hash in the original AuditSink model's integer form.
    pub open spec fn hash_spec(previous: u64, operation: u64) -> int {
        ((previous as int) * 3 + ((operation as int) % 100) + 1) % 100
    }

    /// Execute the public bounded hash instance.
    pub fn hash_exec(previous: u64, operation: u64) -> (result: u64)
        ensures
            result as int == Self::hash_spec(previous, operation),
            result < 100,
    {
        ((previous % 100) * 3 + (operation % 100) + 1) % 100
    }

    /// Construct the public bounded-hash AuditSink.
    pub fn new(max_log_len: usize) -> (sink: AuditSink<BoundedHash>)
        ensures
            sink.max_log_len == max_log_len,
            sink.log@.len() == 0,
            sink.last_hash == 0,
            sink.inv(),
    {
        AuditSink::with_operator(max_log_len, BoundedHash)
    }
}

impl<O: ChainOperation> AuditSink<O> {
    /// Construct an empty chain for a verified operation instance.
    pub fn with_operator(max_log_len: usize, operator: O) -> (sink: AuditSink<O>)
        ensures
            sink.operator == operator,
            sink.max_log_len == max_log_len,
            sink.log@.len() == 0,
            sink.last_hash == 0,
            sink.inv(),
    {
        AuditSink { operator, max_log_len, log: Vec::new(), last_hash: 0 }
    }

    /// Whether the retained log fits within its configured capacity.
    pub open spec fn type_invariant(&self) -> bool {
        self.log.len() <= self.max_log_len
    }

    /// Whether every non-genesis record links to its immediate predecessor.
    pub open spec fn chain_integrity(&self) -> bool {
        forall|index: int|
            #![trigger self.log@[index]]
            1 <= index < self.log.len() ==>
                self.log@[index].prev_hash == self.log@[index - 1].hash
    }

    /// Whether the retained head agrees with the last record or the empty-chain value.
    pub open spec fn hash_consistency(&self) -> bool {
        if self.log.len() > 0 {
            self.last_hash == self.log@[self.log.len() - 1].hash
        } else {
            self.last_hash == 0
        }
    }

    /// Every entry is the configured chain operation applied to its own content.
    pub open spec fn hash_binds_content(&self) -> bool {
        forall|index: int|
            #![trigger self.log@[index]]
            0 <= index < self.log.len() ==>
                self.log@[index].hash
                    == self.operator.combine_spec(
                        self.log@[index].prev_hash,
                        self.log@[index].operation,
                    )
    }

    /// Every stored operation was in the configured operation's executable domain.
    pub open spec fn operations_enabled(&self) -> bool {
        forall|index: int|
            #![trigger self.log@[index]]
            0 <= index < self.log.len() ==>
                self.operator.enabled(
                    self.log@[index].prev_hash,
                    self.log@[index].operation,
                )
    }

    /// Whether the first retained record links to the genesis hash.
    pub open spec fn genesis_consistency(&self) -> bool {
        self.log.len() > 0 ==> self.log@[0].prev_hash == 0
    }

    /// Whether all append-only chain obligations hold.
    pub open spec fn inv(&self) -> bool {
        &&& self.type_invariant()
        &&& self.chain_integrity()
        &&& self.hash_consistency()
        &&& self.hash_binds_content()
        &&& self.operations_enabled()
        &&& self.genesis_consistency()
    }

    /// Append one operation through the chain owner.
    pub fn record(&mut self, operation: u64) -> (accepted: bool)
        requires
            old(self).inv(),
            old(self).operator.enabled(old(self).last_hash, operation),
        ensures
            final(self).inv(),
            final(self).operator == old(self).operator,
            final(self).max_log_len == old(self).max_log_len,
            accepted == (old(self).log.len() < old(self).max_log_len),
            accepted ==> {
                &&& final(self).log@.len() == old(self).log@.len() + 1
                &&& final(self).last_hash
                    == old(self).operator.combine_spec(old(self).last_hash, operation)
                &&& final(self).log@[old(self).log@.len() as int].operation == operation
                &&& final(self).log@[old(self).log@.len() as int].prev_hash
                    == old(self).last_hash
                &&& forall|index: int|
                    #![trigger final(self).log@[index]]
                    0 <= index < old(self).log@.len() ==>
                        final(self).log@[index] == old(self).log@[index]
            },
            !accepted ==>
                final(self).log@ == old(self).log@
                    && final(self).last_hash == old(self).last_hash,
    {
        if self.log.len() < self.max_log_len {
            let new_hash = self.operator.combine(self.last_hash, operation);
            let entry = AuditEntry {
                operation,
                prev_hash: self.last_hash,
                hash: new_hash,
            };
            assert(self.log@.len() > 0 ==>
                self.last_hash == self.log@[self.log@.len() - 1].hash);
            self.log.push(entry);
            self.last_hash = new_hash;
            assert(self.chain_integrity()) by {
                assert forall|index: int| #![trigger self.log@[index]]
                    1 <= index < self.log.len() implies
                        self.log@[index].prev_hash == self.log@[index - 1].hash by {
                    if index < self.log.len() - 1 {
                    }
                }
            }
            assert(self.hash_binds_content()) by {
                assert forall|index: int| #![trigger self.log@[index]]
                    0 <= index < self.log.len() implies
                        self.log@[index].hash == self.operator.combine_spec(
                            self.log@[index].prev_hash,
                            self.log@[index].operation,
                        ) by {
                    if index < self.log.len() - 1 {
                    }
                }
            }
            assert(self.operations_enabled()) by {
                assert forall|index: int| #![trigger self.log@[index]]
                    0 <= index < self.log.len() implies
                        self.operator.enabled(
                            self.log@[index].prev_hash,
                            self.log@[index].operation,
                        ) by {
                    if index < self.log.len() - 1 {
                    }
                }
            }
            assert(self.genesis_consistency());
            true
        } else {
            false
        }
    }

    /// Recompute the entire configured chain from the zero genesis.
    pub fn validate(&self) -> (valid: bool)
        ensures valid == self.inv(),
    {
        if self.log.len() > self.max_log_len {
            return false;
        }

        let length = self.log.len();
        let mut index: usize = 0;
        let mut expected_previous: u64 = 0;
        while index < length
            invariant
                index <= length,
                length == self.log.len(),
                self.log.len() <= self.max_log_len,
                index == 0 ==> expected_previous == 0,
                index > 0 ==> expected_previous == self.log@[index as int - 1].hash,
                forall|entry: int| 0 <= entry < index ==>
                    #[trigger] self.log@[entry].hash == self.operator.combine_spec(
                        self.log@[entry].prev_hash,
                        self.log@[entry].operation,
                    ),
                forall|entry: int| 0 <= entry < index ==>
                    #[trigger] self.operator.enabled(
                        self.log@[entry].prev_hash,
                        self.log@[entry].operation,
                    ),
                forall|entry: int| 1 <= entry < index ==>
                    #[trigger] self.log@[entry].prev_hash == self.log@[entry - 1].hash,
                index > 0 ==> self.log@[0].prev_hash == 0,
            decreases length - index,
        {
            if self.log[index].prev_hash != expected_previous {
                return false;
            }
            if !self.operator.enabled_exec(self.log[index].prev_hash, self.log[index].operation) {
                return false;
            }
            let expected_hash = self.operator.combine(
                self.log[index].prev_hash,
                self.log[index].operation,
            );
            if self.log[index].hash != expected_hash {
                return false;
            }
            expected_previous = self.log[index].hash;
            index = index + 1;
        }

        if self.last_hash != expected_previous {
            return false;
        }
        true
    }
}

}
