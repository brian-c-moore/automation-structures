// AuditSink-backed ReductionStream named composition.
//
// ReductionStreamFromAuditSink.tla has no held glue state: the source is
// immutable configuration, the AuditSink log is the consumed prefix,
// `result` is `last_hash`, and `pos` is `Len(log)`. AdditiveChain instantiates
// AuditSink's operation with the reduction operator.
//
// Overflow ceiling: values bounded to <= 1e9, inputs to <= 1e9 elements,
// so the accumulator stays under 1e18 < u64::MAX.

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::primitives::audit_sink::{AdditiveChain, AuditSink, ChainOperation};

verus! {

/// Fold of `s[0..n]`.
pub open spec fn sum_to(s: Seq<u64>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else if n > s.len() as int {
        0
    } else {
        s[n - 1] as int + sum_to(s, n - 1)
    }
}

/// Fold of the entire sequence.
pub open spec fn sum_spec(s: Seq<u64>) -> int {
    sum_to(s, s.len() as int)
}

/// Partial fold bounded by (max element) * n.
pub proof fn lemma_sum_to_bounded(s: Seq<u64>, n: int)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] <= 1_000_000_000u64,
        0 <= n <= s.len() as int,
    ensures
        sum_to(s, n) <= 1_000_000_000 * n,
    decreases n,
{
    if n > 0 {
        lemma_sum_to_bounded(s, n - 1);
    }
}

/// sum_to(s.push(x), n) == sum_to(s, n) for 0 <= n <= |s|.
proof fn lemma_sum_to_push_prefix(s: Seq<u64>, x: u64, n: int)
    requires
        0 <= n <= s.len() as int,
    ensures
        sum_to(s.push(x), n) == sum_to(s, n),
    decreases n,
{
    if n > 0 {
        lemma_sum_to_push_prefix(s, x, n - 1);
        assert(s.push(x)[n - 1] == s[n - 1]);
    }
}

/// sum_spec(s.push(x)) == sum_spec(s) + x.
/// Re-association: the fold of a prefix plus one element equals the fold of the whole.
pub proof fn lemma_sum_push(s: Seq<u64>, x: u64)
    ensures
        sum_spec(s.push(x)) == sum_spec(s) + x as int,
{
    let t = s.push(x);
    let n = s.len() as int;
    assert(t.len() == n + 1);
    lemma_sum_to_push_prefix(s, x, n);
    assert(t[n] == x);
    assert(sum_to(t, n + 1) == t[n] as int + sum_to(t, n));
}

/// Additive ReductionStream assembled from the AuditSink owner.
pub struct Reducer {
    /// Immutable reduction source.
    pub source: Vec<u64>,
    /// Owner of the consumed prefix, position, and result.
    pub audit: AuditSink<AdditiveChain>,
}

impl Reducer {
    /// AuditSink's log is exactly the consumed source prefix.
    pub open spec fn prefix_binding(&self) -> bool {
        &&& self.audit.log.len() <= self.source.len()
        &&& forall|index: int|
            #![trigger self.audit.log@[index]]
            0 <= index < self.audit.log.len() ==>
                self.audit.log@[index].operation == self.source@[index]
    }

    /// AuditSink's carry is the fold of the consumed source prefix.
    pub open spec fn aggregate(&self) -> bool {
        self.audit.last_hash as int == sum_to(self.source@, self.audit.log.len() as int)
    }

    /// Overflow ceiling for the additive AuditSink operation.
    pub open spec fn bounded(&self) -> bool {
        &&& forall|k: int| 0 <= k < self.source@.len() ==> self.source@[k] <= 1_000_000_000u64
        &&& self.source@.len() <= 1_000_000_000
    }

    /// Complete representation invariant of the named composition.
    pub open spec fn inv(&self) -> bool {
        &&& self.audit.inv()
        &&& self.audit.max_log_len == self.source.len()
        &&& self.prefix_binding()
        &&& self.aggregate()
        &&& self.bounded()
    }

    /// Empty AuditSink over the immutable source.
    pub fn new(items: Vec<u64>) -> (r: Reducer)
        requires
            forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
            items@.len() <= 1_000_000_000,
        ensures
            r.inv(),
            r.source@ == items@,
            r.audit.log@.len() == 0,
            r.audit.last_hash == 0,
    {
        let audit = AuditSink::with_operator(items.len(), AdditiveChain);
        let r = Reducer { source: items, audit };
        proof {
            assert(r.audit.log@.len() == 0);
            assert(sum_to(r.source@, 0) == 0);
        }
        r
    }

    /// Number of source elements already consumed.
    pub fn position(&self) -> (position: usize)
        ensures position == self.audit.log@.len(),
    {
        self.audit.log.len()
    }

    /// Current additive result, projected from AuditSink's carry.
    pub fn result(&self) -> (result: u64)
        ensures result == self.audit.last_hash,
    {
        self.audit.last_hash
    }

    /// Number of source elements not yet consumed.
    pub fn remaining_len(&self) -> (remaining: usize)
        requires self.prefix_binding(),
        ensures remaining == self.source@.len() - self.audit.log@.len(),
    {
        self.source.len() - self.audit.log.len()
    }

    /// Whether the complete source prefix has been reduced.
    pub fn done(&self) -> (d: bool)
        requires self.prefix_binding(),
        ensures
            d == (self.audit.log@.len() == self.source@.len()),
    {
        self.audit.log.len() == self.source.len()
    }

    /// Consume the next source value through AuditSink's `Record` action.
    pub fn process(&mut self)
        requires
            old(self).inv(),
            old(self).audit.log@.len() < old(self).source@.len(),
        ensures
            final(self).inv(),
            final(self).source@ == old(self).source@,
            final(self).audit.log@.len() == old(self).audit.log@.len() + 1,
            final(self).audit.last_hash
                == old(self).audit.last_hash
                    + old(self).source@[old(self).audit.log@.len() as int],
    {
        let old_position = self.audit.log.len();
        let x = self.source[old_position];
        let ghost old_log = self.audit.log@;
        let ghost source = self.source@;
        proof {
            lemma_sum_to_bounded(self.source@, old_position as int);
            assert(self.audit.last_hash as int
                == sum_to(self.source@, old_position as int));
            assert(self.audit.last_hash as int <= 1_000_000_000 * old_position as int);
            assert(x <= 1_000_000_000u64);
            assert(old_position < 1_000_000_000usize);
            assert(self.audit.last_hash as int + x as int <= 1_000_000_000_000_000_000int);
            assert(1_000_000_000_000_000_000int < u64::MAX as int);
            assert(self.audit.operator.enabled(self.audit.last_hash, x));
        }
        let accepted = self.audit.record(x);
        assert(accepted);
        let _ = accepted;

        proof {
            assert(self.audit.log@[old_position as int].operation == x);
            assert(self.prefix_binding()) by {
                assert forall|index: int|
                    #![trigger self.audit.log@[index]]
                    0 <= index < self.audit.log.len() implies
                        self.audit.log@[index].operation == self.source@[index] by {
                    if index < old_position {
                        assert(self.audit.log@[index] == old_log[index]);
                    } else {
                        assert(index == old_position);
                    }
                }
            }
            assert(sum_to(source, old_position as int + 1)
                == source[old_position as int] as int
                    + sum_to(source, old_position as int));
            assert(self.aggregate());
        }
    }
}

// ---------------------------------------------------------------------------
// Operator-generic batch fold. `Reducer` remains the incremental sum state
// machine above. `reduce_sum` and `reduce_max` instantiate the standalone fold
// with distinct operators and identities. Genericity lives at the
// spec level (`fold_to`, parametrized by a `spec_fn` operator -- Verus's
// pure, total ghost-function type, callable directly in spec/proof context;
// an ordinary generic `F: Fn(u64,u64)->u64` cannot be called from ghost code
// in this Verus version). `reduce_sum`/`reduce_max` are two concrete exec
// entry points, each proven against the SAME ordered-prefix spec instantiated
// with its own operator. No reassociation theorem or arbitrary executable
// operator is claimed.
/// Fold the first `n` values of `s` from `identity` with `op`.
pub open spec fn fold_to(s: Seq<u64>, n: int, identity: u64, op: spec_fn(u64, u64) -> u64) -> u64
    decreases n,
{
    if n <= 0 {
        identity
    } else if n > s.len() as int {
        identity
    } else {
        op(fold_to(s, n - 1, identity, op), s[n - 1])
    }
}

/// Sum-specific boundedness for the generic fold's exec loop: mirrors
/// lemma_sum_to_bounded above. Boundedness is operator-specific (sum needs a
/// multiplicative bound; max needs only the input ceiling), so it sits outside
/// the generic lemmas.
proof fn lemma_fold_to_bounded_sum(s: Seq<u64>, n: int)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] <= 1_000_000_000u64,
        0 <= n <= s.len() as int,
    ensures
        fold_to(s, n, 0, |a: u64, b: u64| (a + b) as u64) <= 1_000_000_000 * n,
    decreases n,
{
    if n > 0 {
        lemma_fold_to_bounded_sum(s, n - 1);
    }
}

/// Additive fold, stated against the generic fold_to spec. The value is
/// identical to sum_spec; this entry point instantiates the generic spec rather
/// than the sum-specific one above.
pub fn reduce_sum(items: &[u64]) -> (result: u64)
    requires
        forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
        items@.len() <= 1_000_000_000,
    ensures
        result as int == fold_to(items@, items@.len() as int, 0, |a: u64, b: u64| (a + b) as u64) as int,
{
    let n: usize = items.len();
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            n <= 1_000_000_000,
            forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
            result as int == fold_to(items@, i as int, 0, |a: u64, b: u64| (a + b) as u64) as int,
        decreases n - i,
    {
        proof {
            lemma_fold_to_bounded_sum(items@, i as int);
        }
        result = result + items[i];
        i = i + 1;
    }
    result
}

/// Max fold: a second, idempotent instance of the same ordered-prefix spec.
pub fn reduce_max(items: &[u64]) -> (result: u64)
    requires
        forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
        items@.len() <= 1_000_000_000,
    ensures
        result as int == fold_to(items@, items@.len() as int, 0, |a: u64, b: u64| if a > b { a } else { b }) as int,
{
    let n: usize = items.len();
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
            result <= 1_000_000_000u64,
            result as int == fold_to(items@, i as int, 0, |a: u64, b: u64| if a > b { a } else { b }) as int,
        decreases n - i,
    {
        if items[i] > result {
            result = items[i];
        }
        i = i + 1;
    }
    result
}

}
