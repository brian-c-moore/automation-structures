// ReductionStream's additive and maximum instances.
//
// ReductionStream's model state is `result, pos` over a constant source. The
// additive Reducer retains an explicit prefix/suffix decomposition so the
// constant source and exactly-once movement remain executable:
// `pos = processed.len()`, `Src = original`, and
// `processed ++ remaining = original`. The batch sum and max loops are two
// named instances of the same ordered prefix-fold interface.
//
// Overflow ceiling: values bounded to <= 1e9, inputs to <= 1e9 elements,
// so the accumulator stays under 1e18 < u64::MAX.

use vstd::prelude::*;

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

/// Additive ReductionStream instance with explicit processed/remaining views.
pub struct Reducer {
    pub result: u64,
    pub processed: Vec<u64>,
    pub remaining: Vec<u64>,
    pub original: Ghost<Seq<u64>>,
}

impl Reducer {
    /// Source decomposition used by the ReductionStream state mapping.
    pub open spec fn partition(&self) -> bool {
        crate::connectives::accumulator::carries(
            self.original@,
            self.processed@,
            self.remaining@,
        )
    }

    /// Additive instance of `ConsumedPrefixFold`.
    pub open spec fn aggregate(&self) -> bool {
        self.result as int == sum_spec(self.processed@)
    }

    /// Overflow ceiling: all values <= 1e9, total input <= 1e9 elements.
    pub open spec fn bounded(&self) -> bool {
        &&& forall|k: int| 0 <= k < self.processed@.len() ==> self.processed@[k] <= 1_000_000_000u64
        &&& forall|k: int| 0 <= k < self.remaining@.len() ==> self.remaining@[k] <= 1_000_000_000u64
        &&& self.original@.len() <= 1_000_000_000
    }

    /// Empty consumed prefix, full remaining suffix, and additive identity.
    pub fn new(items: Vec<u64>) -> (r: Reducer)
        requires
            forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000_000u64,
            items@.len() <= 1_000_000_000,
        ensures
            r.partition(),
            r.aggregate(),
            r.bounded(),
            r.original@ == items@,
            r.remaining@ == items@,
    {
        let ghost orig = items@;
        let r = Reducer {
            result: 0,
            processed: Vec::new(),
            remaining: items,
            original: Ghost(orig),
        };
        proof {
            assert(r.processed@.len() == 0);
            assert(r.processed@ + r.remaining@ =~= r.original@);
            assert(sum_spec(r.processed@) == 0);
        }
        r
    }

    pub fn done(&self) -> (d: bool)
        ensures
            d == (self.remaining@.len() == 0),
    {
        self.remaining.len() == 0
    }

    /// Consume the next value exactly once and extend the additive prefix fold.
    pub fn process(&mut self)
        requires
            old(self).remaining@.len() > 0,
            old(self).partition(),
            old(self).aggregate(),
            old(self).bounded(),
        ensures
            final(self).partition(),
            final(self).aggregate(),
            final(self).bounded(),
            final(self).original@ == old(self).original@,
            final(self).remaining@.len() == old(self).remaining@.len() - 1,
            final(self).processed@ == old(self).processed@.push(old(self).remaining@[0]),
            final(self).remaining@ == old(self).remaining@.subrange(
                1, old(self).remaining@.len() as int),
            final(self).result == old(self).result + old(self).remaining@[0],
    {
        let ghost p = self.processed@;
        let ghost r = self.remaining@;
        let x = self.remaining[0];
        assert(crate::connectives::ordering_pass::selects_first(self.remaining@, x));

        assert(self.processed@.len() <= self.original@.len()) by {
            assert((p + r).len() == p.len() + r.len());
        }
        proof {
            lemma_sum_to_bounded(self.processed@, self.processed@.len() as int);
        }

        let removed = self.remaining.remove(0);
        let _ = removed;
        self.processed.push(x);
        self.result = self.result + x;

        proof {
            lemma_sum_push(p, x);
            assert(self.remaining@ =~= r.subrange(1, r.len() as int));
            assert(self.processed@ =~= p.push(x));
            assert(r[0] == x);
            assert(self.processed@ + self.remaining@ =~= self.original@);
            assert(sum_spec(self.processed@) == sum_spec(p) + x as int);
            assert(forall|k: int| 0 <= k < self.remaining@.len()
                ==> self.remaining@[k] <= 1_000_000_000u64);
            assert(forall|k: int| 0 <= k < self.processed@.len()
                ==> self.processed@[k] <= 1_000_000_000u64);
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
