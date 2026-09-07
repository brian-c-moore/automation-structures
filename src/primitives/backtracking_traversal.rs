// Reversible traversal; its default modulo-3 profile is BacktrackingTraversalUndo.tla, bound by
// BacktrackingTraversalUndo.cfg. A descent records the pre-mutation value and
// chosen delta in an undo token, then applies Mutate in the same commit. An
// ascent applies the recorded inverse and pops both path and ledger. The model
// remains order-parametric: recorded-leaf validity is not eventual
// coverage of every leaf.

use vstd::prelude::*;

verus! {

/// Pure reversible data operation; path and undo-ledger ownership stay in the traversal.
pub trait TraversalDomain<T: Copy> {
    /// Retained mutation descriptor.
    type Delta: Copy;
    /// Number of admitted positive branch choices.
    spec fn branches(&self) -> u64;
    /// Membership of a retained auxiliary value.
    spec fn valid_aux(&self, value: T) -> bool;
    /// Membership of a retained mutation descriptor.
    spec fn valid_delta(&self, delta: Self::Delta) -> bool;
    /// Result of an admitted mutation.
    spec fn mutated(&self, value: T, delta: Self::Delta) -> T;
    /// Result of restoring an admitted mutation.
    spec fn undone(&self, value: T, delta: Self::Delta) -> T;
    /// Observe the branch count.
    fn branch_count(&self) -> (count: u64) ensures count == self.branches();
    /// Decide whether a mutation descriptor is admitted.
    fn valid_delta_exec(&self, delta: Self::Delta) -> (yes: bool) ensures yes == self.valid_delta(delta);
    /// Compute domain data without retaining another traversal or undo ledger.
    fn mutate(&self, value: T, delta: Self::Delta) -> (result: T)
        requires self.valid_aux(value), self.valid_delta(delta),
        ensures self.valid_aux(result), result == self.mutated(value,delta);
    /// Restore domain data from the retained descriptor.
    fn undo(&self, value: T, delta: Self::Delta) -> (result: T)
        requires self.valid_aux(value), self.valid_delta(delta),
        ensures self.valid_aux(result), result == self.undone(value,delta);
    /// Domain law required by the owner's restoration proof, not a trusted callback.
    proof fn inverse(&self, value: T, delta: Self::Delta)
        requires self.valid_aux(value), self.valid_delta(delta),
        ensures self.undone(self.mutated(value,delta),delta) == value;
}

impl TraversalDomain<u64> for u64 {
    type Delta = u64;
    open spec fn branches(&self) -> u64 { *self }
    open spec fn valid_aux(&self, value: u64) -> bool { value < 3 }
    open spec fn valid_delta(&self, delta: u64) -> bool { 1 <= delta <= 2 }
    open spec fn mutated(&self, value: u64, delta: u64) -> u64 {
        ((value as int + delta as int) % 3) as u64
    }
    open spec fn undone(&self, value: u64, delta: u64) -> u64 {
        ((value as int + (3 - delta as int)) % 3) as u64
    }
    fn branch_count(&self) -> (count: u64) { *self }
    fn valid_delta_exec(&self, delta: u64) -> (yes: bool) { 1 <= delta && delta <= 2 }
    fn mutate(&self, value: u64, delta: u64) -> (result: u64) { modulo_mutate_exec(value,delta) }
    fn undo(&self, value: u64, delta: u64) -> (result: u64) { modulo_undo_exec(value,delta) }
    proof fn inverse(&self, value: u64, delta: u64) { modulo_lemma_undo_inverts(value,delta); }
}

/// Reversible auxiliary-state mutation retained for one descent.
pub struct UndoToken<T: Copy = u64, Delta: Copy = u64> {
    /// Auxiliary value before the descent.
    pub saved: T,
    /// Mutation delta applied by the descent.
    pub delta: Delta,
}

/// Reversible depth-first traversal owner.
pub struct BacktrackingTraversal<T: Copy = u64, D: TraversalDomain<T> = u64> {
    /// Pure branch/mutation domain; the default is the number of branch choices.
    pub branch_factor: D,
    /// Required depth of a complete leaf path.
    pub max_depth: usize,
    /// Auxiliary value at the root.
    pub init_aux: T,
    /// Current branch-choice path.
    pub path: Vec<u64>,
    /// Current auxiliary value.
    pub aux: T,
    /// Undo tokens aligned with the current path.
    pub ledger: Vec<UndoToken<T, D::Delta>>,
    /// A Vec is the executable representation of the TLA+ visited set;
    /// `visited_unique` and Visit's freshness guard preserve set semantics.
    pub visited: Vec<Vec<u64>>,
}

impl<T: Copy, D: TraversalDomain<T>> BacktrackingTraversal<T, D> {
    proof fn lemma_visited_frame(&self, prior: &Self)
        requires self.visited@ == prior.visited@, self.branch_factor == prior.branch_factor,
            self.max_depth == prior.max_depth, prior.recorded_leaf_validity(), prior.visited_unique(),
        ensures self.recorded_leaf_validity(), self.visited_unique(),
    {
        assert forall|e: int| 0 <= e < self.visited.len() implies {
            &&& #[trigger] self.visited@[e].len() == self.max_depth
            &&& forall|j: int| 0 <= j < self.max_depth as int
                ==> 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor.branches()
        } by {
            assert(self.visited@[e] == prior.visited@[e]);
            assert(prior.visited@[e].len() == prior.max_depth);
            assert forall|j: int| 0 <= j < self.max_depth as int
                implies 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor.branches() by {
                assert(self.visited@[e]@[j] == prior.visited@[e]@[j]);
            }
        }
    }

    /// Complete logical owner frame; allocation capacity is deliberately unobserved.
    pub open spec fn same_state(&self, other: &Self) -> bool {
        &&& self.branch_factor == other.branch_factor
        &&& self.max_depth == other.max_depth
        &&& self.init_aux == other.init_aux
        &&& self.path@ == other.path@
        &&& self.aux == other.aux
        &&& self.ledger@ == other.ledger@
        &&& self.visited@ == other.visited@
    }

    /// Fallibly admit path and undo storage for every configured depth.
    ///
    /// # Errors
    /// Returns the allocation error and unchanged domain/initial value.
    pub fn try_new(branch_factor: D, max_depth: usize, init_aux: T)
        -> (result: Result<Self,(std::collections::TryReserveError,D,T)>)
        requires branch_factor.valid_aux(init_aux),
        ensures match result {
            Ok(t) => t.inv() && t.branch_factor == branch_factor && t.max_depth == max_depth
                && t.init_aux == init_aux && t.aux == init_aux && t.path.len() == 0
                && t.ledger.len() == 0 && t.visited.len() == 0,
            Err((_,domain,value)) => domain == branch_factor && value == init_aux,
        },
    {
        let mut path = Vec::new();
        if let Err(e) = path.try_reserve(max_depth) { return Err((e,branch_factor,init_aux)); }
        let mut ledger = Vec::new();
        if let Err(e) = ledger.try_reserve(max_depth) { return Err((e,branch_factor,init_aux)); }
        Ok(Self::initialize(branch_factor,max_depth,init_aux,path,ledger))
    }

    fn initialize(branch_factor: D, max_depth: usize, init_aux: T,
        path: Vec<u64>, ledger: Vec<UndoToken<T,D::Delta>>) -> (t: Self)
        requires branch_factor.valid_aux(init_aux), path.len() == 0, ledger.len() == 0,
        ensures t.inv(), t.branch_factor == branch_factor, t.max_depth == max_depth,
            t.init_aux == init_aux, t.aux == init_aux, t.path.len() == 0, t.ledger.len() == 0, t.visited.len() == 0,
    {
        Self { branch_factor,max_depth,init_aux,path,aux:init_aux,ledger,visited:Vec::new() }
    }

    /// Reserve retained visit slots; the consumer supplies visit-count policy.
    ///
    /// # Errors
    /// Allocation refusal preserves all logical traversal state.
    pub fn try_reserve_visits(&mut self, additional: usize) -> (result: Result<(),std::collections::TryReserveError>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).same_state(old(self)),
    { self.visited.try_reserve(additional) }

    /// Whether path, ledger, auxiliary value, and choices have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.branch_factor.valid_aux(self.init_aux)
        &&& self.branch_factor.valid_aux(self.aux)
        &&& self.path.len() <= self.max_depth
        &&& (forall|i: int| 0 <= i < self.path.len()
                ==> 1 <= #[trigger] self.path@[i] <= self.branch_factor.branches())
        &&& (forall|i: int| 0 <= i < self.ledger.len() ==> {
                &&& self.branch_factor.valid_aux(#[trigger] self.ledger@[i].saved)
                &&& self.branch_factor.valid_delta(self.ledger@[i].delta)
            })
    }

    /// Pairing: one token per outstanding descent and the live value is
    /// exactly the mutation named by the head token.
    pub open spec fn pairing(&self) -> bool {
        &&& self.ledger.len() == self.path.len()
        &&& (self.path.len() == 0 ==> self.aux == self.init_aux)
        &&& (self.path.len() > 0 ==> self.aux
            == self.branch_factor.mutated(
                self.ledger@[self.path.len() - 1].saved,
                self.ledger@[self.path.len() - 1].delta))
    }

    /// StateRestoration: the ledger is a checkpoint chain, not a depth-derived
    /// counter sequence.
    pub open spec fn state_restoration(&self) -> bool {
        &&& (self.ledger.len() >= 1 ==> self.ledger@[0].saved == self.init_aux)
        &&& (forall|i: int| 1 <= i < self.ledger.len() ==>
            #[trigger] self.ledger@[i].saved
                == self.branch_factor.mutated(self.ledger@[i - 1].saved, self.ledger@[i - 1].delta))
    }

    /// Whether every recorded visit is a valid full-depth leaf.
    pub open spec fn recorded_leaf_validity(&self) -> bool {
        forall|e: int| 0 <= e < self.visited.len() ==> {
            &&& #[trigger] self.visited@[e].len() == self.max_depth
            &&& (forall|j: int| 0 <= j < self.max_depth as int
                ==> 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor.branches())
        }
    }

    /// Compatibility alias for [`Self::recorded_leaf_validity`].
    ///
    /// This predicate does not claim eventual or exhaustive leaf coverage.
    pub open spec fn completeness(&self) -> bool {
        self.recorded_leaf_validity()
    }

    /// Whether no full-depth path is recorded more than once.
    pub open spec fn visited_unique(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < self.visited.len() && 0 <= j < self.visited.len() && i != j
                ==> #[trigger] self.visited@[i]@ != #[trigger] self.visited@[j]@
    }

    /// Whether the completed-path set contains `p`.
    pub open spec fn visited_contains(&self, p: Seq<u64>) -> bool {
        exists|e: int| 0 <= e < self.visited.len() && #[trigger] self.visited@[e]@ == p
    }

    /// Whether all traversal and restoration contract clauses hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.pairing()
            && self.state_restoration()
            && self.recorded_leaf_validity()
            && self.visited_unique()
    }

    /// Whether the current path has reached the configured depth.
    pub open spec fn is_leaf(&self) -> bool {
        self.path.len() == self.max_depth
    }

    /// Whether the current path has reached the configured leaf depth.
    pub fn is_leaf_exec(&self) -> (b: bool)
        ensures b == self.is_leaf(),
    {
        self.path.len() == self.max_depth
    }

    /// Whether a choice and mutation delta enable another descent.
    pub fn can_descend(&self, c: u64, d: D::Delta) -> (b: bool)
        requires self.type_invariant(),
        ensures b == (!self.is_leaf() && 1 <= c <= self.branch_factor.branches() && self.branch_factor.valid_delta(d)),
    {
        self.path.len() < self.max_depth
            && 1 <= c && c <= self.branch_factor.branch_count()
            && self.branch_factor.valid_delta_exec(d)
    }

    /// Whether an undo token is available for ascent.
    pub fn can_ascend(&self) -> (b: bool)
        ensures b == (self.path.len() >= 1),
    {
        self.path.len() >= 1
    }

    /// Whether a path occurs in the visited-leaf ledger.
    pub fn has_visited(&self, p: &Vec<u64>) -> (b: bool)
        ensures b == self.visited_contains(p@),
    {
        let len = self.visited.len();
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                len == self.visited.len(),
                forall|e: int| 0 <= e < i ==> #[trigger] self.visited@[e]@ != p@,
            decreases len - i,
        {
            if paths_equal(&self.visited[i], p) {
                assert(self.visited@[i as int]@ == p@);
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// Whether the current path is a fresh leaf that may be visited.
    pub fn can_visit(&self) -> (b: bool)
        ensures b == (self.is_leaf() && !self.visited_contains(self.path@)),
    {
        self.is_leaf_exec() && !self.has_visited(&self.path)
    }

    /// `Descend(c,d)`: record the undo token and apply its mutation atomically.
    pub fn descend(&mut self, c: u64, d: D::Delta)
        requires
            old(self).inv(),
            !old(self).is_leaf(),
            1 <= c <= old(self).branch_factor.branches(),
            old(self).branch_factor.valid_delta(d),
        ensures
            final(self).branch_factor == old(self).branch_factor,
            final(self).max_depth == old(self).max_depth,
            final(self).init_aux == old(self).init_aux,
            final(self).path@ == old(self).path@.push(c),
            final(self).ledger@.len() == old(self).ledger@.len() + 1,
            final(self).ledger@[old(self).ledger@.len() as int].saved == old(self).aux,
            final(self).ledger@[old(self).ledger@.len() as int].delta == d,
            forall|i: int| 0 <= i < old(self).ledger@.len() ==>
                #[trigger] final(self).ledger@[i].saved == old(self).ledger@[i].saved
                && final(self).ledger@[i].delta == old(self).ledger@[i].delta,
            final(self).aux == old(self).branch_factor.mutated(old(self).aux, d),
            final(self).visited@ == old(self).visited@,
            final(self).inv(),
    {
        let next = self.branch_factor.mutate(self.aux, d);
        let token = UndoToken { saved: self.aux, delta: d };
        self.ledger.push(token);
        self.path.push(c);
        self.aux = next;
        proof {
            assert(self.type_invariant()); assert(self.pairing()); assert(self.state_restoration());
            self.lemma_visited_frame(old(self));
        }
    }

    /// `Visit`: append the current leaf only when it is fresh.
    pub fn visit(&mut self)
        requires
            old(self).inv(),
            old(self).is_leaf(),
            !old(self).visited_contains(old(self).path@),
        ensures
            final(self).branch_factor == old(self).branch_factor,
            final(self).max_depth == old(self).max_depth,
            final(self).init_aux == old(self).init_aux,
            final(self).path@ == old(self).path@,
            final(self).ledger@ == old(self).ledger@,
            final(self).aux == old(self).aux,
            final(self).visited@.len() == old(self).visited@.len() + 1,
            final(self).visited@[old(self).visited@.len() as int]@ == old(self).path@,
            forall|i: int| 0 <= i < old(self).visited@.len()
                ==> #[trigger] final(self).visited@[i]@ == old(self).visited@[i]@,
            final(self).inv(),
    {
        let copy = clone_path(&self.path);
        self.commit_visit(copy);
    }

    /// Prepare fallible visit storage before committing the fresh leaf.
    ///
    /// # Errors
    /// Failed path-copy or visit-slot allocation preserves the complete logical state.
    #[allow(clippy::question_mark)] // Preserve the explicit pre-commit error branches in the proof.
    pub fn try_visit(&mut self) -> (result: Result<(),std::collections::TryReserveError>)
        requires
            old(self).inv(),
            old(self).is_leaf(),
            !old(self).visited_contains(old(self).path@),
        ensures
            final(self).branch_factor == old(self).branch_factor,
            final(self).max_depth == old(self).max_depth,
            final(self).init_aux == old(self).init_aux,
            final(self).path@ == old(self).path@,
            final(self).ledger@ == old(self).ledger@,
            final(self).aux == old(self).aux,
            result.is_err() ==> final(self).same_state(old(self)),
            result.is_ok() ==> final(self).visited@.len() == old(self).visited@.len() + 1,
            result.is_ok() ==> final(self).visited@[old(self).visited@.len() as int]@ == old(self).path@,
            forall|i: int| 0 <= i < old(self).visited@.len()
                ==> #[trigger] final(self).visited@[i]@ == old(self).visited@[i]@,
            final(self).inv(),
    {
        let mut copy: Vec<u64> = Vec::new();
        if let Err(e) = copy.try_reserve(self.path.len()) { return Err(e); }
        if let Err(e) = self.try_reserve_visits(1) { return Err(e); }
        let copy = copy_path(&self.path,copy);
        self.commit_visit(copy);
        Ok(())
    }

    /// `Visit`: append the current leaf only when it is fresh.
    fn commit_visit(&mut self, copy: Vec<u64>)
        requires
            copy@ == old(self).path@,
            old(self).inv(),
            old(self).is_leaf(),
            !old(self).visited_contains(old(self).path@),
        ensures
            final(self).branch_factor == old(self).branch_factor,
            final(self).max_depth == old(self).max_depth,
            final(self).init_aux == old(self).init_aux,
            final(self).path@ == old(self).path@,
            final(self).ledger@ == old(self).ledger@,
            final(self).aux == old(self).aux,
            final(self).visited@.len() == old(self).visited@.len() + 1,
            final(self).visited@[old(self).visited@.len() as int]@ == old(self).path@,
            forall|i: int| 0 <= i < old(self).visited@.len()
                ==> #[trigger] final(self).visited@[i]@ == old(self).visited@[i]@,
            final(self).inv(),
    {
        self.visited.push(copy);
        assert(self.recorded_leaf_validity()) by {
            assert forall|e: int| 0 <= e < self.visited.len() implies {
                &&& #[trigger] self.visited@[e].len() == self.max_depth
                &&& (forall|j: int| 0 <= j < self.max_depth as int
                    ==> 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor.branches())
            } by {
                if e < old(self).visited.len() {
                    assert(self.visited@[e] == old(self).visited@[e]);
                    assert(old(self).visited@[e].len() == old(self).max_depth);
                    assert forall|j: int| 0 <= j < self.max_depth as int
                        implies 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor.branches() by {
                        assert(self.visited@[e]@[j] == old(self).visited@[e]@[j]);
                    }
                } else {
                    assert(e == old(self).visited.len());
                    assert(self.visited@[e]@ == old(self).path@);
                    assert forall|j: int| 0 <= j < self.max_depth as int
                        implies 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor.branches() by {
                        assert(self.visited@[e]@[j] == old(self).path@[j]);
                    }
                }
            }
        }
        assert(self.visited_unique()) by {
            assert forall|i: int, j: int|
                0 <= i < self.visited.len() && 0 <= j < self.visited.len() && i != j
                    implies #[trigger] self.visited@[i]@ != #[trigger] self.visited@[j]@ by {
                if i < old(self).visited.len() && j < old(self).visited.len() {
                } else if i == old(self).visited.len() {
                    assert(self.visited@[i]@ == old(self).path@);
                    assert(self.visited@[j]@ == old(self).visited@[j]@);
                } else {
                    assert(j == old(self).visited.len());
                    assert(self.visited@[j]@ == old(self).path@);
                    assert(self.visited@[i]@ == old(self).visited@[i]@);
                }
            }
        }
    }

    /// `Ascend`: apply the recorded inverse, then pop token and path.
    pub fn ascend(&mut self)
        requires old(self).inv(), old(self).path.len() >= 1,
        ensures
            final(self).branch_factor == old(self).branch_factor,
            final(self).max_depth == old(self).max_depth,
            final(self).init_aux == old(self).init_aux,
            final(self).path@ == old(self).path@.drop_last(),
            final(self).ledger@ == old(self).ledger@.drop_last(),
            final(self).aux == old(self).branch_factor.undone(
                old(self).aux,
                old(self).ledger@[old(self).ledger@.len() - 1].delta),
            final(self).aux == old(self).ledger@[old(self).ledger@.len() - 1].saved,
            final(self).visited@ == old(self).visited@,
            final(self).inv(),
    {
        let depth = self.path.len();
        let saved = self.ledger[depth - 1].saved;
        let _ = saved;
        let delta = self.ledger[depth - 1].delta;
        assert(self.aux == self.branch_factor.mutated(saved, delta));
        proof { self.branch_factor.inverse(saved, delta); }
        let restored = self.branch_factor.undo(self.aux, delta);
        assert(restored == saved);
        self.aux = restored;
        self.ledger.pop();
        self.path.pop();
        proof {
            self.lemma_visited_frame(old(self));
            assert(self.ledger@ == old(self).ledger@.drop_last());
            assert(self.path@ == old(self).path@.drop_last());
            assert(self.type_invariant()) by {
                assert forall|i: int| 0 <= i < self.path.len()
                    implies 1 <= #[trigger] self.path@[i] <= self.branch_factor.branches() by {
                    assert(self.path@[i] == old(self).path@[i]);
                }
                assert forall|i: int| 0 <= i < self.ledger.len() implies {
                    &&& self.branch_factor.valid_aux(#[trigger] self.ledger@[i].saved)
                    &&& self.branch_factor.valid_delta(self.ledger@[i].delta)
                } by {
                    assert(self.ledger@[i].saved == old(self).ledger@[i].saved);
                    assert(self.ledger@[i].delta == old(self).ledger@[i].delta);
                }
            }
            assert(self.state_restoration()) by {
                assert forall|i: int| 1 <= i < self.ledger.len() implies
                    #[trigger] self.ledger@[i].saved
                        == self.branch_factor.mutated(self.ledger@[i - 1].saved, self.ledger@[i - 1].delta) by {
                    assert(self.ledger@[i].saved == old(self).ledger@[i].saved);
                    assert(self.ledger@[i - 1].saved == old(self).ledger@[i - 1].saved);
                    assert(self.ledger@[i - 1].delta == old(self).ledger@[i - 1].delta);
                }
            }
            assert(self.pairing()) by {
                if self.path.len() == 0 {
                    assert(depth == 1);
                    assert(old(self).ledger@[0].saved == self.init_aux);
                } else {
                    assert(depth >= 2);
                    assert(old(self).ledger@[depth - 1].saved
                        == self.branch_factor.mutated(
                            old(self).ledger@[depth - 2].saved,
                            old(self).ledger@[depth - 2].delta));
                }
            }
        }
    }
}

fn paths_equal(a: &Vec<u64>, b: &Vec<u64>) -> (same: bool)
    ensures same == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let len = a.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            len == a.len(),
            len == b.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] a@[k] == b@[k],
        decreases len - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

fn clone_path(p: &Vec<u64>) -> (out: Vec<u64>)
    ensures out@ == p@,
{ copy_path(p, Vec::new()) }

fn copy_path(p: &Vec<u64>, mut out: Vec<u64>) -> (copied: Vec<u64>)
    requires out.len() == 0,
    ensures copied@ == p@,
{
    let n = p.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == p.len(),
            out.len() == i,
            forall|k: int| 0 <= k < i ==> out@[k] == p@[k],
        decreases n - i,
    {
        out.push(p[i]);
        i = i + 1;
    }
    assert(out@ =~= p@);
    out
}


    /// Apply the modulo-three mutation used by the traversal profile.
spec fn modulo_mutate_spec(v: u64, d: u64) -> int {
        ((v as int) + (d as int)) % 3
    }

    /// Apply the inverse modulo-three mutation used during restoration.
spec fn modulo_undo_spec(v: u64, d: u64) -> int {
        ((v as int) + (3 - d as int)) % 3
    }

    /// Apply the modulo-three auxiliary mutation.
fn modulo_mutate_exec(v: u64, d: u64) -> (out: u64)
        requires v < 3, 1 <= d <= 2,
        ensures out < 3, out as int == modulo_mutate_spec(v, d),
    {
        if d == 1 {
            if v == 2 { 0 } else { v + 1 }
        } else {
            if v == 0 { 2 } else { v - 1 }
        }
    }

    /// Apply the inverse modulo-three auxiliary mutation.
fn modulo_undo_exec(v: u64, d: u64) -> (out: u64)
        requires v < 3, 1 <= d <= 2,
        ensures out < 3, out as int == modulo_undo_spec(v, d),
    {
        if d == 1 {
            if v == 0 { 2 } else { v - 1 }
        } else {
            if v == 2 { 0 } else { v + 1 }
        }
    }

    /// Prove that the undo operation reverses an admitted mutation.
proof fn modulo_lemma_undo_inverts(v: u64, d: u64)
        requires v < 3, 1 <= d <= 2,
        ensures modulo_undo_spec(modulo_mutate_spec(v, d) as u64, d) == v as int,
    {
        if v == 0 {
            if d == 1 { assert(modulo_mutate_spec(v, d) == 1); }
            else { assert(modulo_mutate_spec(v, d) == 2); }
        } else if v == 1 {
            if d == 1 { assert(modulo_mutate_spec(v, d) == 2); }
            else { assert(modulo_mutate_spec(v, d) == 0); }
        } else {
            assert(v == 2);
            if d == 1 { assert(modulo_mutate_spec(v, d) == 0); }
            else { assert(modulo_mutate_spec(v, d) == 1); }
        }
    }


impl BacktrackingTraversal {
    /// Apply the default modulo-three mutation in specification form.
    pub open spec fn mutate_spec(v: u64,d: u64) -> int { (v as int + d as int) % 3 }
    /// Apply the default modulo-three inverse in specification form.
    pub open spec fn undo_spec(v: u64,d: u64) -> int { (v as int + (3 - d as int)) % 3 }
    /// Compute the default modulo-three mutation.
    pub fn mutate_exec(v: u64,d: u64) -> (out: u64)
        requires v < 3, 1 <= d <= 2,
        ensures out < 3, out as int == Self::mutate_spec(v,d),
    { modulo_mutate_exec(v,d) }
    /// Compute the default modulo-three inverse.
    pub fn undo_exec(v: u64,d: u64) -> (out: u64)
        requires v < 3, 1 <= d <= 2,
        ensures out < 3, out as int == Self::undo_spec(v,d),
    { modulo_undo_exec(v,d) }
    /// Prove the default mutation/inverse law.
    pub proof fn lemma_undo_inverts(v: u64,d: u64)
        requires v < 3, 1 <= d <= 2,
        ensures Self::undo_spec(Self::mutate_spec(v,d) as u64,d) == v as int,
    { modulo_lemma_undo_inverts(v,d); }

    /// Construct a traversal at its root with an empty visited set.
    pub fn new(branch_factor: u64, max_depth: usize, init_aux: u64) -> (t: BacktrackingTraversal)
        requires init_aux < 3,
        ensures
            t.branch_factor == branch_factor,
            t.max_depth == max_depth,
            t.init_aux == init_aux,
            t.path@.len() == 0,
            t.ledger@.len() == 0,
            t.aux == init_aux,
            t.visited@.len() == 0,
            t.inv(),
    { Self::initialize(branch_factor,max_depth,init_aux,Vec::new(),Vec::new()) }
}

}
