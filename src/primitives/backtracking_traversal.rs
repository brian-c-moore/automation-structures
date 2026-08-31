// Executable modulo-3 carrier for BacktrackingTraversalUndo.tla, bound by
// BacktrackingTraversalUndo.cfg. A descent records the pre-mutation value and
// chosen delta in an undo token, then applies Mutate in the same commit. An
// ascent applies the recorded inverse and pops both path and ledger. The model
// remains order-parametric: Completeness is leaf soundness, not eventual
// coverage of every leaf.

use vstd::prelude::*;

verus! {

/// Reversible auxiliary-state mutation retained for one descent.
pub struct UndoToken {
    /// Auxiliary value before the descent.
    pub saved: u64,
    /// Mutation delta applied by the descent.
    pub delta: u64,
}

/// Reversible depth-first traversal owner.
pub struct BacktrackingTraversal {
    /// Number of admitted choices at each non-leaf depth.
    pub branch_factor: u64,
    /// Required depth of a complete leaf path.
    pub max_depth: usize,
    /// Auxiliary value at the root.
    pub init_aux: u64,
    /// Current branch-choice path.
    pub path: Vec<u64>,
    /// Current auxiliary value.
    pub aux: u64,
    /// Undo tokens aligned with the current path.
    pub ledger: Vec<UndoToken>,
    /// A Vec is the executable representation of the TLA+ visited set;
    /// `visited_unique` and Visit's freshness guard preserve set semantics.
    pub visited: Vec<Vec<u64>>,
}

impl BacktrackingTraversal {
    /// Apply the modulo-three mutation used by the traversal profile.
    pub open spec fn mutate_spec(v: u64, d: u64) -> int {
        ((v as int) + (d as int)) % 3
    }

    /// Apply the inverse modulo-three mutation used during restoration.
    pub open spec fn undo_spec(v: u64, d: u64) -> int {
        ((v as int) + (3 - d as int)) % 3
    }

    /// Whether path, ledger, auxiliary value, and choices have valid shape and bounds.
    pub open spec fn type_invariant(&self) -> bool {
        &&& self.init_aux < 3
        &&& self.aux < 3
        &&& self.path.len() <= self.max_depth
        &&& (forall|i: int| 0 <= i < self.path.len()
                ==> 1 <= #[trigger] self.path@[i] <= self.branch_factor)
        &&& (forall|i: int| 0 <= i < self.ledger.len() ==> {
                &&& #[trigger] self.ledger@[i].saved < 3
                &&& 1 <= self.ledger@[i].delta <= 2
            })
    }

    /// Pairing: one token per outstanding descent and the live value is
    /// exactly the mutation named by the head token.
    pub open spec fn pairing(&self) -> bool {
        &&& self.ledger.len() == self.path.len()
        &&& (self.path.len() == 0 ==> self.aux == self.init_aux)
        &&& (self.path.len() > 0 ==> self.aux as int
            == Self::mutate_spec(
                self.ledger@[self.path.len() - 1].saved,
                self.ledger@[self.path.len() - 1].delta))
    }

    /// StateRestoration: the ledger is a checkpoint chain, not a depth-derived
    /// counter sequence.
    pub open spec fn state_restoration(&self) -> bool {
        &&& (self.ledger.len() >= 1 ==> self.ledger@[0].saved == self.init_aux)
        &&& (forall|i: int| 1 <= i < self.ledger.len() ==>
            #[trigger] self.ledger@[i].saved as int
                == Self::mutate_spec(self.ledger@[i - 1].saved, self.ledger@[i - 1].delta))
    }

    /// Completeness: every recorded visit is a valid full-depth leaf.
    pub open spec fn completeness(&self) -> bool {
        forall|e: int| 0 <= e < self.visited.len() ==> {
            &&& #[trigger] self.visited@[e].len() == self.max_depth
            &&& (forall|j: int| 0 <= j < self.max_depth as int
                ==> 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor)
        }
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

    /// Whether all traversal and restoration obligations hold.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant()
            && self.pairing()
            && self.state_restoration()
            && self.completeness()
            && self.visited_unique()
    }

    /// Whether the current path has reached the configured depth.
    pub open spec fn is_leaf(&self) -> bool {
        self.path.len() == self.max_depth
    }

    /// Apply the modulo-three auxiliary mutation.
    pub fn mutate_exec(v: u64, d: u64) -> (out: u64)
        requires v < 3, 1 <= d <= 2,
        ensures out < 3, out as int == Self::mutate_spec(v, d),
    {
        if d == 1 {
            if v == 2 { 0 } else { v + 1 }
        } else {
            if v == 0 { 2 } else { v - 1 }
        }
    }

    /// Apply the inverse modulo-three auxiliary mutation.
    pub fn undo_exec(v: u64, d: u64) -> (out: u64)
        requires v < 3, 1 <= d <= 2,
        ensures out < 3, out as int == Self::undo_spec(v, d),
    {
        if d == 1 {
            if v == 0 { 2 } else { v - 1 }
        } else {
            if v == 2 { 0 } else { v + 1 }
        }
    }

    /// Prove that the undo operation reverses an admitted mutation.
    pub proof fn lemma_undo_inverts(v: u64, d: u64)
        requires v < 3, 1 <= d <= 2,
        ensures Self::undo_spec(Self::mutate_spec(v, d) as u64, d) == v as int,
    {
        if v == 0 {
            if d == 1 { assert(Self::mutate_spec(v, d) == 1); }
            else { assert(Self::mutate_spec(v, d) == 2); }
        } else if v == 1 {
            if d == 1 { assert(Self::mutate_spec(v, d) == 2); }
            else { assert(Self::mutate_spec(v, d) == 0); }
        } else {
            assert(v == 2);
            if d == 1 { assert(Self::mutate_spec(v, d) == 0); }
            else { assert(Self::mutate_spec(v, d) == 1); }
        }
    }

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
    {
        BacktrackingTraversal {
            branch_factor,
            max_depth,
            init_aux,
            path: Vec::new(),
            aux: init_aux,
            ledger: Vec::new(),
            visited: Vec::new(),
        }
    }

    /// Whether the current path has reached the configured leaf depth.
    pub fn is_leaf_exec(&self) -> (b: bool)
        ensures b == self.is_leaf(),
    {
        self.path.len() == self.max_depth
    }

    /// Whether a choice and mutation delta enable another descent.
    pub fn can_descend(&self, c: u64, d: u64) -> (b: bool)
        requires self.type_invariant(),
        ensures b == (!self.is_leaf() && 1 <= c <= self.branch_factor && 1 <= d <= 2),
    {
        self.path.len() < self.max_depth
            && 1 <= c && c <= self.branch_factor
            && 1 <= d && d <= 2
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
    pub fn descend(&mut self, c: u64, d: u64)
        requires
            old(self).inv(),
            !old(self).is_leaf(),
            1 <= c <= old(self).branch_factor,
            1 <= d <= 2,
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
            final(self).aux as int == Self::mutate_spec(old(self).aux, d),
            final(self).visited@ == old(self).visited@,
            final(self).inv(),
    {
        let next = Self::mutate_exec(self.aux, d);
        let token = UndoToken { saved: self.aux, delta: d };
        self.ledger.push(token);
        self.path.push(c);
        self.aux = next;
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
        self.visited.push(copy);
        assert(self.completeness()) by {
            assert forall|e: int| 0 <= e < self.visited.len() implies {
                &&& #[trigger] self.visited@[e].len() == self.max_depth
                &&& (forall|j: int| 0 <= j < self.max_depth as int
                    ==> 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor)
            } by {
                if e < old(self).visited.len() {
                } else {
                    assert(e == old(self).visited.len());
                    assert(self.visited@[e]@ == old(self).path@);
                    assert forall|j: int| 0 <= j < self.max_depth as int
                        implies 1 <= #[trigger] self.visited@[e]@[j] <= self.branch_factor by {
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
            final(self).aux as int == Self::undo_spec(
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
        assert(self.aux as int == Self::mutate_spec(saved, delta));
        proof { Self::lemma_undo_inverts(saved, delta); }
        let restored = Self::undo_exec(self.aux, delta);
        assert(restored == saved);
        self.aux = restored;
        self.ledger.pop();
        self.path.pop();
        proof {
            assert(self.ledger@ == old(self).ledger@.drop_last());
            assert(self.path@ == old(self).path@.drop_last());
            assert(self.type_invariant()) by {
                assert forall|i: int| 0 <= i < self.path.len()
                    implies 1 <= #[trigger] self.path@[i] <= self.branch_factor by {
                    assert(self.path@[i] == old(self).path@[i]);
                }
                assert forall|i: int| 0 <= i < self.ledger.len() implies {
                    &&& #[trigger] self.ledger@[i].saved < 3
                    &&& 1 <= self.ledger@[i].delta <= 2
                } by {
                    assert(self.ledger@[i].saved == old(self).ledger@[i].saved);
                    assert(self.ledger@[i].delta == old(self).ledger@[i].delta);
                }
            }
            assert(self.state_restoration()) by {
                assert forall|i: int| 1 <= i < self.ledger.len() implies
                    #[trigger] self.ledger@[i].saved as int
                        == Self::mutate_spec(self.ledger@[i - 1].saved, self.ledger@[i - 1].delta) by {
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
                    assert(old(self).ledger@[depth - 1].saved as int
                        == Self::mutate_spec(
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
{
    let mut out: Vec<u64> = Vec::new();
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

}
