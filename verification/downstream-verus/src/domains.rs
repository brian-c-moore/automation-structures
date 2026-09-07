use automation_structures::primitives::backtracking_traversal::{
    BacktrackingTraversal, TraversalDomain,
};
use automation_structures::primitives::propagation_pass::{PropagationDomain, PropagationPass};
use automation_structures::value_eq::ValueEq;
use vstd::prelude::*;
verus! {
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Bit { pub set: bool }
impl ValueEq for Bit {
    fn value_eq(&self, other: &Self) -> (equal: bool) { self.set == other.set }
}
#[derive(Clone,Copy,Debug)]
pub struct NeighborComplement { pub allowed: usize }
impl PropagationDomain<Bit> for NeighborComplement {
    open spec fn contains(&self, _value: Bit) -> bool { true }
    open spec fn accepts(&self, _edges: Seq<(usize,usize)>, snapshot: Seq<Bit>, node: usize) -> bool {
        snapshot.len() == 2 && node < self.allowed
    }
    open spec fn combined(&self, _edges: Seq<(usize,usize)>, snapshot: Seq<Bit>, node: usize) -> Bit {
        Bit { set: !snapshot[if node == 0 { 1int } else { 0int }].set }
    }
    fn accepts_exec(&self, _edges: &Vec<(usize,usize)>, snapshot: &Vec<Bit>, node: usize) -> (yes: bool) {
        snapshot.len() == 2 && node < self.allowed
    }
    fn combine(&self, _edges: &Vec<(usize,usize)>, snapshot: &Vec<Bit>, node: usize) -> (value: Bit) {
        Bit { set: !snapshot[if node == 0 { 1 } else { 0 }].set }
    }
}
#[derive(Clone,Copy,Debug)]
pub struct Toggle { pub choices: u64 }
impl TraversalDomain<Bit> for Toggle {
    type Delta = bool;
    open spec fn branches(&self) -> u64 { self.choices }
    open spec fn valid_aux(&self, _value: Bit) -> bool { true }
    open spec fn valid_delta(&self, delta: bool) -> bool { delta }
    open spec fn mutated(&self, value: Bit, _delta: bool) -> Bit { Bit { set: !value.set } }
    open spec fn undone(&self, value: Bit, _delta: bool) -> Bit { Bit { set: !value.set } }
    fn branch_count(&self) -> (count: u64) { self.choices }
    fn valid_delta_exec(&self, delta: bool) -> (yes: bool) { delta }
    fn mutate(&self, value: Bit, _delta: bool) -> (result: Bit) { Bit { set: !value.set } }
    fn undo(&self, value: Bit, _delta: bool) -> (result: Bit) { Bit { set: !value.set } }
    proof fn inverse(&self, value: Bit, delta: bool) {}
}

pub fn generic_snapshot_is_shared() {
    let mut values=Vec::new(); values.push(Bit{set:false}); values.push(Bit{set:false});
    if let Ok(mut p)=PropagationPass::try_new(2,3,NeighborComplement{allowed:2},Vec::new(),values) {
        p.start_round();
        let _first=p.try_update_node(0); assert(_first);
        let _second=p.try_update_node(1); assert(_second);
        assert(p.values@ == seq![Bit{set:true},Bit{set:true}]);
        let ghost before=p;
        let _repeated=p.try_update_node(0); assert(!_repeated); assert(p == before);
        assert(p.all_updated()); p.end_round(); assert(p.iteration == 1 && p.changed);
    }
}
pub fn generic_domain_refusal_stutters() {
    let mut values=Vec::new(); values.push(Bit{set:false}); values.push(Bit{set:false});
    if let Ok(mut p)=PropagationPass::try_new(2,3,NeighborComplement{allowed:1},Vec::new(),values) {
        p.start_round(); let ghost before=p;
        let _accepted=p.try_update_node(1); assert(!_accepted); assert(p == before);
    }
}
pub fn generic_inverse_restores_original(additional: usize) {
    if let Ok(mut t)=BacktrackingTraversal::try_new(Toggle{choices:2},1,Bit{set:false}) {
        t.descend(2,true); assert(t.aux == Bit{set:true});
        assert(t.is_leaf()); assert(!t.visited_contains(t.path@));
        let ghost before=t;
        let _reserved=t.try_reserve_visits(additional); assert(t.same_state(&before));
        let visit=t.try_visit();
        if visit.is_ok() { assert(t.visited.len() == 1); assert(t.visited@[0]@ == seq![2u64]); }
        else { assert(t.same_state(&before)); }
        t.ascend(); assert(t.aux == Bit{set:false} && t.path.len() == 0 && t.ledger.len() == 0);
    }
}
}
