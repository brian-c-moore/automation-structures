// Standalone test harness: unsafe is confined to forwarding System's allocator contract.
// No allocator hook, unsafe block or fault switch is part of the library implementation.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize,AtomicBool,Ordering};
use automation_structures::{primitives::{competitive_selection::CompetitiveSelectionHard,
    actuation_pass::ActuationPass, audit_sink::AuditSink,
    convergence_governor_phase_aware::ConvergenceGovernorPhaseAware,
    propagation_pass::PropagationPass,backtracking_traversal::BacktrackingTraversal},
    modalities::{fork_join::ForkJoin,sequential::Sequential,step_graph::StepGraph},
    compositions::federated_budget::FederatedBudget};

struct FailingAllocator;
static FAIL_AFTER: AtomicIsize=AtomicIsize::new(-1);
static TRIPPED: AtomicBool=AtomicBool::new(false);
fn should_fail() -> bool {
    let count=FAIL_AFTER.load(Ordering::SeqCst);
    if count < 0 { return false; }
    if count == 0 {
        FAIL_AFTER.store(-1,Ordering::SeqCst); TRIPPED.store(true,Ordering::SeqCst); true
    } else { FAIL_AFTER.store(count-1,Ordering::SeqCst); false }
}
// SAFETY: successful allocations/deallocations forward the original pointer and Layout
// to System. Injected failures return null, as required by GlobalAlloc. This binary is
// single-threaded while injection is armed; no library implementation relies on this code.
unsafe impl GlobalAlloc for FailingAllocator {
    unsafe fn alloc(&self,layout:Layout)->*mut u8 {
        if should_fail(){std::ptr::null_mut()}else{unsafe{System.alloc(layout)}}
    }
    unsafe fn alloc_zeroed(&self,layout:Layout)->*mut u8 {
        if should_fail(){std::ptr::null_mut()}else{unsafe{System.alloc_zeroed(layout)}}
    }
    unsafe fn realloc(&self,pointer:*mut u8,layout:Layout,size:usize)->*mut u8 {
        if should_fail(){std::ptr::null_mut()}else{unsafe{System.realloc(pointer,layout,size)}}
    }
    unsafe fn dealloc(&self,pointer:*mut u8,layout:Layout) { unsafe{System.dealloc(pointer,layout)} }
}
#[global_allocator]
static ALLOCATOR: FailingAllocator=FailingAllocator;

fn fail_at<R>(index:isize,operation:impl FnOnce()->R)->R {
    TRIPPED.store(false,Ordering::SeqCst); FAIL_AFTER.store(index,Ordering::SeqCst);
    let result=operation(); FAIL_AFTER.store(-1,Ordering::SeqCst);
    assert!(TRIPPED.load(Ordering::SeqCst),"the selected allocation was not reached"); result
}
fn no_allocations(operation:impl FnOnce()) {
    TRIPPED.store(false,Ordering::SeqCst); FAIL_AFTER.store(0,Ordering::SeqCst);
    operation(); FAIL_AFTER.store(-1,Ordering::SeqCst);
    assert!(!TRIPPED.load(Ordering::SeqCst),"admitted action attempted an allocation");
}

fn main() {
    assert!(fail_at(0,||CompetitiveSelectionHard::try_new(4)).is_err());
    let edges=vec![(0,1)]; let address=edges.as_ptr();
    let Err((_,edges))=fail_at(0,||StepGraph::try_new(2,edges)) else{panic!("missing refusal")};
    assert_eq!(edges.as_ptr(),address); assert_eq!(edges,vec![(0,1)]);
    let assignments=vec![Some(2),None]; let address=assignments.as_ptr();
    let Err((_,assignments))=fail_at(0,||ActuationPass::try_new(assignments,2)) else{panic!("missing refusal")};
    assert_eq!(assignments.as_ptr(),address); assert_eq!(assignments,vec![Some(2),None]);
    assert!(fail_at(0,||Sequential::try_new(3,10,0)).is_err());
    for allocation in 0..3 { assert!(fail_at(allocation,||ForkJoin::try_new(3,10,0)).is_err()); }
    assert!(fail_at(0,||FederatedBudget::try_new(10,3)).is_err());
    assert!(fail_at(0,||ConvergenceGovernorPhaseAware::try_new(3,6,3,9)).is_err());
    let mut audit=AuditSink::new(4); assert!(audit.record(7));
    let before=(audit.log.len(),audit.last_hash,audit.max_log_len);
    assert!(fail_at(0,||audit.try_reserve_records(audit.log.capacity()+1)).is_err());
    assert_eq!((audit.log.len(),audit.last_hash,audit.max_log_len),before);
    assert_eq!(audit.log[0].operation,7); assert!(audit.validate());
    for allocation in 0..2 {
        let edges=vec![(0,1)]; let values=vec![0,2]; let addresses=(edges.as_ptr(),values.as_ptr());
        let Err((_,ceiling,edges,values))=fail_at(allocation,||PropagationPass::try_new(2,4,10,edges,values)) else{panic!("missing refusal")};
        assert_eq!(ceiling,10); assert_eq!((edges.as_ptr(),values.as_ptr()),addresses);
        assert_eq!(values,vec![0,2]);
        assert!(fail_at(allocation,||BacktrackingTraversal::try_new(2,3,0)).is_err());
    }
    for allocation in 0..2 {
        let mut traversal=BacktrackingTraversal::try_new(2,1,0).unwrap(); traversal.descend(1,1);
        let before=(traversal.path.as_ptr(),traversal.ledger.as_ptr(),traversal.aux);
        assert!(fail_at(allocation,||traversal.try_visit()).is_err());
        assert_eq!((traversal.path.as_ptr(),traversal.ledger.as_ptr(),traversal.aux),before);
        assert_eq!(traversal.path,vec![1]); assert_eq!(traversal.ledger.len(),1);
        assert_eq!((traversal.ledger[0].saved,traversal.ledger[0].delta),(0,1));
        assert!(traversal.visited.is_empty()); traversal.ascend(); assert_eq!(traversal.aux,0);
    }
    let mut sequence=Sequential::try_new(3,10,0).unwrap();
    let mut fork=ForkJoin::try_new(3,10,0).unwrap();
    let mut propagation=PropagationPass::try_new(2,4,10,vec![(0,1)],vec![0,2]).unwrap();
    let mut traversal=BacktrackingTraversal::try_new(2,3,0).unwrap();
    no_allocations(|| {
        for i in 0..3 { assert!(sequence.begin_step()); assert!(sequence.complete_step(i+1)); }
        for i in 0..3 { assert!(fork.start_worker(i)); assert!(fork.complete_worker(i,7)); }
        assert!(fork.barrier()); assert!(fork.produce_output());
        for _ in 0..3 { propagation.start_round(); propagation.update_node(0); propagation.update_node(1); propagation.end_round(); }
        for _ in 0..3 { traversal.descend(1,1); }
        for _ in 0..3 { traversal.ascend(); }
    });
    println!("allocation-refusal KAT: valid-input failures preserve owners; admitted actions allocate no arrays");
}
