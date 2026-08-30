// Executable cross-check for the six-action Budget carrier.

extern crate automation_structures;

use automation_structures::primitives::budget::Budget;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        true
    } else {
        eprintln!("FAIL {name}: got {got:?}, want {want:?}");
        false
    }
}

fn main() {
    let mut ok = true;
    let mut budget = Budget::new(100);

    ok &= check("initial available", budget.available(), 100);
    ok &= check("allocate within ceiling", budget.try_allocate(30), true);
    ok &= check("reserve within ceiling", budget.reserve(40), true);
    ok &= check("reject overspend", budget.try_allocate(40), false);
    ok &= check("allocate exact remainder", budget.try_allocate(30), true);
    ok &= check("reject above exact ceiling", budget.try_allocate(1), false);

    budget.commit_reservation(40);
    ok &= check("reservation committed", budget.allocated, 100);
    ok &= check("reservation cleared", budget.reserved, 0);

    budget.release(50);
    budget.mark_eviction(30);
    budget.complete_eviction(10);
    ok &= check("final allocated", budget.allocated, 20);
    ok &= check("final pending eviction", budget.pending_eviction, 20);
    ok &= check("final available", budget.available(), 60);

    if ok {
        println!("KAT_RESULT: SUCCESS (Budget)");
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
