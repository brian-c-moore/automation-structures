use automation_structures::primitives::actuation_pass::ActuationPass;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

/// Focused known-answer vector for the ActuationPass executable
/// carrier. It covers each non-stuttering action and representative rejected
/// admissions; it is an executable cross-check, not a proof.
pub fn run() -> bool {
    let mut all_ok = true;
    let alloc: Vec<Option<u64>> = vec![Some(10u64), None, Some(30u64), Some(40u64)];
    let mut ap = ActuationPass::new(alloc, 4);
    all_ok &= check(
        "ActuationPass Init: seat 0 has no effect",
        ap.effects[0],
        None,
    );
    all_ok &= check(
        "ActuationPass rejection: NULL seat cannot actuate",
        ap.can_actuate(1),
        false,
    );
    all_ok &= check(
        "ActuationPass pre-closure: pass is incomplete",
        ap.complete,
        false,
    );

    ap.allocate(1, 20);
    all_ok &= check(
        "ActuationPass Allocate: seat 1 gets resource 20",
        ap.allocation[1],
        Some(20),
    );
    ap.deallocate(1);
    all_ok &= check(
        "ActuationPass Deallocate: unapplied seat 1 returns to NULL",
        ap.allocation[1],
        None,
    );

    ap.actuate(0);
    all_ok &= check(
        "ActuationPass Actuate: effect records resource 10",
        ap.effects[0],
        Some(10),
    );
    all_ok &= check(
        "ActuationPass ownership: applied seat cannot deallocate",
        ap.can_deallocate(0),
        false,
    );
    all_ok &= check(
        "ActuationPass completeness guard rejects unfinished pass",
        ap.ready_to_finish_exec(),
        false,
    );

    ap.actuate(2);
    ap.actuate(3);
    all_ok &= check(
        "ActuationPass frame: NULL seat 1 remains unapplied",
        ap.effects[1],
        None,
    );
    all_ok &= check(
        "ActuationPass completeness guard accepts finished work",
        ap.ready_to_finish_exec(),
        true,
    );
    ap.finish();
    all_ok &= check("ActuationPass Finish: closure committed", ap.complete, true);
    all_ok &= check(
        "ActuationPass post-closure: allocation rejected",
        ap.can_allocate(1),
        false,
    );
    all_ok
}
