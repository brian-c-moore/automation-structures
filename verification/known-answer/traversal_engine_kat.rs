extern crate automation_structures;

use automation_structures::compositions::traversal_engine::TraversalEngine;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn main() {
    let mut all_ok = true;

    let mut walk = TraversalEngine::new(4, 0, 6);
    all_ok &= check("Init queues exactly root", walk.queue.clone(), vec![0]);
    all_ok &= check(
        "Visit admission accepts queued root",
        walk.can_visit(0),
        true,
    );
    all_ok &= check(
        "Visit admission rejects nonqueued node",
        walk.can_visit(1),
        false,
    );
    all_ok &= check(
        "Visit admission rejects invalid node",
        walk.can_visit(4),
        false,
    );
    all_ok &= check(
        "Terminate disabled while queue nonempty",
        walk.can_terminate(),
        false,
    );

    walk.visit_node(0);
    all_ok &= check("root removed from queue", walk.queue_contains(0), false);
    all_ok &= check(
        "root visit enqueues exact star",
        walk.queue.clone(),
        vec![1, 2, 3],
    );
    all_ok &= check("root visited", walk.visited_contains(0), true);
    all_ok &= check("root accepted", walk.accepted_contains(0), true);
    all_ok &= check("root cost charged", walk.budget_remaining, 4);
    all_ok &= check("duplicate visit disabled", walk.can_visit(0), false);

    walk.visit_node(1);
    all_ok &= check("child removed from queue", walk.queue_contains(1), false);
    all_ok &= check("leaf adds no children", walk.queue.clone(), vec![2, 3]);
    all_ok &= check("child accepted", walk.accepted_contains(1), true);
    all_ok &= check("second cost charged", walk.budget_remaining, 2);

    let mut exhausted = TraversalEngine::new(2, 0, 2);
    exhausted.visit_node(0);
    exhausted.visit_node(1);
    all_ok &= check(
        "unaffordable node still visited",
        exhausted.visited_contains(1),
        true,
    );
    all_ok &= check(
        "unaffordable node not accepted",
        exhausted.accepted_contains(1),
        false,
    );
    all_ok &= check(
        "unaffordable visit frames zero budget",
        exhausted.budget_remaining,
        0,
    );
    all_ok &= check(
        "unaffordable visit removes queue member",
        exhausted.queue.len(),
        0,
    );
    all_ok &= check(
        "Terminate enabled exactly at empty queue",
        exhausted.can_terminate(),
        true,
    );
    let before = (
        exhausted.budget_remaining,
        exhausted.visited.clone(),
        exhausted.accepted.clone(),
        exhausted.queue.clone(),
    );
    exhausted.terminate();
    all_ok &= check(
        "Terminate is exact stutter",
        (
            exhausted.budget_remaining,
            exhausted.visited.clone(),
            exhausted.accepted.clone(),
            exhausted.queue.clone(),
        ),
        before,
    );

    let mut skipped = TraversalEngine::new(3, 0, 4);
    skipped.visit_node(0);
    let skip_frames = (
        skipped.budget_remaining,
        skipped.visited.clone(),
        skipped.accepted.clone(),
    );
    all_ok &= check(
        "Skip admission accepts queued child",
        skipped.can_skip(1),
        true,
    );
    skipped.skip(1);
    all_ok &= check(
        "Skip removes exactly selected child",
        skipped.queue.clone(),
        vec![2],
    );
    all_ok &= check(
        "Skip frames budget visited accepted",
        (
            skipped.budget_remaining,
            skipped.visited.clone(),
            skipped.accepted.clone(),
        ),
        skip_frames,
    );
    all_ok &= check(
        "Skip admission rejects removed child",
        skipped.can_skip(1),
        false,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (TraversalEngine action correspondence)");
    } else {
        println!("KAT_RESULT: FAIL (TraversalEngine action correspondence)");
        std::process::exit(1);
    }
}
