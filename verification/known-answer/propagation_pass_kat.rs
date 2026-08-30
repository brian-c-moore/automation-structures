extern crate automation_structures;

use automation_structures::primitives::propagation_pass::{PropagationPass, Round};

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn run_round(pass: &mut PropagationPass, order: &[usize]) {
    pass.start_round();
    for node in order {
        pass.update_node(*node);
    }
    pass.end_round();
}

fn main() {
    let mut ok = true;

    // Path 0 -> 1 -> 2. Updating 1 before 2 distinguishes a shared snapshot
    // round from a same-round (Gauss-Seidel) read.
    let mut pass = PropagationPass::new(
        3,
        5,
        3,
        vec![(0usize, 1usize), (1usize, 2usize)],
        vec![0u64, 2, 3],
    );
    ok &= check("init round", pass.round, Round::Idle);
    ok &= check("init snapshot", pass.snapshot.clone(), vec![0u64, 2, 3]);
    ok &= check(
        "init updated",
        pass.updated.clone(),
        vec![false, false, false],
    );

    pass.start_round();
    ok &= check("start round", pass.round, Round::Running);
    ok &= check("start snapshot", pass.snapshot.clone(), vec![0u64, 2, 3]);
    pass.update_node(1);
    ok &= check("local update node 1", pass.values[1], 1);
    pass.update_node(2);
    ok &= check("snapshot isolation node 2", pass.values[2], 2);
    ok &= check("partial coverage", pass.all_nodes_updated(), false);
    pass.update_node(0);
    ok &= check("complete coverage", pass.all_nodes_updated(), true);
    pass.end_round();
    ok &= check("round 1 values", pass.values.clone(), vec![0u64, 1, 2]);
    ok &= check("round 1 iteration", pass.iteration, 1);
    ok &= check("round 1 changed", pass.changed, true);

    run_round(&mut pass, &[2, 0, 1]);
    ok &= check("round 2 values", pass.values.clone(), vec![0u64, 0, 1]);
    run_round(&mut pass, &[0, 1, 2]);
    ok &= check("round 3 values", pass.values.clone(), vec![0u64, 0, 0]);
    run_round(&mut pass, &[1, 2, 0]);
    ok &= check("fixed values", pass.values.clone(), vec![0u64, 0, 0]);
    ok &= check("fixed point changed false", pass.changed, false);
    ok &= check("fixed point iteration", pass.iteration, 4);
    pass.terminate();
    ok &= check("terminate is a self-loop", pass.iteration, 4);

    // A changing round may consume the final budget slot and then terminate at
    // the ceiling without claiming a fixed point.
    let mut bounded = PropagationPass::new(2, 1, 2, vec![(0usize, 1usize)], vec![0u64, 2]);
    run_round(&mut bounded, &[0, 1]);
    ok &= check("ceiling iteration", bounded.iteration, 1);
    ok &= check("ceiling changed", bounded.changed, true);
    bounded.terminate();

    // An edgeless graph settles after exactly one complete round.
    let mut edgeless = PropagationPass::new(2, 2, 3, vec![], vec![2u64, 3]);
    run_round(&mut edgeless, &[1, 0]);
    ok &= check("edgeless unchanged", edgeless.values.clone(), vec![2u64, 3]);
    ok &= check("edgeless settled", edgeless.changed, false);

    if ok {
        println!("KAT_RESULT: SUCCESS (PropagationPass)");
    } else {
        println!("KAT_RESULT: FAIL (PropagationPass)");
        std::process::exit(1);
    }
}
