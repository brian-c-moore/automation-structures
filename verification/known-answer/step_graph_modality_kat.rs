extern crate automation_structures;

use automation_structures::modalities::step_graph::StepGraph;

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
    let mut ok = true;
    let mut d = StepGraph::new(4, vec![(0, 1), (0, 2), (1, 3), (2, 3)]);
    ok &= check("diamond initial states", d.nstate.clone(), vec![1, 0, 0, 0]);
    ok &= check("predecessor blocks child ready", d.become_ready(1), false);
    ok &= check("root starts", d.start_running(0), true);
    ok &= check("root completes", d.complete_node(0), true);
    ok &= check("first fan-out child ready", d.become_ready(1), true);
    ok &= check("second fan-out child ready", d.become_ready(2), true);
    ok &= check(
        "join blocked before both predecessors",
        d.become_ready(3),
        false,
    );
    ok &= check("child 1 runs", d.start_running(1), true);
    ok &= check("child 1 completes", d.complete_node(1), true);
    ok &= check("join still blocked by child 2", d.become_ready(3), false);
    ok &= check("child 2 runs", d.start_running(2), true);
    ok &= check("child 2 completes", d.complete_node(2), true);
    ok &= check("diamond join becomes ready", d.become_ready(3), true);
    ok &= check("join runs", d.start_running(3), true);
    ok &= check("join completes", d.complete_node(3), true);
    ok &= check("terminal stutter enabled", d.done_stuttering(), true);
    ok &= check("backward start rejected", d.start_running(0), false);
    ok &= check("node bound rejected", d.become_ready(4), false);

    let mut linear = StepGraph::new(3, vec![(0, 1), (1, 2)]);
    linear.start_running(0);
    linear.complete_node(0);
    linear.become_ready(1);
    ok &= check(
        "linear releases exactly next node",
        linear.nstate.clone(),
        vec![3, 1, 0],
    );

    let mut cycle = StepGraph::new(2, vec![(0, 1), (1, 0)]);
    ok &= check(
        "cycle has no initial ready node",
        cycle.nstate.clone(),
        vec![0, 0],
    );
    ok &= check(
        "cycle boundary cannot become ready",
        cycle.become_ready(0),
        false,
    );
    ok &= check(
        "cycle boundary not terminal",
        cycle.done_stuttering(),
        false,
    );

    if ok {
        println!("KAT_RESULT: SUCCESS (StepGraph modality)");
    } else {
        println!("KAT_RESULT: FAIL (StepGraph modality)");
        std::process::exit(1);
    }
}
