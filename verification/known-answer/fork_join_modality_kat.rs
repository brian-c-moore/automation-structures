extern crate automation_structures;

use automation_structures::modalities::fork_join::ForkJoin;
use automation_structures::ForkJoinPhase;

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
    let mut f = ForkJoin::new(3, 10, 0);
    ok &= check("initial fork phase", f.phase, ForkJoinPhase::Fork);
    ok &= check("early output rejected", f.produce_output(), false);
    ok &= check("incomplete barrier rejected", f.barrier(), false);
    ok &= check("worker bound rejected", f.start_worker(3), false);
    ok &= check("worker 0 starts independently", f.start_worker(0), true);
    ok &= check("worker 1 starts independently", f.start_worker(1), true);
    ok &= check("repeat start rejected", f.start_worker(0), false);
    ok &= check(
        "invalid worker value rejected",
        f.complete_worker(0, 10),
        false,
    );
    ok &= check("worker 0 completes", f.complete_worker(0, 4), true);
    ok &= check(
        "barrier still rejects one ready and one running",
        f.barrier(),
        false,
    );
    ok &= check("worker 2 starts", f.start_worker(2), true);
    ok &= check("worker 2 completes", f.complete_worker(2, 8), true);
    ok &= check("worker 1 completes", f.complete_worker(1, 6), true);
    ok &= check("exact worker values", f.wvalue.clone(), vec![4, 6, 8]);
    ok &= check("barrier admits all-complete state", f.barrier(), true);
    ok &= check("join phase", f.phase, ForkJoinPhase::Join);
    ok &= check(
        "worker start rejected after barrier",
        f.start_worker(0),
        false,
    );
    ok &= check("output produced after join", f.produce_output(), true);
    ok &= check("done phase", f.phase, ForkJoinPhase::Done);
    ok &= check("output readiness", f.output_ready, true);
    ok &= check(
        "output is exact worker snapshot",
        f.output_snapshot.clone(),
        vec![4, 6, 8],
    );
    let before = (f.phase, f.output_ready, f.output_snapshot.clone());
    ok &= check("terminal stutter enabled", f.done_stuttering(), true);
    ok &= check(
        "terminal stutter frame",
        (f.phase, f.output_ready, f.output_snapshot.clone()),
        before,
    );

    if ok {
        println!("KAT_RESULT: SUCCESS (ForkJoin modality)");
    } else {
        println!("KAT_RESULT: FAIL (ForkJoin modality)");
        std::process::exit(1);
    }
}
