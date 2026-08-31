extern crate automation_structures;

use automation_structures::compositions::bisection::Bisection;

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

    // The tight domain-fit instance: 32 = 2^5. Threshold 1 follows the
    // longest branch and consumes exactly MaxProbes steps.
    let mut tight = Bisection::new(0, 32, 1, 32, 5);
    ok &= check("tight domain", tight.domain_size, 32);
    ok &= check("tight max probes", tight.budget.capacity, 5);
    ok &= check("tight initial probes", tight.budget.allocated, 0);
    tight.probe();
    ok &= check("tight step 1 hi", tight.hi, 16);
    ok &= check("tight step 1 probes", tight.budget.allocated, 1);
    tight.probe();
    ok &= check("tight step 2 hi", tight.hi, 8);
    tight.bisect();
    ok &= check("tight converged", tight.hi - tight.lo < 2, true);
    ok &= check("tight endpoint", (tight.lo, tight.hi), (0, 1));
    ok &= check(
        "tight exact budget",
        tight.budget.allocated,
        tight.budget.capacity,
    );

    // A slack budget remains a ceiling, not a required number of probes.
    let mut slack = Bisection::new(0, 16, 15, 16, 5);
    slack.bisect();
    ok &= check("slack converged", slack.hi - slack.lo < 2, true);
    ok &= check(
        "slack threshold bracketed",
        slack.lo <= slack.threshold && slack.threshold <= slack.hi,
        true,
    );
    ok &= check(
        "slack below budget",
        slack.budget.allocated < slack.budget.capacity,
        true,
    );

    // The smallest legal domain reaches the boundary in one step.
    let mut smallest = Bisection::new(0, 2, 1, 2, 1);
    smallest.bisect();
    ok &= check("smallest converged", (smallest.lo, smallest.hi), (0, 1));
    ok &= check("smallest exact budget", smallest.budget.allocated, 1);

    // TLA+ Init permits a valid sub-interval of the configured domain.
    let mut sub = Bisection::new(10, 20, 15, 32, 5);
    sub.bisect();
    ok &= check(
        "sub-interval threshold bracketed",
        sub.lo <= sub.threshold && sub.threshold <= sub.hi,
        true,
    );
    ok &= check(
        "sub-interval within budget",
        sub.budget.allocated <= sub.budget.capacity,
        true,
    );

    if ok {
        println!("KAT_RESULT: SUCCESS (Bisection MaxProbes)");
    } else {
        println!("KAT_RESULT: FAIL (Bisection MaxProbes)");
        std::process::exit(1);
    }
}
