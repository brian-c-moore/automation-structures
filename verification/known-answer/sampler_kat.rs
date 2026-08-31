extern crate automation_structures;

use automation_structures::compositions::sampler::Sampler;

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

    let mut singleton = Sampler::new(vec![5], 1);
    all_ok &= check(
        "weighted low draw accepts singleton",
        singleton.draw_weighted(0, 0),
        true,
    );
    all_ok &= check(
        "sample ceiling rejects second draw",
        singleton.draw_uniform(0),
        false,
    );
    all_ok &= check(
        "selected ownership rejects live zero",
        singleton.zero(0),
        false,
    );
    all_ok &= check(
        "selected weight remains framed",
        singleton.weight(0),
        5,
    );

    let mut live = Sampler::new(vec![3, 0, 5], 2);
    all_ok &= check(
        "zero-support uniform draw rejected",
        live.draw_uniform(1),
        false,
    );
    all_ok &= check(
        "weighted threshold high boundary rejected",
        live.draw_weighted(0, 3),
        false,
    );
    all_ok &= check(
        "weighted threshold last accepted value",
        live.draw_weighted(0, 2),
        true,
    );
    all_ok &= check("first exact selection", live.contains_exec(0), true);
    all_ok &= check("first selection count", live.budget.allocated, 1);
    all_ok &= check("unselected support can be zeroed", live.zero(2), true);
    all_ok &= check(
        "zero commits exact distribution change",
        vec![live.weight(0), live.weight(1), live.weight(2)],
        vec![3, 0, 0],
    );
    all_ok &= check("zero frames selected item", live.contains_exec(0), true);
    all_ok &= check("zero frames selected count", live.budget.allocated, 1);
    all_ok &= check(
        "removed support cannot be drawn",
        live.draw_uniform(2),
        false,
    );
    all_ok &= check("invalid zero index rejected", live.zero(3), false);
    all_ok &= check(
        "invalid zero frames distribution",
        vec![live.weight(0), live.weight(1), live.weight(2)],
        vec![3, 0, 0],
    );

    let mut all_zero = Sampler::new(vec![0, 0], 2);
    all_ok &= check(
        "all-zero uniform policy rejects",
        all_zero.draw_uniform(0),
        false,
    );
    all_ok &= check(
        "all-zero weighted policy rejects",
        all_zero.draw_weighted(1, 0),
        false,
    );
    all_ok &= check(
        "all-zero policy keeps selected empty",
        all_zero.budget.allocated,
        0,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (Sampler safety/support)");
    } else {
        println!("KAT_RESULT: FAIL (Sampler safety/support)");
        std::process::exit(1);
    }
}
