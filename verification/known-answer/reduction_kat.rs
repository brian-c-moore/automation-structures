extern crate automation_structures;

use automation_structures::compositions::reduction::{reduce_max, reduce_sum, Reducer};

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

    all_ok &= check("sum empty identity", reduce_sum(&[]), 0);
    all_ok &= check("sum singleton", reduce_sum(&[7]), 7);
    all_ok &= check("sum multi-item ordered prefix", reduce_sum(&[3, 1, 2]), 6);
    all_ok &= check("max empty identity", reduce_max(&[]), 0);
    all_ok &= check("max singleton", reduce_max(&[7]), 7);
    all_ok &= check("max front boundary", reduce_max(&[9, 2, 3]), 9);
    all_ok &= check("max tail boundary", reduce_max(&[1, 2, 9]), 9);
    all_ok &= check(
        "named instances remain distinct",
        (reduce_sum(&[1, 2, 3]), reduce_max(&[1, 2, 3])),
        (6, 3),
    );

    let mut r = Reducer::new(vec![3, 1, 2]);
    all_ok &= check("stream begins undrained", r.done(), false);
    r.process();
    all_ok &= check("consume first updates result", r.result(), 3);
    let consumed: Vec<u64> = r.audit.log.iter().map(|entry| entry.operation).collect();
    all_ok &= check("consume first exact prefix", consumed, vec![3]);
    all_ok &= check(
        "consume first exact suffix",
        r.source[r.position()..].to_vec(),
        vec![1, 2],
    );
    r.process();
    all_ok &= check("consume second updates fold", r.result(), 4);
    r.process();
    all_ok &= check("drained aggregate", r.result(), 6);
    let consumed: Vec<u64> = r.audit.log.iter().map(|entry| entry.operation).collect();
    all_ok &= check("drained exact prefix", consumed, vec![3, 1, 2]);
    all_ok &= check("drained suffix empty", r.remaining_len(), 0);
    all_ok &= check("drain boundary reports done", r.done(), true);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (ReductionStream instances)");
    } else {
        println!("KAT_RESULT: FAIL (ReductionStream instances)");
        std::process::exit(1);
    }
}
