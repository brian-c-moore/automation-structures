extern crate automation_structures;

use automation_structures::primitives::audit_sink::AuditSink;

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

    let empty = AuditSink::new(0);
    all_ok &= check("empty/genesis chain validates", empty.validate(), true);

    let mut s = AuditSink::new(3);
    all_ok &= check("first append accepted", s.record(1), true);
    all_ok &= check("multi-record append 2 accepted", s.record(2), true);
    all_ok &= check("multi-record append 3 accepted", s.record(3), true);
    all_ok &= check("intact multi-record chain validates", s.validate(), true);
    let before_hash = s.last_hash;
    all_ok &= check("capacity rejection", s.record(4), false);
    all_ok &= check("capacity rejection frames length", s.log.len(), 3);
    all_ok &= check("capacity rejection frames head", s.last_hash, before_hash);

    let original_op = s.log[1].operation;
    s.log[1].operation = 7;
    all_ok &= check("operation-only mutation fails recomputation", s.validate(), false);
    s.log[1].operation = original_op;
    all_ok &= check("restored operation validates", s.validate(), true);

    let original_prev = s.log[1].prev_hash;
    s.log[1].prev_hash = original_prev + 1;
    all_ok &= check("link-only mutation fails recomputation", s.validate(), false);
    s.log[1].prev_hash = original_prev;

    let original_record_hash = s.log[1].hash;
    s.log[1].hash = original_record_hash + 1;
    all_ok &= check("stored-hash-only mutation fails recomputation", s.validate(), false);
    s.log[1].hash = original_record_hash;

    s.last_hash += 1;
    all_ok &= check("head-only mutation fails recomputation", s.validate(), false);
    s.last_hash -= 1;
    all_ok &= check("fully restored chain validates", s.validate(), true);

    let mut collision_demo = AuditSink::new(1);
    collision_demo.record(1);
    collision_demo.log[0].operation = 101;
    all_ok &= check(
        "declared ceiling: concrete modulo-hash collision is not detected",
        collision_demo.validate(),
        true,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (AuditSink structural chain; HashCR external)");
    } else {
        println!("KAT_RESULT: FAIL (AuditSink)");
        std::process::exit(1);
    }
}
