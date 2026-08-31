extern crate automation_structures;

use automation_structures::modalities::stream_graph_fanout::StreamGraphFanout;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn conserved(s: &StreamGraphFanout) -> bool {
    s.ingested.value() as usize == s.left_queue.len() + s.left_emitted.value() as usize
        && s.ingested.value() as usize
            == s.right_queue.len() + s.right_emitted.value() as usize
}

fn main() {
    let mut ok = true;
    ok &= check("valid config", StreamGraphFanout::valid_config(2, 8), true);
    ok &= check(
        "zero capacity rejected",
        StreamGraphFanout::valid_config(0, 8),
        false,
    );
    ok &= check(
        "empty domain rejected",
        StreamGraphFanout::valid_config(2, 0),
        false,
    );

    let mut s = StreamGraphFanout::new(2, 3, 8);
    ok &= check("initial conservation", conserved(&s), true);
    ok &= check("empty left blocked", s.consume_left(), false);
    ok &= check("empty right blocked", s.consume_right(), false);
    ok &= check("out-of-domain blocked", s.source_ingest(8), false);
    ok &= check("first broadcast", s.source_ingest(3), true);
    ok &= check(
        "copies match",
        (s.left_queue.values.clone(), s.right_queue.values.clone()),
        (vec![3], vec![3]),
    );
    ok &= check("left drains independently", s.consume_left(), true);
    ok &= check("second broadcast", s.source_ingest(5), true);
    ok &= check("right capacity blocks source", s.source_ingest(7), false);
    ok &= check("right drains first copy", s.consume_right(), true);
    ok &= check("third broadcast after room", s.source_ingest(7), true);
    ok &= check("input bound blocks source", s.source_ingest(1), false);
    ok &= check("mid-run conservation", conserved(&s), true);
    while s.consume_left() {}
    while s.consume_right() {}
    ok &= check("drained conservation", conserved(&s), true);
    ok &= check("terminal", s.terminal(), true);
    ok &= check(
        "branch totals",
        (s.left_emitted.value(), s.right_emitted.value()),
        (3, 3),
    );

    if ok {
        println!("KAT_RESULT: SUCCESS (StreamGraph fan-out modality)");
    } else {
        println!("KAT_RESULT: FAIL (StreamGraph fan-out modality)");
        std::process::exit(1);
    }
}
