extern crate automation_structures;

use automation_structures::modalities::stream_graph::StreamGraph;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn conserved(s: &StreamGraph) -> bool {
    let queued = if s.chain_length == 3 {
        s.q1.len() + s.q2.len()
    } else {
        s.q1.len() + s.q2.len() + s.q3.len()
    };
    s.ingested.value() as usize == queued + s.emitted.value() as usize
}

fn main() {
    let mut ok = true;
    ok &= check(
        "three-node config accepted",
        StreamGraph::valid_config(3, 2, 8),
        true,
    );
    ok &= check(
        "four-node config accepted",
        StreamGraph::valid_config(4, 2, 8),
        true,
    );
    ok &= check(
        "zero capacity rejected",
        StreamGraph::valid_config(3, 0, 8),
        false,
    );
    ok &= check(
        "short topology rejected",
        StreamGraph::valid_config(2, 2, 8),
        false,
    );
    ok &= check(
        "long topology rejected",
        StreamGraph::valid_config(5, 2, 8),
        false,
    );
    ok &= check(
        "empty domain rejected",
        StreamGraph::valid_config(3, 2, 0),
        false,
    );

    let mut s = StreamGraph::new(3, 2, 3, 8);
    ok &= check(
        "initial queues empty",
        (
            s.q1.values.clone(),
            s.q2.values.clone(),
            s.q3.values.clone(),
        ),
        (vec![], vec![], vec![]),
    );
    ok &= check("initial conservation", conserved(&s), true);
    ok &= check("empty middle blocked", s.middle2_fire(), false);
    ok &= check("three-node third middle absent", s.middle3_fire(), false);
    ok &= check("empty sink blocked", s.sink_consume(), false);
    ok &= check(
        "not terminal before input bound",
        s.done_stuttering(),
        false,
    );
    ok &= check("out-of-domain source blocked", s.source_ingest(8), false);
    ok &= check("first source ingest", s.source_ingest(3), true);
    ok &= check("second source ingest", s.source_ingest(5), true);
    ok &= check("full source queue blocks ingest", s.source_ingest(7), false);
    ok &= check("source FIFO", s.q1.values.clone(), vec![3, 5]);
    ok &= check("conservation at full source", conserved(&s), true);
    ok &= check("first middle transfer", s.middle2_fire(), true);
    ok &= check("second middle transfer", s.middle2_fire(), true);
    ok &= check("middle FIFO", s.q2.values.clone(), vec![3, 5]);
    ok &= check("third source ingest after room", s.source_ingest(7), true);
    ok &= check("full output queue blocks middle", s.middle2_fire(), false);
    ok &= check("first sink consume", s.sink_consume(), true);
    ok &= check(
        "blocked record transfers after sink room",
        s.middle2_fire(),
        true,
    );
    ok &= check(
        "FIFO after backpressure release",
        s.q2.values.clone(),
        vec![5, 7],
    );
    ok &= check("second sink consume", s.sink_consume(), true);
    ok &= check("third sink consume", s.sink_consume(), true);
    ok &= check("drain conservation", conserved(&s), true);
    ok &= check("input bound blocks later ingest", s.source_ingest(1), false);
    ok &= check("terminal stutter enabled", s.done_stuttering(), true);
    ok &= check(
        "terminal counters",
        (s.ingested.value(), s.emitted.value()),
        (3, 3),
    );

    let mut l = StreamGraph::new(4, 1, 1, 16);
    ok &= check("long-chain source", l.source_ingest(11), true);
    ok &= check("long-chain first middle", l.middle2_fire(), true);
    ok &= check("long-chain record at q2", l.q2.values.clone(), vec![11]);
    ok &= check("long-chain second middle", l.middle3_fire(), true);
    ok &= check("long-chain record at q3", l.q3.values.clone(), vec![11]);
    ok &= check("long-chain sink", l.sink_consume(), true);
    ok &= check("long-chain conservation", conserved(&l), true);
    ok &= check("long-chain terminal", l.done_stuttering(), true);

    if ok {
        println!("KAT_RESULT: SUCCESS (StreamGraph modality)");
    } else {
        println!("KAT_RESULT: FAIL (StreamGraph modality)");
        std::process::exit(1);
    }
}
