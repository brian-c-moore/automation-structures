//! External checked-API consumer used by the packaged-artifact release gate.

use automation_structures::{
    Budget, ForkJoin, RelationshipGraph, Sequential, Signal, StepGraph, StreamGraph,
};
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let mut budget = Budget::new(4);
    assert!(budget.try_reserve(2));
    budget.commit_reservation(2)?;

    let mut graph = RelationshipGraph::new(2, 1);
    assert!(graph.add_edge(0, 1, 1)?);

    let mut signal = Signal::new(0, 2, 1)?;
    assert!(signal.set_value(1)?);
    signal.notify(0)?;

    let mut sequential = Sequential::new(1, 2, 0)?;
    assert!(sequential.begin_step());
    assert!(sequential.complete_step(1));

    let mut fork_join = ForkJoin::new(1, 2, 0)?;
    assert!(fork_join.start_worker(0));
    assert!(fork_join.complete_worker(0, 1));
    assert!(fork_join.barrier());
    assert!(fork_join.produce_output());

    let mut step_graph = StepGraph::new(1, vec![])?;
    assert!(step_graph.start(0));
    assert!(step_graph.complete(0));

    let mut stream_graph = StreamGraph::new(3, 1, 1, 2)?;
    assert!(stream_graph.ingest(1));
    assert!(stream_graph.advance_first());
    assert_eq!(stream_graph.consume(), Some(1));

    Ok(())
}
