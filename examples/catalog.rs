//! Construct and exercise every structure in the public catalog.

use std::error::Error;

use automation_structures::{
    Accumulator, ActuationPass, AllEdges, AllocationSnapshot, AuditSink, BacktrackingTraversal,
    Bisection, Budget, Buffer, CheckedSignedAdd, CompetitiveSelectionHard,
    CompetitiveSelectionHardExclusive, CompetitiveSelectionRanked, CompetitiveSelectionSoft,
    ConvergenceGovernor, Counter, Cursor, EdgeDirection, EquivalenceClass, FederatedBudget,
    ForkJoin, IncrementalReduction, Marker, PositionalEdgeHandles, PropagationPass,
    QualityHierarchy, RateLimit, Reduction, ReductionColumns, RelationshipGraph, ResourceRegistry,
    Sampler, SelectThenActuate, Sequential, Signal, StepGraph, StreamGraph, TraversalEngine,
    projection_consistent, strictly_before,
};

macro_rules! assert_debuggable {
    ($($value:expr),+ $(,)?) => {
        $(assert!(!format!("{:?}", &$value).is_empty());)+
    };
}

#[expect(
    clippy::panic_in_result_fn,
    reason = "catalog assertions check documented example outcomes; operation failures propagate typed errors"
)]
fn main() -> Result<(), Box<dyn Error>> {
    // Primitives.
    let mut latest = automation_structures::SummarySignal::new(1, 0u64, 1, 2);
    let listener = latest.register()?;
    assert_eq!(latest.set_value(7), Ok(true));
    assert_eq!(latest.notify(listener)?.value, 7);
    assert!(!latest.notify(listener)?.changed);
    latest.remove(listener)?;
    let mut typed = automation_structures::TypedStream::try_new(2, 2, 8)?;
    typed
        .publish(String::from("sample"), 6)
        .map_err(|refusal| refusal.error)?;
    typed.close_input();
    assert_eq!(typed.receive()?.value, "sample");
    assert!(typed.is_drained());
    let mut shared = automation_structures::TypedFanout::try_new(3, 1, 8)?;
    shared
        .publish(String::from("sample"), 6)
        .map_err(|refusal| refusal.error)?;
    shared.close_input();
    for branch in [
        automation_structures::FanoutBranch::Left,
        automation_structures::FanoutBranch::Right,
    ] {
        let observation = shared.observe(branch)?;
        assert_eq!(observation.value, "sample");
        shared.consume(observation.token)?;
    }
    assert!(shared.is_drained());
    let mut budget = Budget::new(8);
    assert!(budget.try_reserve(3));
    budget.commit_reservation(3)?;

    let mut hierarchy = QualityHierarchy::new(2, 2);
    hierarchy.set_node_properties(0, 2, 1)?;
    hierarchy.set_node_properties(1, 1, 2)?;
    hierarchy.add_child(0, 1)?;

    let mut registry = ResourceRegistry::new();
    registry.insert(1, 10);
    assert_eq!(registry.get(1), Some(10));

    let mut hard = CompetitiveSelectionHard::new(2)?;
    hard.update_score(0, 2)?;
    hard.update_score(1, 1)?;
    assert_eq!(hard.evaluate(), 0);

    let mut exclusive = CompetitiveSelectionHardExclusive::new(1, 2, 2)?;
    exclusive.update_score(0, 0, 2)?;
    exclusive.update_score(0, 1, 1)?;
    assert_eq!(exclusive.evaluate(0)?, 0);

    let mut soft = CompetitiveSelectionSoft::begin(vec![3, 1], 4, 3)?;
    assert_eq!(soft.assign_next()?, 0);

    let mut ranked = CompetitiveSelectionRanked::new(vec![2, 1], 1, 2)?;
    ranked.select();
    assert_eq!(ranked.is_selected(0), Some(true));

    let route_metrics = vec![
        automation_structures::NullableSigned::Value(3),
        automation_structures::NullableSigned::Value(1),
        automation_structures::NullableSigned::Value(1),
    ];
    let minimum = automation_structures::CompetitiveSelectionMinimum::try_new(
        automation_structures::SignedRowOrder {
            values: &route_metrics,
            descending: false,
            nulls_first: false,
        },
    )
    .map_err(|(reason, _)| reason)?;
    assert_eq!(minimum.selected(), [1, 2]);

    let mut actuation = ActuationPass::new(vec![Some(7)]);
    actuation.actuate(0)?;
    actuation.finish()?;

    let mut propagation = PropagationPass::new(1, 2, vec![], vec![0])?;
    propagation.start_round()?;
    propagation.update_node(0)?;
    propagation.end_round()?;

    let mut convergence = ConvergenceGovernor::new(2, 6, 2, 10)?;
    assert_eq!(convergence.update(1)?, 1);

    let mut audit = AuditSink::new(1);
    assert!(audit.try_record(7));
    assert!(audit.validate());

    let mut backtracking = BacktrackingTraversal::new(2, 1, 0)?;
    backtracking.descend(1, 1)?;
    backtracking.visit()?;

    // Named compositions.
    let mut snapshot = AllocationSnapshot::new(3, 1);
    snapshot.accept(0, 3)?;
    let snapshot = snapshot.seal();
    assert_eq!(snapshot.total_cost(), 3);

    let mut federated = FederatedBudget::new(4, 1);
    assert!(federated.try_delegate(0, 4));
    assert!(federated.try_allocate(0, 2));

    let mut bisection = Bisection::new(4, 2)?;
    bisection.converge();
    assert!(bisection.is_converged());

    let mut classes = EquivalenceClass::new(2, 1);
    assert!(classes.union(0, 1)?);

    let mut rate_limit = RateLimit::new(1, 1, 1)?;
    assert!(rate_limit.try_acquire());

    let mut reduction = Reduction::new(vec![2, 3])?;
    reduction.process_next()?;

    let mut incremental = IncrementalReduction::new(2, CheckedSignedAdd);
    incremental
        .prepare(7)
        .map_err(|(error, _input)| error)?
        .commit();
    incremental
        .prepare(-4)
        .map_err(|(error, _input)| error)?
        .commit();
    assert_eq!((incremental.processed_len(), incremental.result()), (2, 3));
    let mut columns = ReductionColumns::try_new(&vec![CheckedSignedAdd; 2], 1)?;
    columns.prepare_row(&vec![7, -4])?.commit();
    assert_eq!(columns.column_result(0), Some(7));
    assert_eq!(columns.column_result(1), Some(-4));

    let mut graph = RelationshipGraph::new(2, 1);
    assert!(graph.add_edge(0, 1, 1)?);
    let adjacency = graph
        .materialize(PositionalEdgeHandles { count: 1 }, AllEdges)
        .map_err(|(reason, _, _, _)| reason)?;
    assert_eq!(adjacency.edge_count(), 1);
    assert_eq!(adjacency.edge(&0), Some((0, 1, 1)));
    assert_eq!(
        adjacency.incident(0, EdgeDirection::Outgoing),
        Some([0].as_slice())
    );
    assert_eq!(
        adjacency.incident(1, EdgeDirection::Incoming),
        Some([0].as_slice())
    );
    assert_eq!(adjacency.rank_of(&0, EdgeDirection::Incoming), Some(0));

    let mut sampler = Sampler::new(vec![1, 1], 1);
    sampler.sample(0)?;

    let mut select_then_actuate = SelectThenActuate::new(1, 2)?;
    select_then_actuate.update_score(0, 0, 1)?;
    assert_eq!(select_then_actuate.evaluate(0)?, 0);
    select_then_actuate.actuate(0)?;
    select_then_actuate.finish()?;

    let mut signal = Signal::new(0, 2, 1)?;
    assert!(signal.set_value(1)?);
    signal.notify(0)?;

    let mut traversal = TraversalEngine::new(1, 0, 2)?;
    traversal.visit(0)?;
    assert_eq!(traversal.accepted_cost(), 2);
    traversal.terminate()?;

    // Execution modalities.
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

    // Connective roles.
    let mut cursor = Cursor::new(0);
    cursor.advance_to(1)?;

    let mut accumulator = Accumulator::new(vec![1]);
    assert_eq!(accumulator.advance(), Some(1));
    assert_eq!(accumulator.accumulated(0), Some(1));

    let mut marker = Marker::new(false);
    assert!(marker.set());

    let mut counter = Counter::new(0);
    assert!(counter.try_increment());

    let mut buffer = Buffer::new(1);
    assert_eq!(buffer.push(1), Ok(()));
    assert_eq!(buffer.pop(), Some(1));

    assert!(projection_consistent(true, true));
    assert!(strictly_before(0, 1));

    assert_debuggable!(
        budget,
        hierarchy,
        registry,
        hard,
        exclusive,
        soft,
        ranked,
        actuation,
        propagation,
        convergence,
        audit,
        backtracking,
        snapshot,
        federated,
        bisection,
        classes,
        rate_limit,
        reduction,
        incremental,
        columns,
        adjacency,
        sampler,
        select_then_actuate,
        signal,
        traversal,
        sequential,
        fork_join,
        step_graph,
        stream_graph,
        cursor,
        accumulator,
        marker,
        counter,
        buffer,
    );

    println!("all public automation structures constructed and exercised");
    Ok(())
}
