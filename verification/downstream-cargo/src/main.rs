//! External checked-API consumer used by the packaged-artifact release gate.

use automation_structures::{
    AllocationSnapshot, Budget, Buffer, CheckedSignedAdd, ForkJoin, IncrementalReduction,
    RecordRefusal, ReductionColumns, ReductionRowError, RelationshipGraph, ResourceRegistry,
    Sequential, Signal, StepGraph, StreamGraph,
};
use std::error::Error;
use vstd::prelude::*;

verus! {
    struct OwnedCount { value: u64 }
    struct AddOwnedCount;
    impl automation_structures::OwnedReductionOperation<OwnedCount> for AddOwnedCount {
        type View = int;
        open spec fn observe(&self, value: OwnedCount) -> int { value.value as int }
        open spec fn accepts(&self, previous: OwnedCount, input: OwnedCount) -> bool {
            previous.value as int + input.value as int <= u64::MAX
        }
        open spec fn combined(&self, previous: OwnedCount, input: OwnedCount) -> int {
            previous.value as int + input.value as int
        }
        fn try_combine(&self, previous: &OwnedCount, input: &OwnedCount)
            -> (result: Result<OwnedCount, automation_structures::OwnedReductionError>)
        {
            match previous.value.checked_add(input.value) {
                Some(value) => Ok(OwnedCount { value }),
                None => Err(automation_structures::OwnedReductionError::Domain),
            }
        }
    }
    struct EncodedSize;
    impl automation_structures::BufferSizeProjection<usize> for EncodedSize {
        open spec fn size_spec(&self, value: usize) -> usize { value }
        fn size(&self, value: &usize) -> (size: usize) { *value }
    }
}

#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions are external consumer test oracles; fallible setup propagates typed errors"
)]
fn main() -> Result<(), Box<dyn Error>> {
    let mut candidates = automation_structures::CandidateTraversal::try_new("version 1", 321, 3)
        .map_err(|(error, _)| error)?;
    let root = candidates
        .admit(None, Box::new(1u64), 2, 0)
        .map_err(|(error, _)| error)?;
    assert_eq!(candidates.step()?, Some(root));
    let child = candidates
        .admit(Some(root), Box::new(2u64), 1, 0)
        .map_err(|(error, _)| error)?;
    assert_eq!(candidates.step()?, Some(child));
    candidates.close();
    let completed = candidates
        .finish()
        .map_err(|_| "candidate completion refused")?;
    assert_eq!(completed.get(child).map(|value| **value), Some(2));
    let mut forest = automation_structures::QualityHierarchy::try_new(2, u64::MAX)?;
    forest.set_node_properties(0, 2, 0)?;
    forest.set_node_properties(1, 1, 0)?;
    forest.add_child(0, 1)?;
    let mut traversal = forest
        .try_traversal()
        .map_err(|(reason, _original)| reason)?;
    assert_eq!(traversal.step(), Some(0));
    assert_eq!(traversal.step(), Some(1));
    assert_eq!(traversal.step(), None);
    let discovered = traversal
        .finish()
        .map_err(|_original| "forest completion refused")?;
    assert_eq!(discovered.discovery_order(), &[0, 1]);
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
    assert!(typed.close_input());
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
    assert!(matches!(
        typed.receive(),
        Err(automation_structures::TypedStreamError::Closed)
    ));
    assert_eq!(
        latest.notify(listener),
        Err(automation_structures::SignalProfileError::UnknownListener)
    );
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
    let mut versions = automation_structures::VersionedReduction::try_new(
        OwnedCount { value: 7 },
        2,
        AddOwnedCount,
    )
    .map_err(|(reason, _, _)| reason)?;
    assert_eq!(
        versions
            .prepare(OwnedCount { value: 4 })
            .map_err(|(reason, _)| reason)?
            .commit(),
        1
    );
    assert_eq!(
        versions
            .prepare(OwnedCount { value: 3 })
            .map_err(|(reason, _)| reason)?
            .commit(),
        2
    );
    assert_eq!(
        versions.version(0).ok_or("missing initial version")?.value,
        7
    );
    assert_eq!(
        versions.version(1).ok_or("missing previous version")?.value,
        11
    );
    assert_eq!(
        versions.version(2).ok_or("missing current version")?.value,
        14
    );
    assert_eq!(versions.processed_len(), 2);
    let mut routes = automation_structures::TypedAllocation::unbudgeted(
        automation_structures::UnrestrictedAllocation,
    );
    routes
        .prepare_batch(vec![
            (7u64, (Box::new(1u64), vec![])),
            (8, (Box::new(99), vec![])),
        ])?
        .commit();
    assert_eq!(routes.dimension_count(), 0);
    assert_eq!(routes.budget(0), None);
    assert_eq!(
        **routes.seal().get(&8).ok_or("missing unbudgeted member")?,
        99
    );
    let mut batch = automation_structures::TypedAllocation::try_new(
        &vec![2, 4],
        automation_structures::UnrestrictedAllocation,
    )?;
    batch
        .prepare_batch(vec![
            (7u64, (Box::new(1u64), vec![1, 1])),
            (8, (Box::new(99), vec![1, 3])),
        ])?
        .commit();
    assert_eq!(batch.budget(1), Some((4, 4)));
    assert_eq!(**batch.get(&8).ok_or("missing admitted batch member")?, 99);
    let owned = Buffer::from_values(vec![Box::new(7u64), Box::new(99)]);
    assert_eq!(
        owned.into_iter().map(|value| *value).collect::<Vec<_>>(),
        vec![7, 99]
    );
    let values = vec![
        automation_structures::NullableSigned::Value(2),
        automation_structures::NullableSigned::Value(1),
    ];
    let order = automation_structures::SignedRowOrder {
        values: &values,
        descending: false,
        nulls_first: false,
    };
    let arranged = automation_structures::IndexArrangement::try_new(2, &order)?;
    assert_eq!(arranged.positions(), &[1, 0]);
    assert_eq!(arranged.rank_of(0), Some(1));
    let mut allocation = automation_structures::TypedAllocation::try_new(
        &vec![2, 8],
        automation_structures::UnrestrictedAllocation,
    )?;
    allocation
        .prepare(
            automation_structures::ByteKey::from_bytes(b"key".to_vec()),
            vec![7u8],
            vec![1, 3],
        )?
        .commit();
    let sealed = allocation.seal();
    assert_eq!(sealed.budget(1), Some((8, 3)));
    assert_eq!(sealed.get_query(&(&b"key"[..])), Some(&vec![7u8]));
    assert_eq!(
        sealed.get(&automation_structures::ByteKey::from_bytes(b"key".to_vec())),
        Some(&vec![7u8])
    );
    let mut columns = ReductionColumns::try_new(&vec![CheckedSignedAdd; 3], 2)?;
    columns.prepare_row(&vec![7, i64::MAX, -4])?.commit();
    assert!(matches!(
        columns.prepare_row(&vec![1, 1, 1]),
        Err(ReductionRowError::Column {
            column: 1,
            reason: RecordRefusal::Domain
        })
    ));
    assert_eq!(columns.column_result(0), Some(7));
    assert_eq!(columns.column_result(1), Some(i64::MAX));
    assert_eq!(columns.column_processed(2), Some(1));
    let mut sizes = Buffer::new(2);
    assert_eq!(sizes.projected_size(&EncodedSize), Ok(0));
    assert_eq!(sizes.push(usize::MAX), Ok(()));
    assert_eq!(sizes.projected_size(&EncodedSize), Ok(usize::MAX));
    assert_eq!(sizes.push(1), Ok(()));
    assert_eq!(
        sizes.projected_size(&EncodedSize),
        Err(automation_structures::BufferSizeError::Overflow)
    );

    let mut buffer = Buffer::try_new(1)?;
    assert_eq!(buffer.push(String::from("payload")), Ok(()));
    assert_eq!(buffer.pop().as_deref(), Some("payload"));

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
    assert!(fork_join.all_complete());
    assert!(fork_join.barrier());
    assert!(fork_join.produce_output());

    let mut step_graph = StepGraph::new(1, vec![])?;
    assert_eq!(step_graph.predecessors_complete(0), Some(true));
    assert!(step_graph.start(0));
    assert!(step_graph.complete(0));

    let mut stream_graph = StreamGraph::new(3, 1, 1, 2)?;
    assert!(stream_graph.ingest(1));
    assert!(stream_graph.advance_first());
    assert_eq!(stream_graph.consume(), Some(1));

    let mut registry = ResourceRegistry::new();
    assert_eq!(registry.try_insert_unique(1, 7), Ok(0));
    assert!(registry.try_insert_unique(1, 99).is_err());
    assert_eq!(registry.get(1), Some(7));

    let captured = AllocationSnapshot::capture(4, 2, &[0, 1], &[3, 2])?;
    assert_eq!(
        captured.accepted_entries().copied().collect::<Vec<_>>(),
        vec![(0, 3)]
    );
    assert_eq!((captured.total_cost(), captured.budget_remaining()), (3, 1));

    let mut reduction = IncrementalReduction::new(2, CheckedSignedAdd);
    assert_eq!(
        reduction
            .prepare(7)
            .map_err(|(reason, _input)| reason)?
            .cancel(),
        7
    );
    assert_eq!((reduction.processed_len(), reduction.result()), (0, 0));
    assert_eq!(
        reduction
            .prepare(i64::MAX)
            .map_err(|(reason, _input)| reason)?
            .commit(),
        (1, i64::MAX)
    );
    assert!(matches!(
        reduction.prepare(1),
        Err((RecordRefusal::Domain, 1))
    ));
    assert_eq!(
        reduction
            .prepare(-i64::MAX)
            .map_err(|(reason, _input)| reason)?
            .commit(),
        (2, 0)
    );
    assert!(matches!(
        reduction.prepare(9),
        Err((RecordRefusal::Capacity, 9))
    ));

    Ok(())
}
