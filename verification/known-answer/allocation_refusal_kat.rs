// Standalone test harness: unsafe is confined to forwarding System's allocator contract.
// No allocator hook, unsafe block or fault switch is part of the library implementation.
use automation_structures::{CheckedSignedAdd, ReductionColumns, ReductionRowError};
use automation_structures::{
    compositions::federated_budget::FederatedBudget,
    modalities::{fork_join::ForkJoin, sequential::Sequential, step_graph::StepGraph},
    primitives::{
        actuation_pass::ActuationPass, audit_sink::AuditSink,
        backtracking_traversal::BacktrackingTraversal,
        competitive_selection::CompetitiveSelectionHard,
        convergence_governor_phase_aware::ConvergenceGovernorPhaseAware,
        propagation_pass::PropagationPass,
    },
};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicIsize, Ordering};

struct FailingAllocator;
static FAIL_AFTER: AtomicIsize = AtomicIsize::new(-1);
static TRIPPED: AtomicBool = AtomicBool::new(false);
#[expect(
    clippy::arithmetic_side_effects,
    reason = "the positive failpoint counter is decremented only after its zero and negative guards"
)]
fn should_fail() -> bool {
    let count = FAIL_AFTER.load(Ordering::SeqCst);
    if count < 0 {
        return false;
    }
    if count == 0 {
        FAIL_AFTER.store(-1, Ordering::SeqCst);
        TRIPPED.store(true, Ordering::SeqCst);
        true
    } else {
        FAIL_AFTER.store(count - 1, Ordering::SeqCst);
        false
    }
}
// SAFETY: successful allocations/deallocations forward the original pointer and Layout
// to System. Injected failures return null, as required by GlobalAlloc. This binary is
// single-threaded while injection is armed; no library implementation relies on this code.
#[expect(
    unsafe_code,
    reason = "the existing test-only GlobalAlloc binding forwards System's original Layout and pointer; failures return null"
)]
unsafe impl GlobalAlloc for FailingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if should_fail() {
            std::ptr::null_mut()
        } else {
            unsafe { System.alloc(layout) }
        }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if should_fail() {
            std::ptr::null_mut()
        } else {
            unsafe { System.alloc_zeroed(layout) }
        }
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        if should_fail() {
            std::ptr::null_mut()
        } else {
            unsafe { System.realloc(pointer, layout, size) }
        }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: FailingAllocator = FailingAllocator;

// Non-Copy native content; no domain allocation can disguise a Registry refusal.
struct OwnedCount(u64);
struct AddOwnedCount;
impl automation_structures::OwnedReductionOperation<OwnedCount> for AddOwnedCount {
    type View = ();
    fn try_combine(
        &self,
        previous: &OwnedCount,
        input: &OwnedCount,
    ) -> Result<OwnedCount, automation_structures::OwnedReductionError> {
        previous
            .0
            .checked_add(input.0)
            .map(OwnedCount)
            .ok_or(automation_structures::OwnedReductionError::Domain)
    }
}

fn fail_at<R>(index: isize, operation: impl FnOnce() -> R) -> R {
    TRIPPED.store(false, Ordering::SeqCst);
    FAIL_AFTER.store(index, Ordering::SeqCst);
    let result = operation();
    FAIL_AFTER.store(-1, Ordering::SeqCst);
    assert!(
        TRIPPED.load(Ordering::SeqCst),
        "the selected allocation was not reached"
    );
    result
}
fn no_allocations<R>(operation: impl FnOnce() -> R) -> R {
    TRIPPED.store(false, Ordering::SeqCst);
    FAIL_AFTER.store(0, Ordering::SeqCst);
    let result = operation();
    FAIL_AFTER.store(-1, Ordering::SeqCst);
    assert!(
        !TRIPPED.load(Ordering::SeqCst),
        "admitted action attempted an allocation"
    );
    result
}

#[expect(
    clippy::panic_in_result_fn,
    reason = "assertions are allocator-fault test oracles; fallible setup propagates typed errors"
)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut summary_signal =
        no_allocations(|| automation_structures::SummarySignal::new(51, 0u64, 1, 3));
    assert_eq!(
        fail_at(0, || summary_signal.register()),
        Err(automation_structures::SignalProfileError::StorageUnavailable)
    );
    assert_eq!(summary_signal.listener_count(), 0);
    let listener = summary_signal.register()?;
    assert_eq!(listener.generation(), 1);
    no_allocations(|| {
        assert_eq!(summary_signal.set_value(7), Ok(true));
        assert_eq!(summary_signal.set_value(9), Ok(true));
        assert_eq!(summary_signal.set_value(9), Ok(false));
        assert_eq!(summary_signal.pending(listener), Ok(true));
        assert_eq!(
            summary_signal.notify(listener),
            Ok(automation_structures::SignalObservation {
                value: 9,
                head: 2,
                changed: true
            })
        );
        assert_eq!(
            summary_signal.notify(listener),
            Ok(automation_structures::SignalObservation {
                value: 9,
                head: 2,
                changed: false
            })
        );
        assert_eq!(summary_signal.remove(listener), Ok(()));
        assert_eq!(
            summary_signal.notify(listener),
            Err(automation_structures::SignalProfileError::UnknownListener)
        );
    });
    let reused_storage = no_allocations(|| summary_signal.register())?;
    assert_eq!(reused_storage.generation(), 2);
    let (reason, initial, _operator) = fail_at(0, || {
        automation_structures::VersionedReduction::try_new(OwnedCount(7), 32, AddOwnedCount)
    })
    .err()
    .ok_or("initial version storage failure was admitted")?;
    assert_eq!(
        reason,
        automation_structures::OwnedReductionError::StorageUnavailable
    );
    assert_eq!(initial.0, 7);
    let mut versions =
        automation_structures::VersionedReduction::try_new(OwnedCount(7), 32, AddOwnedCount)
            .map_err(|(reason, _, _)| reason)?;
    let mut storage_refusal = false;
    // Vec may reserve more than requested. Reach its next growth within a bounded
    // batch and distinguish refusal by the allocator's actual attempted call.
    for _ in 0..16 {
        let prefix = versions.processed_len();
        let value = versions
            .version(prefix)
            .ok_or("missing owned carried version")?
            .0;
        TRIPPED.store(false, Ordering::SeqCst);
        FAIL_AFTER.store(0, Ordering::SeqCst);
        let prepared = versions.prepare(OwnedCount(3));
        FAIL_AFTER.store(-1, Ordering::SeqCst);
        match prepared {
            Ok(prepared) => {
                no_allocations(|| prepared.commit());
            }
            Err((reason, returned)) => {
                assert!(TRIPPED.load(Ordering::SeqCst));
                assert_eq!(
                    reason,
                    automation_structures::OwnedReductionError::StorageUnavailable
                );
                assert_eq!(returned.0, 3);
                assert_eq!(versions.processed_len(), prefix);
                assert_eq!(
                    versions
                        .version(prefix)
                        .ok_or("lost carried version on refusal")?
                        .0,
                    value
                );
                storage_refusal = true;
                break;
            }
        }
    }
    assert!(
        storage_refusal,
        "bounded Registry growth control did not reach a reservation"
    );
    let prepared = versions
        .prepare(OwnedCount(3))
        .map_err(|(reason, _)| reason)?;
    let committed = no_allocations(|| prepared.commit());
    assert_eq!(committed, versions.processed_len());
    assert_eq!(
        versions.version(0).ok_or("initial version was replaced")?.0,
        7
    );
    // Original handles plus forward/inverse/handle/offset storage in each direction.
    for site in 0..9 {
        let mut graph = automation_structures::RelationshipGraph::new(3, 10);
        assert!(graph.add_edge(0, 1, 3)?);
        assert!(graph.add_edge(0, 2, 7)?);
        assert!(graph.add_edge(1, 2, 9)?);
        let (reason, graph, domain, _predicate) = fail_at(site, || {
            graph.materialize(
                automation_structures::PositionalEdgeHandles { count: 3 },
                automation_structures::AllEdges,
            )
        })
        .err()
        .ok_or("adjacency allocation failure admitted")?;
        assert_eq!(
            reason,
            automation_structures::AdjacencyBuildError::StorageUnavailable
        );
        assert_eq!(graph.num_nodes(), 3);
        assert_eq!(graph.edge_count(), 3);
        assert_eq!(
            graph.edges().collect::<Vec<_>>(),
            vec![(0, 1, 3), (0, 2, 7), (1, 2, 9)]
        );
        assert_eq!(domain.count, 3);
    }
    let mut graph = automation_structures::RelationshipGraph::new(3, 10);
    assert!(graph.add_edge(0, 1, 3)?);
    assert!(graph.add_edge(0, 2, 7)?);
    assert!(graph.add_edge(1, 2, 9)?);
    let adjacency = graph
        .materialize(
            automation_structures::PositionalEdgeHandles { count: 3 },
            automation_structures::AllEdges,
        )
        .map_err(|(reason, _graph, _domain, _predicate)| reason)?;
    no_allocations(|| {
        use automation_structures::EdgeDirection::{Incoming, Outgoing};
        assert_eq!(
            adjacency.incident(0, Outgoing),
            Some([0usize, 1].as_slice())
        );
        assert_eq!(
            adjacency.incident(2, Incoming),
            Some([1usize, 2].as_slice())
        );
        assert_eq!(adjacency.edge(&2), Some((1, 2, 9)));
        assert_eq!(adjacency.rank_of(&2, Incoming), Some(2));
        assert_eq!(adjacency.handle_at(usize::MAX), None);
    });
    // An unbudgeted batch reserves pending identities and final member storage.
    for site in 0..2 {
        let mut allocation = automation_structures::TypedAllocation::unbudgeted(
            automation_structures::UnrestrictedAllocation,
        );
        let items = vec![(7u64, (vec![3u8], vec![])), (8, (vec![1u8], vec![]))];
        let address = items.as_ptr();
        let refused = fail_at(site, || allocation.prepare_batch(items))
            .err()
            .ok_or("unbudgeted batch allocation failure admitted")?;
        assert_eq!(
            refused.reason,
            Some(automation_structures::TypedAllocationError::StorageUnavailable)
        );
        assert_eq!(refused.items.as_ptr(), address);
        assert_eq!(allocation.len(), 0);
        assert_eq!(allocation.dimension_count(), 0);
    }
    let mut allocation = automation_structures::TypedAllocation::unbudgeted(
        automation_structures::UnrestrictedAllocation,
    );
    let value = vec![3u8];
    let charges = vec![];
    let address = value.as_ptr();
    let refused = fail_at(0, || allocation.prepare(7u64, value, charges))
        .err()
        .ok_or("unbudgeted entry allocation failure admitted")?;
    assert_eq!(
        refused.reason,
        Some(automation_structures::TypedAllocationError::StorageUnavailable)
    );
    assert_eq!(refused.value, vec![3]);
    assert_eq!(refused.value.as_ptr(), address);
    assert_eq!(allocation.len(), 0);
    let prepared =
        allocation.prepare_batch(vec![(7u64, (vec![3u8], vec![])), (8, (vec![1u8], vec![]))])?;
    no_allocations(|| prepared.commit());
    assert_eq!(allocation.len(), 2);
    // AdditiveChain is zero-sized: the operator Vec allocates no backing memory.
    // The five actual sites are column owners, pending identities, two prepared
    // rows, and final member storage.
    for site in 0..5 {
        let mut allocation = automation_structures::TypedAllocation::try_new(
            &vec![2, 8],
            automation_structures::UnrestrictedAllocation,
        )?;
        let items = vec![
            (7u64, (vec![3u8], vec![1, 2])),
            (8, (vec![1u8], vec![1, 6])),
        ];
        let address = items.as_ptr();
        let first = items
            .first()
            .ok_or("missing first batch item")?
            .1
            .0
            .as_ptr();
        let refused = fail_at(site, || allocation.prepare_batch(items))
            .err()
            .ok_or("batch allocation failure admitted")?;
        assert_eq!(
            refused.reason,
            Some(automation_structures::TypedAllocationError::StorageUnavailable)
        );
        assert_eq!(refused.items.as_ptr(), address);
        assert_eq!(
            refused
                .items
                .first()
                .ok_or("missing returned first item")?
                .1
                .0
                .as_ptr(),
            first
        );
        assert_eq!(allocation.len(), 0);
        assert_eq!(allocation.budget(1), Some((8, 0)));
    }
    let mut batch_allocation = automation_structures::TypedAllocation::try_new(
        &vec![2, 8],
        automation_structures::UnrestrictedAllocation,
    )?;
    let prepared = batch_allocation.prepare_batch(vec![
        (7u64, (vec![3u8], vec![1, 2])),
        (8, (vec![1u8], vec![1, 6])),
    ])?;
    no_allocations(|| prepared.commit());
    assert_eq!(batch_allocation.len(), 2);
    assert_eq!(batch_allocation.budget(1), Some((8, 8)));
    let empty = Vec::<(u64, (Vec<u8>, Vec<u64>))>::new();
    no_allocations(|| -> Result<(), Box<dyn std::error::Error>> {
        batch_allocation.prepare_batch(empty)?.commit();
        Ok(())
    })?;
    let mut bytes = automation_structures::TypedAllocation::try_new(
        &vec![1, 2],
        automation_structures::UnrestrictedAllocation,
    )?;
    bytes
        .prepare(
            automation_structures::ByteKey::from_bytes(vec![0, 255]),
            vec![7u8],
            vec![1, 1],
        )?
        .commit();
    no_allocations(|| {
        assert_eq!(
            bytes.get_query(&(&[0, 255][..])).map(Vec::as_slice),
            Some([7u8].as_slice())
        );
    });
    let owned = automation_structures::Buffer::from_values(vec![Box::new(7u64), Box::new(99u64)]);
    no_allocations(|| {
        let mut transfer = owned.into_iter();
        assert_eq!(transfer.next().map(|value| *value), Some(7));
        assert_eq!(transfer.next().map(|value| *value), Some(99));
        assert!(transfer.next().is_none());
    });
    let admission_capacities = vec![2, 8];
    assert!(matches!(
        fail_at(0, || {
            automation_structures::TypedAllocation::<u64, Vec<u8>>::try_new(
                &admission_capacities,
                automation_structures::UnrestrictedAllocation,
            )
        }),
        Err(automation_structures::TypedAllocationError::StorageUnavailable)
    ));
    let mut allocation = automation_structures::TypedAllocation::try_new(
        &vec![2, 8],
        automation_structures::UnrestrictedAllocation,
    )?;
    let payload = vec![3u8, 1];
    let payload_address = payload.as_ptr();
    let charges = vec![1, 2];
    let charges_address = charges.as_ptr();
    let refused = fail_at(0, || allocation.prepare(7u64, payload, charges))
        .err()
        .ok_or("entry allocation failure admitted")?;
    assert_eq!(
        refused.reason,
        Some(automation_structures::TypedAllocationError::StorageUnavailable)
    );
    assert_eq!(refused.value.as_ptr(), payload_address);
    assert_eq!(refused.charges.as_ptr(), charges_address);
    assert_eq!(allocation.len(), 0);
    assert_eq!(allocation.budget(0), Some((2, 0)));
    assert_eq!(allocation.budget(1), Some((8, 0)));
    let prepared = allocation.prepare(refused.key, refused.value, refused.charges)?;
    no_allocations(|| prepared.commit());
    assert_eq!(allocation.len(), 1);
    assert_eq!(allocation.budget(0), Some((2, 1)));
    assert_eq!(allocation.budget(1), Some((8, 2)));
    assert_eq!(
        allocation
            .get(&7)
            .ok_or("missing admitted payload")?
            .as_ptr(),
        payload_address
    );
    let values = vec![
        automation_structures::NullableSigned::Value(2),
        automation_structures::NullableSigned::Value(1),
    ];
    let order = automation_structures::connectives::ordering_pass::SignedRowOrder {
        values: &values,
        descending: false,
        nulls_first: false,
    };
    for allocation in 0..2 {
        assert!(matches!(
            fail_at(allocation, || {
                automation_structures::IndexArrangement::try_new(2, &order)
            }),
            Err(automation_structures::connectives::ordering_pass::ArrangementError::Allocation)
        ));
        assert_eq!(
            values,
            vec![
                automation_structures::NullableSigned::Value(2),
                automation_structures::NullableSigned::Value(1)
            ]
        );
    }
    let arranged = automation_structures::IndexArrangement::try_new(2, &order)?;
    no_allocations(|| {
        assert_eq!(arranged.positions(), &[1, 0]);
        assert_eq!(arranged.inverse(), &[1, 0]);
        assert_eq!(arranged.rank_of(0), Some(1));
    });
    let borrowed = [1_000_000_000, 0, 1_000_000_000];
    no_allocations(|| {
        assert_eq!(
            automation_structures::compositions::reduction::reduce_sum(&borrowed),
            2_000_000_000
        );
        assert_eq!(
            automation_structures::compositions::reduction::reduce_max(&borrowed),
            1_000_000_000
        );
    });
    let operators = vec![CheckedSignedAdd; 3];
    assert!(matches!(
        fail_at(0, || ReductionColumns::try_new(&operators, 2)),
        Err(ReductionRowError::StorageUnavailable)
    ));
    let mut columns = ReductionColumns::try_new(&operators, 2)?;
    let items = vec![7, -4, 8];
    assert!(matches!(
        fail_at(0, || columns.prepare_row(&items)),
        Err(ReductionRowError::StorageUnavailable)
    ));
    for column in 0..3 {
        assert_eq!(columns.column_processed(column), Some(0));
        assert_eq!(columns.column_result(column), Some(0));
    }
    let row = columns.prepare_row(&items)?;
    no_allocations(|| row.commit());
    for (column, item) in items.iter().copied().enumerate() {
        assert_eq!(columns.column_processed(column), Some(1));
        assert_eq!(columns.column_result(column), Some(item));
    }
    assert!(fail_at(0, || CompetitiveSelectionHard::try_new(4)).is_err());
    let minima = vec![
        automation_structures::NullableSigned::Value(3),
        automation_structures::NullableSigned::Value(1),
    ];
    let original = minima.as_ptr();
    for site in 0..3 {
        let (reason, returned) = fail_at(site, || {
            automation_structures::CompetitiveSelectionMinimum::try_new(
                automation_structures::SignedRowOrder {
                    values: &minima,
                    descending: false,
                    nulls_first: false,
                },
            )
        })
        .err()
        .ok_or("missing complete minimum storage refusal")?;
        assert_eq!(reason, automation_structures::ArrangementError::Allocation);
        assert_eq!(returned.values.as_ptr(), original);
    }
    let empty_minima = Vec::new();
    let empty_selection = no_allocations(|| {
        automation_structures::CompetitiveSelectionMinimum::try_new(
            automation_structures::SignedRowOrder {
                values: &empty_minima,
                descending: false,
                nulls_first: false,
            },
        )
    })
    .map_err(|(reason, _)| reason)?;
    assert!(empty_selection.is_empty());
    let edges = vec![(0, 1)];
    let address = edges.as_ptr();
    let (_, edges) = fail_at(0, || StepGraph::try_new(2, edges))
        .err()
        .ok_or("missing StepGraph refusal")?;
    assert_eq!(edges.as_ptr(), address);
    assert_eq!(edges, vec![(0, 1)]);
    let assignments = vec![Some(2), None];
    let address = assignments.as_ptr();
    let (_, assignments) = fail_at(0, || ActuationPass::try_new(assignments, 2))
        .err()
        .ok_or("missing ActuationPass refusal")?;
    assert_eq!(assignments.as_ptr(), address);
    assert_eq!(assignments, vec![Some(2), None]);
    assert!(fail_at(0, || Sequential::try_new(3, 10, 0)).is_err());
    for allocation in 0..3 {
        assert!(fail_at(allocation, || ForkJoin::try_new(3, 10, 0)).is_err());
    }
    assert!(fail_at(0, || FederatedBudget::try_new(10, 3)).is_err());
    assert!(fail_at(0, || ConvergenceGovernorPhaseAware::try_new(3, 6, 3, 9)).is_err());
    let mut audit = AuditSink::new(4);
    assert!(audit.record(7));
    let before = (audit.log.len(), audit.last_hash, audit.max_log_len);
    let additional = audit
        .log
        .capacity()
        .checked_add(1)
        .ok_or("audit reserve fixture overflow")?;
    assert!(fail_at(0, || audit.try_reserve_records(additional)).is_err());
    assert_eq!(
        (audit.log.len(), audit.last_hash, audit.max_log_len),
        before
    );
    assert_eq!(
        audit
            .log
            .first()
            .ok_or("missing retained audit entry")?
            .operation,
        7
    );
    assert!(audit.validate());
    for allocation in 0..2 {
        let edges = vec![(0, 1)];
        let values = vec![0, 2];
        let addresses = (edges.as_ptr(), values.as_ptr());
        let (_, ceiling, edges, values) = fail_at(allocation, || {
            PropagationPass::try_new(2, 4, 10, edges, values)
        })
        .err()
        .ok_or("missing PropagationPass refusal")?;
        assert_eq!(ceiling, 10);
        assert_eq!((edges.as_ptr(), values.as_ptr()), addresses);
        assert_eq!(values, vec![0, 2]);
        assert!(fail_at(allocation, || BacktrackingTraversal::try_new(2, 3, 0)).is_err());
    }
    for allocation in 0..2 {
        let mut traversal =
            BacktrackingTraversal::try_new(2, 1, 0).map_err(|(error, _domain, _initial)| error)?;
        traversal.descend(1, 1);
        let before = (
            traversal.path.as_ptr(),
            traversal.ledger.as_ptr(),
            traversal.aux,
        );
        assert!(fail_at(allocation, || traversal.try_visit()).is_err());
        assert_eq!(
            (
                traversal.path.as_ptr(),
                traversal.ledger.as_ptr(),
                traversal.aux
            ),
            before
        );
        assert_eq!(traversal.path, vec![1]);
        assert_eq!(traversal.ledger.len(), 1);
        let token = traversal
            .ledger
            .first()
            .ok_or("missing retained undo token")?;
        assert_eq!((token.saved, token.delta), (0, 1));
        assert!(traversal.visited.is_empty());
        traversal.ascend();
        assert_eq!(traversal.aux, 0);
    }
    for allocation in 0..2 {
        let refused = fail_at(allocation, || {
            automation_structures::TypedStream::<u64>::try_new(59, 2, 4)
        });
        assert!(matches!(
            refused,
            Err(automation_structures::TypedStreamError::StorageUnavailable)
        ));
    }
    let mut stream = automation_structures::TypedStream::try_new(59, 2, 4)?;
    no_allocations(|| -> Result<(), automation_structures::TypedStreamError> {
        assert_eq!(stream.publish(7u64, 2).map_err(|refusal| refusal.error)?, 0);
        assert_eq!(stream.publish(9u64, 2).map_err(|refusal| refusal.error)?, 1);
        assert!(
            matches!(stream.publish(11u64, 0), Err(refusal) if refusal.error == automation_structures::TypedStreamError::SlotCapacity && refusal.value == 11)
        );
        assert_eq!(stream.receive()?.value, 7);
        assert_eq!(
            stream.publish(13u64, 2).map_err(|refusal| refusal.error)?,
            2
        );
        assert_eq!(stream.receive()?.value, 9);
        assert!(stream.close_input());
        assert_eq!(stream.receive()?.value, 13);
        assert!(stream.is_drained());
        assert!(matches!(
            stream.receive(),
            Err(automation_structures::TypedStreamError::Closed)
        ));
        Ok(())
    })?;
    let _empty_stream =
        no_allocations(|| automation_structures::TypedStream::<u64>::try_new(60, 0, 0))?;
    for allocation in 0..2 {
        let refused = fail_at(allocation, || {
            automation_structures::TypedFanout::<OwnedCount>::try_new(61, 2, 4)
        });
        assert!(matches!(
            refused,
            Err(automation_structures::TypedFanoutError::StorageUnavailable)
        ));
    }
    let mut fanout = automation_structures::TypedFanout::try_new(61, 2, 4)?;
    let refused = fail_at(0, || fanout.publish(OwnedCount(7), 2));
    assert!(
        matches!(refused, Err(refusal) if refusal.error == automation_structures::TypedFanoutError::StorageUnavailable && refusal.value.0 == 7)
    );
    assert_eq!((fanout.retained_len(), fanout.retained_bytes()), (0, 0));
    assert_eq!(
        fanout.pending_len(automation_structures::FanoutBranch::Left),
        0
    );
    assert_eq!(
        fanout.pending_len(automation_structures::FanoutBranch::Right),
        0
    );
    assert_eq!(
        fanout
            .publish(OwnedCount(9), 2)
            .map_err(|refusal| refusal.error)?,
        0
    );
    no_allocations(|| -> Result<(), automation_structures::TypedFanoutError> {
        assert_eq!(
            fanout
                .publish(OwnedCount(11), 2)
                .map_err(|refusal| refusal.error)?,
            1
        );
        let left = fanout.observe(automation_structures::FanoutBranch::Left)?;
        assert_eq!(left.value.0, 9);
        fanout.consume(left.token)?;
        assert_eq!(fanout.retained_bytes(), 4);
        assert!(
            matches!(fanout.publish(OwnedCount(13), 0), Err(refusal) if refusal.error == automation_structures::TypedFanoutError::BranchCapacity && refusal.value.0 == 13)
        );
        let right = fanout
            .observe(automation_structures::FanoutBranch::Right)?
            .token;
        fanout.consume(right)?;
        assert_eq!(fanout.retained_bytes(), 2);
        assert_eq!(
            fanout
                .publish(OwnedCount(15), 2)
                .map_err(|refusal| refusal.error)?,
            2
        );
        assert!(fanout.close_input());
        for branch in [
            automation_structures::FanoutBranch::Left,
            automation_structures::FanoutBranch::Right,
        ] {
            for expected in [11, 15] {
                let observation = fanout.observe(branch)?;
                assert_eq!(observation.value.0, expected);
                fanout.consume(observation.token)?;
            }
        }
        assert!(fanout.is_drained());
        assert_eq!((fanout.retained_len(), fanout.retained_bytes()), (0, 0));
        Ok(())
    })?;
    let mut sequence = Sequential::try_new(3, 10, 0)?;
    for allocation in 0..4 {
        let refused = fail_at(allocation, || {
            automation_structures::QualityHierarchy::try_new(4, u64::MAX)
        });
        assert!(refused.is_err());
    }
    let mut hierarchy =
        automation_structures::primitives::quality_hierarchy::QualityHierarchy::try_new(
            4,
            u64::MAX,
        )?;
    no_allocations(|| {
        hierarchy.set_node_properties(0, u64::MAX, 0);
        hierarchy.set_node_properties(1, 2, 0);
        hierarchy.set_node_properties(2, 1, 0);
        hierarchy.add_child(0, 1);
        hierarchy.add_child(1, 2);
        assert_eq!(hierarchy.parent_of(2), 1);
        assert!(hierarchy.has_edge(0, 1));
        assert!(hierarchy.has_edge(1, 2));
        assert_eq!(hierarchy.parent_of(3), 4);
    });
    for allocation in 0..4 {
        let refused = fail_at(allocation, || {
            automation_structures::TraversalEngine::try_new(4, 0, 8)
        });
        assert!(matches!(
            refused,
            Err(automation_structures::TraversalBuildError::StorageUnavailable)
        ));
    }
    let mut work =
        automation_structures::compositions::traversal_engine::TraversalEngine::try_new(4, 0, 8)?;
    no_allocations(|| {
        work.visit_node(0);
        work.visit_node(2);
        work.skip(1);
        work.visit_node(3);
        work.terminate();
        assert_eq!(
            (work.queue.len(), work.accepted.len(), work.budget.allocated),
            (0, 3, 6)
        );
    });
    for allocation in 0..6 {
        let hierarchy = automation_structures::QualityHierarchy::try_new(4, u64::MAX)?;
        let refused = fail_at(allocation, || hierarchy.try_traversal());
        match refused {
            Err((automation_structures::TraversalBuildError::StorageUnavailable, original)) => {
                assert_eq!((original.len(), original.edge_count()), (4, 0));
                assert_eq!(original.encoded_parents(), &[4; 4]);
            }
            _ => return Err("forest work reservation did not refuse".into()),
        }
    }
    let mut forest = automation_structures::QualityHierarchy::try_new(4, u64::MAX)?;
    forest.set_node_properties(0, u64::MAX, 0)?;
    forest.set_node_properties(1, 2, 0)?;
    forest.set_node_properties(2, 1, 0)?;
    forest.add_child(0, 1)?;
    forest.add_child(1, 2)?;
    let mut forest = forest
        .try_traversal()
        .map_err(|(reason, _original)| reason)?;
    no_allocations(|| {
        assert_eq!(forest.step(), Some(0));
        assert_eq!(forest.step(), Some(1));
        assert_eq!(forest.step(), Some(2));
        assert_eq!(forest.step(), Some(3));
        assert_eq!(forest.step(), None);
        assert!(forest.finish().is_ok());
    });
    for site in 0..9 {
        let result = fail_at(site, || {
            automation_structures::CandidateTraversal::<_, u64>::try_new(17u64, 501, 4)
        });
        match result {
            Err((automation_structures::CandidateTraversalError::StorageUnavailable, context)) => {
                assert_eq!(context, 17)
            }
            _ => {
                return Err(
                    "dynamic candidate constructor did not preserve context on storage refusal"
                        .into(),
                );
            }
        }
    }
    let mut candidates = automation_structures::CandidateTraversal::try_new(17u64, 502, 4)
        .map_err(|(error, _)| error)?;
    let root = no_allocations(|| candidates.admit(None, OwnedCount(1), 4, 0))
        .map_err(|(error, _)| error)?;
    for site in 0..2 {
        let result = fail_at(site, || candidates.step());
        assert_eq!(
            result,
            Err(automation_structures::CandidateTraversalError::StorageUnavailable)
        );
        assert_eq!((candidates.len(), candidates.pending()), (1, 1));
        assert_eq!(candidates.get(root).map(|value| value.0), Some(1));
    }
    assert_eq!(candidates.step()?, Some(root));
    let child = no_allocations(|| candidates.admit(Some(root), OwnedCount(2), 1, 0))
        .map_err(|(error, _)| error)?;
    assert_eq!(candidates.step()?, Some(child));
    no_allocations(|| candidates.close());
    let completed = no_allocations(|| {
        candidates
            .finish()
            .map_err(|_| "dynamic completion refused")
    })?;
    assert_eq!(completed.get(child).map(|value| value.0), Some(2));
    let mut fork = ForkJoin::try_new(3, 10, 0)?;
    let mut propagation = PropagationPass::try_new(2, 4, 10, vec![(0, 1)], vec![0, 2])
        .map_err(|(error, _domain, _edges, _values)| error)?;
    let mut traversal =
        BacktrackingTraversal::try_new(2, 3, 0).map_err(|(error, _domain, _initial)| error)?;
    no_allocations(|| {
        for value in [1u64, 2, 3] {
            assert!(sequence.begin_step());
            assert!(sequence.complete_step(value));
        }
        for i in 0..3 {
            assert!(fork.start_worker(i));
            assert!(fork.complete_worker(i, 7));
        }
        assert!(fork.barrier());
        assert!(fork.produce_output());
        for _ in 0..3 {
            propagation.start_round();
            propagation.update_node(0);
            propagation.update_node(1);
            propagation.end_round();
        }
        for _ in 0..3 {
            traversal.descend(1, 1);
        }
        for _ in 0..3 {
            traversal.ascend();
        }
    });
    println!(
        "allocation-refusal KAT: valid-input failures preserve owners; admitted actions allocate no arrays"
    );
    println!("KAT_RESULT: SUCCESS (allocation refusals and admitted storage actions)");
    Ok(())
}
