use automation_structures::{
    Accumulator, ActuationError, ActuationPass, AllocationSnapshot, AllocationSnapshotError,
    AuditRecord, AuditSink, BacktrackingBuildError, BacktrackingError, BacktrackingTraversal,
    Bisection, Budget, BudgetError, Buffer, CompetitiveSelectionError, CompetitiveSelectionHard,
    CompetitiveSelectionHardExclusive, CompetitiveSelectionRanked, CompetitiveSelectionSoft,
    ConvergenceBuildError, ConvergenceError, ConvergenceGovernor, ConvergencePhase,
    ConvergenceState, Counter, Cursor, CursorError, EquivalenceClass, EquivalenceClassError,
    FederatedBudget, ForkJoin, ForkJoinPhase, Marker, PropagationBuildError, PropagationError,
    PropagationPass, QualityHierarchy, QualityHierarchyError, RateLimit, RateLimitError, Reduction,
    ReductionError, RelationshipGraph, RelationshipGraphError, ResourceRegistry, Sampler,
    SamplerError, SelectThenActuate, SelectThenActuateBuildError, SelectThenActuateError,
    Sequential, Signal, SignalError, StepGraph, StepGraphBuildError, StepState, StreamGraph,
    TraversalEngine, TraversalError, WorkerState, projection_consistent, strictly_before,
};

#[test]
fn checked_budget_api_preserves_guards_and_observations() {
    let mut budget = Budget::new(10);

    assert_eq!(budget.capacity(), 10);
    assert_eq!(budget.available(), 10);
    assert!(budget.try_reserve(4));
    assert!(!budget.try_allocate(7));
    assert_eq!(
        budget.commit_reservation(5),
        Err(BudgetError::AmountExceedsReservation)
    );
    assert_eq!(budget.commit_reservation(4), Ok(()));
    assert_eq!(budget.mark_eviction(3), Ok(()));
    assert_eq!(budget.pending_eviction(), 3);
    assert_eq!(
        budget.complete_eviction(4),
        Err(BudgetError::AmountExceedsPendingEviction)
    );
    assert_eq!(budget.complete_eviction(3), Ok(()));
    assert_eq!(budget.allocated(), 1);
    assert_eq!(budget.reserved(), 0);
    assert_eq!(budget.release(2), Err(BudgetError::AmountExceedsAllocation));
    assert_eq!(budget.release(1), Ok(()));
    assert_eq!(budget.available(), 10);
}

#[test]
fn checked_cursor_api_refuses_regression() {
    let mut cursor = Cursor::new(3);

    assert_eq!(cursor.advance_to(2), Err(CursorError::Regression));
    assert_eq!(cursor.position(), 3);
    assert_eq!(cursor.advance_to(5), Ok(()));
    assert_eq!(cursor.position(), 5);
    assert_eq!(cursor.advance_to(5), Ok(()));
    assert_eq!(cursor.position(), 5);
}

#[test]
fn checked_registry_returns_prior_values() {
    let mut registry = ResourceRegistry::new();
    assert!(registry.is_empty());
    assert_eq!(registry.insert(4, 10), None);
    assert_eq!(registry.insert(4, 20), Some(10));
    assert_eq!(registry.get(4), Some(20));
    assert_eq!(registry.entry(0), Some((4, 20)));
    assert_eq!(registry.entry(1), None);
    assert_eq!(registry.remove(4), Some(20));
    assert_eq!(registry.remove(4), None);
    assert_eq!(registry.len(), 0);
}

#[test]
fn checked_registry_preserves_deterministic_survivor_order() {
    let mut registry = ResourceRegistry::new();
    assert_eq!(registry.insert(1, 10), None);
    assert_eq!(registry.insert(2, 20), None);
    assert_eq!(registry.insert(3, 30), None);
    assert_eq!(registry.insert(2, 21), Some(20));
    assert_eq!(registry.entry(0), Some((1, 10)));
    assert_eq!(registry.entry(1), Some((3, 30)));
    assert_eq!(registry.entry(2), Some((2, 21)));
    assert_eq!(registry.remove(1), Some(10));
    assert_eq!(registry.entry(0), Some((3, 30)));
    assert_eq!(registry.entry(1), Some((2, 21)));
}

#[cfg(feature = "proof-api")]
#[test]
fn proof_registry_instantiates_with_typed_composition_keys() {
    use automation_structures::primitives::resource_registry::ResourceRegistry as ProofRegistry;

    let mut registry: ProofRegistry<(usize, usize, u64), ()> = ProofRegistry::new();
    registry.register((1, 2, 3), ());
    assert_eq!(registry.lookup((1, 2, 3)), Some(()));
    assert_eq!(registry.lookup((1, 2, 4)), None);
}

#[test]
fn checked_audit_sink_bounds_append_and_exposes_immutable_records() {
    let mut sink = AuditSink::new(1);
    assert!(sink.is_empty());
    assert!(sink.try_record(9));
    assert!(!sink.try_record(10));
    assert_eq!(sink.capacity(), 1);
    assert_eq!(sink.len(), 1);
    assert_eq!(sink.last_hash(), 10);
    assert_eq!(
        sink.record(0),
        Some(AuditRecord {
            operation: 9,
            previous_hash: 0,
            hash: 10,
        })
    );
    assert_eq!(sink.record(1), None);
    assert!(sink.validate());
}

#[test]
fn checked_propagation_rejects_disabled_actions() {
    assert!(matches!(
        PropagationPass::new(2, 3, vec![], vec![4]),
        Err(PropagationBuildError::InitialValueOutOfRange)
    ));
    assert!(matches!(
        PropagationPass::new(2, 3, vec![(0, 1)], vec![0]),
        Err(PropagationBuildError::EdgeEndpointOutOfRange)
    ));

    let result = PropagationPass::new(1, 3, vec![(0, 1)], vec![0, 2]);
    assert!(result.is_ok());
    if let Ok(mut pass) = result {
        assert_eq!(pass.num_nodes(), 2);
        assert_eq!(pass.update_node(0), Err(PropagationError::RoundNotRunning));
        assert_eq!(pass.start_round(), Ok(()));
        assert_eq!(
            pass.start_round(),
            Err(PropagationError::RoundAlreadyRunning)
        );
        assert_eq!(pass.update_node(2), Err(PropagationError::NodeOutOfRange));
        assert_eq!(pass.update_node(0), Ok(()));
        assert_eq!(
            pass.update_node(0),
            Err(PropagationError::NodeAlreadyUpdated)
        );
        assert_eq!(pass.end_round(), Err(PropagationError::RoundIncomplete));
        assert_eq!(pass.update_node(1), Ok(()));
        assert_eq!(pass.end_round(), Ok(()));
        assert_eq!(pass.iteration(), 1);
        assert_eq!(pass.value(1), Some(1));
        assert_eq!(pass.start_round(), Err(PropagationError::PassTerminated));
        assert_eq!(pass.terminate(), Ok(()));
    }
}

#[test]
fn checked_actuation_rejects_disabled_actions() {
    let mut pass = ActuationPass::new(vec![Some(11), None]);
    assert_eq!(pass.len(), 2);
    assert_eq!(pass.actuate(2), Err(ActuationError::SeatOutOfRange));
    assert_eq!(pass.actuate(1), Err(ActuationError::SeatUnallocated));
    assert_eq!(pass.finish(), Err(ActuationError::PassIncomplete));
    assert_eq!(pass.actuate(0), Ok(()));
    assert_eq!(pass.effect(0), Some(Some(11)));
    assert_eq!(pass.deallocate(0), Err(ActuationError::SeatAlreadyActuated));
    assert_eq!(pass.allocate(1, 22), Ok(()));
    assert_eq!(
        pass.allocate(1, 33),
        Err(ActuationError::SeatAlreadyAllocated)
    );
    assert_eq!(pass.deallocate(1), Ok(()));
    assert!(pass.ready_to_finish());
    assert_eq!(pass.finish(), Ok(()));
    assert!(pass.is_complete());
    assert_eq!(pass.allocate(1, 22), Err(ActuationError::PassComplete));
    assert_eq!(pass.allocation(2), None);
}

#[test]
fn checked_quality_hierarchy_preserves_refinement_guards() {
    let mut hierarchy = QualityHierarchy::new(4, 5);
    assert!(!hierarchy.is_empty());
    assert_eq!(hierarchy.len(), 4);
    assert_eq!(hierarchy.max_level(), 5);

    assert_eq!(hierarchy.set_node_properties(0, 3, 1), Ok(()));
    assert_eq!(hierarchy.set_node_properties(1, 2, 2), Ok(()));
    assert_eq!(hierarchy.set_node_properties(2, 2, 3), Ok(()));
    assert_eq!(hierarchy.set_node_properties(3, 1, 4), Ok(()));
    assert_eq!(hierarchy.add_child(0, 1), Ok(()));
    assert_eq!(hierarchy.add_child(0, 2), Ok(()));
    assert_eq!(hierarchy.add_child(1, 3), Ok(()));

    assert_eq!(hierarchy.parent(0), None);
    assert_eq!(hierarchy.parent(1), Some(0));
    assert_eq!(hierarchy.level(3), Some(1));
    assert_eq!(hierarchy.cost(3), Some(4));
    assert_eq!(hierarchy.edge_count(), 3);
    assert_eq!(hierarchy.edge(0), Some((0, 1)));
    assert_eq!(hierarchy.edge(3), None);
    assert_eq!(
        hierarchy.set_node_properties(0, 4, 1),
        Err(QualityHierarchyError::NodeNotIsolated)
    );
    assert_eq!(
        hierarchy.add_child(0, 1),
        Err(QualityHierarchyError::EdgeAlreadyExists)
    );
    assert_eq!(
        hierarchy.add_child(2, 1),
        Err(QualityHierarchyError::ChildAlreadyParented)
    );
}

#[test]
fn checked_backtracking_pairs_descent_with_inverse_ascent() {
    assert!(matches!(
        BacktrackingTraversal::new(2, 3, 3),
        Err(BacktrackingBuildError::InitialAuxOutOfRange)
    ));

    let traversal = BacktrackingTraversal::new(2, 3, 0);
    assert!(traversal.is_ok());
    if let Ok(mut traversal) = traversal {
        assert_eq!(traversal.ascend(), Err(BacktrackingError::AtRoot));
        assert_eq!(traversal.visit(), Err(BacktrackingError::NotLeaf));
        assert_eq!(traversal.descend(1, 2), Ok(()));
        assert_eq!(traversal.descend(2, 2), Ok(()));
        assert_eq!(traversal.descend(1, 1), Ok(()));
        assert_eq!(traversal.depth(), 3);
        assert_eq!(traversal.auxiliary(), 2);
        assert_eq!(traversal.choice(0), Some(1));
        assert_eq!(traversal.choice(1), Some(2));
        assert_eq!(traversal.choice(2), Some(1));
        assert_eq!(traversal.choice(3), None);
        assert!(traversal.is_leaf());
        assert_eq!(traversal.descend(1, 1), Err(BacktrackingError::AtLeaf));
        assert_eq!(traversal.visit(), Ok(()));
        assert_eq!(traversal.visit(), Err(BacktrackingError::AlreadyVisited));
        assert_eq!(traversal.visited_count(), 1);
        assert_eq!(traversal.ascend(), Ok(()));
        assert_eq!(traversal.ascend(), Ok(()));
        assert_eq!(traversal.ascend(), Ok(()));
        assert_eq!(traversal.auxiliary(), 0);
        assert_eq!(traversal.ascend(), Err(BacktrackingError::AtRoot));
    }
}

#[test]
fn checked_hard_selection_is_stable_and_invalidates_stale_results() {
    assert!(matches!(
        CompetitiveSelectionHard::new(0),
        Err(CompetitiveSelectionError::NoCandidates)
    ));

    let selection = CompetitiveSelectionHard::new(3);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.update_score(0, 5), Ok(()));
        assert_eq!(selection.update_score(1, 7), Ok(()));
        assert_eq!(selection.update_score(2, 7), Ok(()));
        assert_eq!(selection.evaluate(), 1);
        assert_eq!(selection.winner(), Some(1));
        assert_eq!(
            selection.update_score(3, 9),
            Err(CompetitiveSelectionError::CandidateOutOfRange)
        );
        assert_eq!(selection.update_score(0, 8), Ok(()));
        assert_eq!(selection.winner(), None);
        assert_eq!(selection.evaluate(), 0);
    }
}

#[test]
fn checked_hard_exclusive_selection_prevents_candidate_reuse() {
    let selection = CompetitiveSelectionHardExclusive::new(2, 2, 10);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.update_score(0, 0, 9), Ok(()));
        assert_eq!(selection.update_score(0, 1, 8), Ok(()));
        assert_eq!(selection.update_score(1, 0, 10), Ok(()));
        assert_eq!(selection.update_score(1, 1, 7), Ok(()));
        assert_eq!(selection.evaluate(0), Ok(0));
        assert_eq!(selection.evaluate(1), Ok(1));
        assert_eq!(selection.candidate_available(1, 0), Some(false));
        assert_eq!(
            selection.evaluate(1),
            Err(CompetitiveSelectionError::SeatAlreadyAllocated)
        );
        assert_eq!(
            selection.update_score(2, 0, 1),
            Err(CompetitiveSelectionError::SeatOutOfRange)
        );
        assert_eq!(
            selection.update_score(0, 2, 1),
            Err(CompetitiveSelectionError::CandidateOutOfRange)
        );
        assert_eq!(
            selection.update_score(0, 0, 11),
            Err(CompetitiveSelectionError::ScoreOutOfRange)
        );
        assert_eq!(selection.update_score(0, 0, 10), Ok(()));
        assert_eq!(selection.allocation(0), None);
        assert_eq!(selection.allocation(1), None);
    }
}

#[test]
fn checked_soft_selection_exposes_incremental_apportionment() {
    let selection = CompetitiveSelectionSoft::begin(vec![3, 1], 4, 3);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        assert_eq!(selection.assigned_weight(), 2);
        assert!(!selection.is_complete());
        assert_eq!(selection.assign_next(), Ok(0));
        assert_eq!(selection.assign_next(), Ok(0));
        assert!(selection.is_complete());
        assert_eq!(selection.weight(0), Some(3));
        assert_eq!(selection.weight(1), Some(1));
        assert_eq!(
            selection.assign_next(),
            Err(CompetitiveSelectionError::AllocationComplete)
        );
        assert_eq!(selection.update_score(1, 3), Ok(()));
        assert_eq!(selection.assigned_weight(), 2);
        assert!(!selection.is_complete());
    }

    assert!(matches!(
        CompetitiveSelectionSoft::begin(vec![1, 1], 1, 1),
        Err(CompetitiveSelectionError::WeightTotalBelowReservedFloor)
    ));
}

#[test]
fn checked_ranked_selection_is_stable_and_rejects_invalid_replacements() {
    let selection = CompetitiveSelectionRanked::new(vec![5, 5, 4], 2, 5);
    assert!(selection.is_ok());
    if let Ok(mut selection) = selection {
        selection.select();
        assert_eq!(selection.is_selected(0), Some(true));
        assert_eq!(selection.is_selected(1), Some(true));
        assert_eq!(selection.is_selected(2), Some(false));
        assert_eq!(
            selection.update_scores(vec![1, 2]),
            Err(CompetitiveSelectionError::ScoreCountMismatch)
        );
        assert_eq!(
            selection.update_scores(vec![1, 2, 6]),
            Err(CompetitiveSelectionError::ScoreOutOfRange)
        );
        assert_eq!(selection.update_scores(vec![1, 2, 3]), Ok(()));
        assert_eq!(selection.is_selected(0), Some(false));
        selection.select();
        assert_eq!(selection.is_selected(1), Some(true));
        assert_eq!(selection.is_selected(2), Some(true));
    }
}

#[test]
fn checked_convergence_governor_computes_its_own_window_average() {
    assert!(matches!(
        ConvergenceGovernor::new(1, 3, 0, 5),
        Err(ConvergenceBuildError::EmptyWindow)
    ));

    let governor = ConvergenceGovernor::new(10, 30, 3, 50);
    assert!(governor.is_ok());
    if let Ok(mut governor) = governor {
        assert_eq!(governor.state(), ConvergenceState::Active);
        assert_eq!(governor.phase(), ConvergencePhase::Cold);
        assert_eq!(governor.update(51), Err(ConvergenceError::DeltaOutOfRange));
        assert_eq!(governor.update(12), Ok(12));
        assert_eq!(governor.state(), ConvergenceState::Cooling);
        assert_eq!(governor.phase(), ConvergencePhase::Warming);
        assert!(governor.peak_observed());
        assert_eq!(governor.update(2), Ok(7));
        assert_eq!(governor.state(), ConvergenceState::Converged);
        assert_eq!(governor.phase(), ConvergencePhase::Declining);
        assert_eq!(governor.history_len(), 2);
        assert_eq!(governor.history(0), Some(12));
        assert_eq!(governor.history(1), Some(2));
        assert_eq!(governor.history(2), None);
    }
}

#[test]
fn checked_allocation_snapshot_couples_membership_and_budget() {
    let mut snapshot = AllocationSnapshot::new(7, 3);
    assert_eq!(snapshot.accept(0, 3), Ok(()));
    assert_eq!(
        snapshot.accept(0, 1),
        Err(AllocationSnapshotError::NodeAlreadyAccepted)
    );
    assert_eq!(
        snapshot.accept(3, 1),
        Err(AllocationSnapshotError::NodeOutOfRange)
    );
    assert_eq!(
        snapshot.accept(1, 0),
        Err(AllocationSnapshotError::ZeroCost)
    );
    assert_eq!(
        snapshot.accept(1, 5),
        Err(AllocationSnapshotError::InsufficientBudget)
    );
    assert_eq!(snapshot.accept(1, 4), Ok(()));
    assert_eq!(snapshot.total_cost(), 7);
    assert_eq!(snapshot.budget_remaining(), 0);
    assert_eq!(snapshot.accepted(0), Some(0));
    assert_eq!(snapshot.accepted(1), Some(1));
}

#[test]
fn checked_federated_budget_preserves_capacity_conservation() {
    let mut budget = FederatedBudget::new(10, 2);
    assert!(budget.try_delegate(0, 6));
    assert!(!budget.try_delegate(1, 5));
    assert!(budget.try_delegate(1, 4));
    assert!(budget.try_allocate(0, 5));
    assert_eq!(budget.pool_allocated(1), Some(0));
    assert!(!budget.try_allocate(0, 2));
    assert!(budget.try_allocate(1, 2));
    assert_eq!(budget.pool_allocated(0), Some(5));
    assert!(budget.try_release(0, 3));
    assert_eq!(budget.master_allocated(), 10);
    assert_eq!(budget.pool_capacity(1), Some(4));
    assert_eq!(budget.pool_allocated(0), Some(2));
    assert_eq!(budget.pool_allocated(1), Some(2));
}

#[test]
fn checked_bisection_converges_within_its_probe_budget() {
    let bisection = Bisection::new(16, 11);
    assert!(bisection.is_ok());
    if let Ok(mut bisection) = bisection {
        assert!(!bisection.is_converged());
        bisection.converge();
        assert!(bisection.is_converged());
        assert!(bisection.lower() <= 11 && 11 <= bisection.upper());
        assert!(bisection.probes_taken() <= bisection.max_probes());
    }
}

#[test]
fn checked_equivalence_class_bounds_indices_and_union_work() {
    let mut classes = EquivalenceClass::new(3, 2);
    assert_eq!(classes.union(0, 1), Ok(true));
    assert_eq!(classes.equivalent(0, 1), Ok(true));
    assert_eq!(classes.union(0, 1), Ok(false));
    assert_eq!(classes.union(1, 2), Ok(true));
    assert_eq!(classes.unions_performed(), 2);
    assert_eq!(classes.max_unions(), 2);
    assert_eq!(classes.union(0, 2), Ok(false));
    assert_eq!(
        classes.representative(3),
        Err(EquivalenceClassError::ElementOutOfRange)
    );
}

#[test]
fn checked_rate_limit_rolls_windows_on_its_logical_clock() {
    let limit = RateLimit::new(2, 2, 2);
    assert!(limit.is_ok());
    if let Ok(mut limit) = limit {
        assert!(limit.try_acquire());
        assert!(limit.try_acquire());
        assert!(!limit.try_acquire());
        assert_eq!(limit.tick(), Ok(()));
        assert!(!limit.try_acquire());
        assert_eq!(limit.tick(), Ok(()));
        assert!(limit.try_acquire());
        assert_eq!(limit.window_start(), 2);
        assert_eq!(limit.tick(), Err(RateLimitError::ClockExhausted));
    }
}

#[test]
fn checked_reduction_consumes_one_ordered_prefix() {
    let reduction = Reduction::new(vec![2, 3, 5]);
    assert!(reduction.is_ok());
    if let Ok(mut reduction) = reduction {
        assert_eq!(reduction.process_next(), Ok(()));
        assert_eq!(reduction.result(), 2);
        assert_eq!(reduction.process_next(), Ok(()));
        assert_eq!(reduction.process_next(), Ok(()));
        assert!(reduction.is_complete());
        assert_eq!(reduction.result(), 10);
        assert_eq!(reduction.process_next(), Err(ReductionError::Complete));
    }
}

#[test]
fn checked_relationship_graph_keeps_adjacency_in_sync() {
    let mut graph = RelationshipGraph::new(3, 10);
    assert_eq!(graph.add_edge(0, 1, 4), Ok(true));
    assert_eq!(graph.add_edge(0, 1, 4), Ok(false));
    assert_eq!(graph.add_edge(0, 1, 7), Ok(true));
    assert_eq!(graph.add_edge(1, 2, 6), Ok(true));
    assert_eq!(graph.edge_count(), 3);
    assert_eq!(
        graph.add_edge(0, 0, 1),
        Err(RelationshipGraphError::SelfLoop)
    );
    assert_eq!(
        graph.add_edge(0, 3, 1),
        Err(RelationshipGraphError::NodeOutOfRange)
    );
    assert_eq!(
        graph.add_edge(0, 2, 11),
        Err(RelationshipGraphError::WeightOutOfRange)
    );
    assert!(graph.contains(0, 1));
    graph.remove_edges(0, 1);
    assert!(!graph.contains(0, 1));
    assert!(graph.contains(1, 2));
    assert_eq!(graph.edge_count(), 1);
    assert_eq!(graph.edge(0), Some((1, 2, 6)));
}

#[test]
fn checked_sampler_keeps_selection_bounded_and_supported() {
    let mut sampler = Sampler::new(vec![2, 0, 4], 2);
    assert_eq!(sampler.sample(1), Err(SamplerError::OutsideSupport));
    assert_eq!(sampler.sample(0), Ok(()));
    assert_eq!(sampler.sample(0), Err(SamplerError::AlreadySelected));
    assert_eq!(sampler.draw_weighted(2, 3), Ok(true));
    assert_eq!(sampler.sample(1), Err(SamplerError::SampleFull));
    assert!(!sampler.zero(0));

    let mut branches = Sampler::new(vec![2, 0, 4], 3);
    assert_eq!(branches.draw_uniform(0), Ok(true));
    assert_eq!(branches.draw_uniform(0), Ok(false));
    assert!(branches.zero(1));
    assert_eq!(branches.draw_uniform(1), Ok(false));
    assert_eq!(branches.draw_weighted(2, 4), Ok(false));
    assert_eq!(branches.draw_weighted(2, 3), Ok(true));
    assert_eq!(
        branches.draw_weighted(3, 0),
        Err(SamplerError::ItemOutOfRange)
    );
    assert!(!branches.zero(3));
}

#[test]
fn checked_select_then_actuate_uses_one_selection_and_actuation_lifecycle() {
    let composition = SelectThenActuate::new(2, 2);
    assert!(composition.is_ok());
    if let Ok(mut composition) = composition {
        assert_eq!(composition.score(0, 0), Some(0));
        assert_eq!(composition.score(0, 1), Some(0));
        assert_eq!(composition.score(1, 0), Some(0));
        assert_eq!(composition.score(1, 1), Some(0));
        assert_eq!(composition.update_score(0, 0, 2), Ok(()));
        assert_eq!(composition.update_score(0, 1, 5), Ok(()));
        assert_eq!(composition.score(1, 0), Some(0));
        assert_eq!(composition.score(1, 1), Some(0));
        assert_eq!(composition.evaluate(0), Ok(1));
        assert_eq!(composition.allocation(1), None);
        assert_eq!(
            composition.evaluate(0),
            Err(SelectThenActuateError::SeatAlreadyAllocated)
        );
        assert_eq!(composition.actuate(0), Ok(()));
        assert_eq!(composition.is_actuated(0), Some(true));
        assert_eq!(
            composition.update_score(0, 1, 6),
            Err(SelectThenActuateError::EffectAlreadyApplied)
        );
        assert_eq!(composition.finish(), Ok(()));
        assert!(composition.is_complete());
    }
}

#[test]
fn checked_signal_tracks_each_recorded_change_epoch() {
    let signal = Signal::new(0, 3, 2);
    assert!(signal.is_ok());
    if let Ok(mut signal) = signal {
        assert_eq!(signal.set_value(0), Ok(false));
        assert_eq!(signal.set_value(3), Err(SignalError::ValueOutOfRange));
        assert_eq!(signal.set_value(2), Ok(true));
        assert_eq!(signal.is_pending(0), Some(true));
        assert_eq!(signal.notify(0), Ok(()));
        assert_eq!(signal.notify(0), Err(SignalError::ListenerNotPending));
        assert_eq!(signal.is_notified(0), Some(true));
        assert_eq!(signal.set_value(1), Ok(true));
        assert_eq!(signal.change_count(), 2);
        assert_eq!(signal.value(), 1);
        assert_eq!(signal.is_pending(0), Some(true));
        assert_eq!(signal.notify(0), Ok(()));
        assert_eq!(signal.notify(2), Err(SignalError::ListenerOutOfRange));
    }

    let bounded = Signal::with_change_capacity(0, 2, 1, 1);
    assert!(bounded.is_ok());
    if let Ok(mut bounded) = bounded {
        assert_eq!(bounded.set_value(1), Ok(true));
        assert_eq!(
            bounded.set_value(0),
            Err(SignalError::ChangeCapacityExhausted)
        );
        assert_eq!(bounded.change_count(), 1);
        assert_eq!(bounded.value(), 1);
    }
}

#[test]
fn checked_traversal_engine_tracks_budgeted_acceptance() {
    let traversal = TraversalEngine::new(3, 0, 4);
    assert!(traversal.is_ok());
    if let Ok(mut traversal) = traversal {
        assert_eq!(traversal.accepted_cost(), 0);
        assert_eq!(traversal.terminate(), Err(TraversalError::QueueNotEmpty));
        assert_eq!(traversal.visit(0), Ok(()));
        assert!(traversal.is_accepted(0));
        assert_eq!(traversal.accepted_len(), 1);
        assert_eq!(traversal.accepted_cost(), 2);
        assert!(traversal.is_queued(1));
        assert_eq!(traversal.visit(1), Ok(()));
        assert!(traversal.is_accepted(1));
        assert_eq!(traversal.accepted_len(), 2);
        assert_eq!(traversal.accepted_cost(), 4);
        assert_eq!(traversal.visit(2), Ok(()));
        assert!(traversal.is_visited(2));
        assert!(!traversal.is_accepted(2));
        assert_eq!(traversal.accepted_len(), 2);
        assert_eq!(traversal.accepted_cost(), 4);
        assert_eq!(traversal.terminate(), Ok(()));
    }
}

#[test]
fn checked_traversal_skip_removes_only_the_named_frontier_node() {
    let traversal = TraversalEngine::new(4, 0, 8);
    assert!(traversal.is_ok());
    if let Ok(mut traversal) = traversal {
        assert_eq!(traversal.visit(0), Ok(()));
        assert_eq!(traversal.accepted_cost(), 2);
        assert_eq!(traversal.queued_len(), 3);
        assert_eq!(traversal.skip(2), Ok(()));
        assert_eq!(traversal.accepted_cost(), 2);
        assert!(!traversal.is_queued(2));
        assert!(!traversal.is_visited(2));
        assert!(!traversal.is_accepted(2));
        assert!(traversal.is_queued(1));
        assert!(traversal.is_queued(3));
        assert_eq!(traversal.skip(2), Err(TraversalError::NodeNotQueued));
        assert_eq!(traversal.skip(4), Err(TraversalError::NodeOutOfRange));
    }
}

#[test]
fn checked_sequential_execution_preserves_history_position_agreement() {
    let execution = Sequential::new(2, 4, 0);
    assert!(execution.is_ok());
    if let Ok(mut execution) = execution {
        assert!(!execution.complete_step(1));
        assert!(execution.begin_step());
        assert!(!execution.begin_step());
        assert!(!execution.complete_step(4));
        assert!(execution.complete_step(2));
        assert!(execution.begin_step());
        assert!(execution.complete_step(3));
        assert!(execution.is_done());
        assert_eq!(execution.history(0), Some(2));
        assert_eq!(execution.history(1), Some(3));
        assert!(!execution.begin_step());
    }
}

#[test]
fn checked_fork_join_requires_every_worker_before_output() {
    let execution = ForkJoin::new(2, 10, 0);
    assert!(execution.is_ok());
    if let Ok(mut execution) = execution {
        assert!(!execution.barrier());
        assert!(execution.start_worker(0));
        assert!(execution.start_worker(1));
        assert_eq!(execution.worker_state(0), Some(WorkerState::Running));
        assert!(execution.complete_worker(0, 4));
        assert!(!execution.barrier());
        assert!(execution.complete_worker(1, 6));
        assert!(execution.barrier());
        assert_eq!(execution.phase(), ForkJoinPhase::Join);
        assert!(execution.produce_output());
        assert_eq!(execution.output(0), Some(4));
        assert_eq!(execution.output(1), Some(6));
        assert_eq!(execution.phase(), ForkJoinPhase::Done);
    }
}

#[test]
fn checked_step_graph_enforces_predecessor_completion() {
    assert!(matches!(
        StepGraph::new(2, vec![(0, 2)]),
        Err(StepGraphBuildError::EdgeEndpointOutOfRange)
    ));
    assert!(matches!(
        StepGraph::new(2, vec![(0, 1), (0, 1)]),
        Err(StepGraphBuildError::DuplicateEdge)
    ));

    let graph = StepGraph::new(2, vec![(0, 1)]);
    assert!(graph.is_ok());
    if let Ok(mut graph) = graph {
        assert_eq!(graph.state(0), Some(StepState::Ready));
        assert_eq!(graph.state(1), Some(StepState::NotReady));
        assert!(!graph.start(1));
        assert!(graph.start(0));
        assert!(graph.complete(0));
        assert!(graph.become_ready(1));
        assert!(graph.start(1));
        assert!(graph.complete(1));
        assert!(graph.is_done());
    }
}

#[test]
fn checked_stream_graph_preserves_fifo_and_backpressure() {
    let stream = StreamGraph::new(3, 1, 2, 10);
    assert!(stream.is_ok());
    if let Ok(mut stream) = stream {
        assert!(stream.has_enabled_action());
        assert_eq!(stream.consume(), None);
        assert!(stream.ingest(3));
        assert_eq!(
            stream.ingested(),
            stream.emitted()
                + stream.first_queue_len()
                + stream.second_queue_len()
                + stream.third_queue_len()
        );
        assert!(!stream.ingest(5));
        assert!(stream.advance_first());
        assert!(stream.ingest(5));
        assert_eq!(stream.consume(), Some(3));
        assert!(stream.advance_first());
        assert_eq!(stream.consume(), Some(5));
        assert!(stream.is_done());
        assert!(stream.has_enabled_action());
    }
}

#[test]
fn checked_four_stage_stream_graph_uses_the_second_transfer() {
    let stream = StreamGraph::new(4, 1, 2, 10);
    assert!(stream.is_ok());
    if let Ok(mut stream) = stream {
        assert!(stream.has_enabled_action());
        assert!(!stream.advance_second());
        assert!(stream.ingest(3));
        assert!(stream.advance_first());
        assert_eq!(stream.second_queue_len(), 1);
        assert!(stream.advance_second());
        assert_eq!(stream.second_queue_len(), 0);
        assert_eq!(stream.third_queue_len(), 1);
        assert_eq!(stream.consume(), Some(3));
        assert!(stream.ingest(5));
        assert!(stream.advance_first());
        assert!(stream.advance_second());
        assert_eq!(stream.consume(), Some(5));
        assert!(stream.is_done());
        assert!(stream.has_enabled_action());
    }
}

#[test]
fn connective_accumulator_carries_one_partial_result() {
    let mut input = Accumulator::new(vec![4u64, 5]);
    assert_eq!(input.accumulated_len(), 0);
    assert_eq!(input.pending_len(), 2);
    assert_eq!(input.checked_len(), Some(2));
    assert!(!input.is_complete());
    assert_eq!(input.pending(0), Some(4));
    assert_eq!(input.pending(1), Some(5));
    assert_eq!(input.advance(), Some(4));
    assert_eq!(input.accumulated(0), Some(4));
    assert_eq!(input.advance(), Some(5));
    assert!(input.is_complete());
    assert_eq!(input.advance(), None);

    let mut output = Accumulator::from_accumulated(Vec::<u64>::new());
    assert_eq!(output.try_append(4), Ok(()));
    assert_eq!(output.try_append(5), Ok(()));
    assert_eq!(output.try_append(6), Ok(()));
    assert_eq!(output.accumulated_len(), 3);
    assert_eq!(output.checked_len(), Some(3));
    assert_eq!(output.accumulated(0), Some(4));
    assert_eq!(output.accumulated(2), Some(6));
}

#[test]
fn connective_buffer_is_bounded_fifo() {
    let mut buffer = Buffer::new(2);
    assert_eq!(buffer.push(1), Ok(()));
    assert_eq!(buffer.push(2), Ok(()));
    assert_eq!(buffer.push(3), Err(3));
    assert!(buffer.is_full());
    assert_eq!(buffer.pop(), Some(1));
    assert_eq!(buffer.pop(), Some(2));
    assert_eq!(buffer.pop(), None);

    let mut distinct = Buffer::<u64>::new(2);
    assert!(distinct.push_unique(7));
    assert!(!distinct.push_unique(7));
    assert!(distinct.contains(7));
    assert!(distinct.remove(7));
    assert!(!distinct.contains(7));

    let mut ordered = Buffer::<u64>::new(4);
    assert!(ordered.push_unique(1));
    assert!(ordered.push_unique(2));
    assert!(ordered.push_unique(3));
    assert!(ordered.remove(2));
    assert_eq!(ordered.pop(), Some(1));
    assert_eq!(ordered.pop(), Some(3));
    assert_eq!(ordered.pop(), None);
}

#[test]
fn connective_counter_marker_projection_and_order_are_reusable() {
    let mut counter = Counter::new(0);
    assert!(!counter.try_decrement());
    assert!(counter.try_increment());
    assert_eq!(counter.value(), 1);
    assert!(counter.try_decrement());
    assert_eq!(counter.value(), 0);

    let mut marker = Marker::new(false);
    assert!(marker.set());
    assert!(!marker.set());
    assert!(marker.clear());
    assert!(!marker.clear());

    assert!(projection_consistent(true, true));
    assert!(!projection_consistent(true, false));
    assert!(strictly_before(1, 2));
    assert!(!strictly_before(2, 2));
}

#[test]
fn public_types_support_standard_debugging_and_thread_transfer() {
    fn assert_common<T: core::fmt::Debug + Send + Sync + 'static>() {}
    fn assert_error<T: std::error::Error + Send + Sync + 'static>() {}

    assert_common::<Budget>();
    assert_common::<ResourceRegistry>();
    assert_common::<AuditRecord>();
    assert_common::<AuditSink>();
    assert_common::<Cursor>();
    assert_common::<PropagationPass>();
    assert_common::<ActuationPass>();
    assert_common::<QualityHierarchy>();
    assert_common::<BacktrackingTraversal>();
    assert_common::<CompetitiveSelectionHard>();
    assert_common::<CompetitiveSelectionHardExclusive>();
    assert_common::<CompetitiveSelectionSoft>();
    assert_common::<CompetitiveSelectionRanked>();
    assert_common::<ConvergenceGovernor>();
    assert_common::<AllocationSnapshot>();
    assert_common::<FederatedBudget>();
    assert_common::<Bisection>();
    assert_common::<EquivalenceClass>();
    assert_common::<RateLimit>();
    assert_common::<Reduction>();
    assert_common::<RelationshipGraph>();
    assert_common::<Sampler>();
    assert_common::<SelectThenActuate>();
    assert_common::<Signal>();
    assert_common::<TraversalEngine>();
    assert_common::<Sequential>();
    assert_common::<ForkJoin>();
    assert_common::<StepGraph>();
    assert_common::<StreamGraph>();
    assert_common::<Accumulator<u64>>();
    assert_common::<Buffer<u64>>();
    assert_common::<Counter>();
    assert_common::<Marker>();
    assert_common::<automation_structures::PropagationRound>();
    assert_common::<ConvergencePhase>();
    assert_common::<ConvergenceState>();
    assert_common::<ForkJoinPhase>();
    assert_common::<WorkerState>();
    assert_common::<StepState>();

    assert_error::<BudgetError>();
    assert_error::<CursorError>();
    assert_error::<PropagationBuildError>();
    assert_error::<PropagationError>();
    assert_error::<ActuationError>();
    assert_error::<QualityHierarchyError>();
    assert_error::<BacktrackingBuildError>();
    assert_error::<BacktrackingError>();
    assert_error::<CompetitiveSelectionError>();
    assert_error::<ConvergenceBuildError>();
    assert_error::<ConvergenceError>();
    assert_error::<AllocationSnapshotError>();
    assert_error::<automation_structures::BisectionBuildError>();
    assert_error::<automation_structures::BisectionError>();
    assert_error::<EquivalenceClassError>();
    assert_error::<automation_structures::RateLimitBuildError>();
    assert_error::<RateLimitError>();
    assert_error::<automation_structures::ReductionBuildError>();
    assert_error::<ReductionError>();
    assert_error::<RelationshipGraphError>();
    assert_error::<SamplerError>();
    assert_error::<SelectThenActuateBuildError>();
    assert_error::<SelectThenActuateError>();
    assert_error::<automation_structures::SignalBuildError>();
    assert_error::<SignalError>();
    assert_error::<automation_structures::TraversalBuildError>();
    assert_error::<TraversalError>();
    assert_error::<automation_structures::SequentialBuildError>();
    assert_error::<automation_structures::ForkJoinBuildError>();
    assert_error::<StepGraphBuildError>();
    assert_error::<automation_structures::StreamGraphBuildError>();
}

#[test]
fn checked_constructors_reject_invalid_configurations() {
    assert!(matches!(
        Bisection::new(1, 0),
        Err(automation_structures::BisectionBuildError::DomainTooSmall)
    ));
    assert!(matches!(
        Bisection::new(2, 0),
        Err(automation_structures::BisectionBuildError::ThresholdOutOfRange)
    ));
    assert!(matches!(
        RateLimit::new(0, 1, 1),
        Err(automation_structures::RateLimitBuildError::ZeroLimit)
    ));
    assert!(matches!(
        Reduction::new(vec![1_000_000_001]),
        Err(automation_structures::ReductionBuildError::ValueOutOfRange)
    ));
    assert!(matches!(
        Signal::new(1, 1, 0),
        Err(automation_structures::SignalBuildError::InitialValueOutOfRange)
    ));
    assert!(matches!(
        SelectThenActuate::new(1, 0),
        Err(SelectThenActuateBuildError::NoCandidates)
    ));
    assert!(matches!(
        TraversalEngine::new(0, 0, 0),
        Err(automation_structures::TraversalBuildError::NoNodes)
    ));
    assert!(matches!(
        TraversalEngine::new(1, 1, 0),
        Err(automation_structures::TraversalBuildError::RootOutOfRange)
    ));
    assert!(matches!(
        Sequential::new(0, 1, 0),
        Err(automation_structures::SequentialBuildError::NoSteps)
    ));
    assert!(matches!(
        Sequential::new(1, 0, 0),
        Err(automation_structures::SequentialBuildError::EmptyValueDomain)
    ));
    assert!(matches!(
        ForkJoin::new(1, 0, 0),
        Err(automation_structures::ForkJoinBuildError::EmptyValueDomain)
    ));
    assert!(matches!(
        StreamGraph::new(2, 1, 1, 1),
        Err(automation_structures::StreamGraphBuildError::UnsupportedChainLength)
    ));
    assert!(matches!(
        StreamGraph::new(3, 0, 1, 1),
        Err(automation_structures::StreamGraphBuildError::ZeroCapacity)
    ));
    assert!(matches!(
        StreamGraph::new(3, 1, 1, 0),
        Err(automation_structures::StreamGraphBuildError::EmptyRecordDomain)
    ));
}
