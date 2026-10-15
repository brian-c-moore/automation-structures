//! External Verus consumer used by the cross-crate proof API gate.

use automation_structures::Buffer;
use automation_structures::primitives::resource_registry;
use vstd::prelude::*;

verus! {

pub fn checked_actuation_effect_slice_exports_its_owner_invariant(
    pass: &automation_structures::ActuationPass)
{
    let _effects = pass.effects();
    assert(pass.state_spec().invariant());
}

pub fn select_then_actuate_borrows_one_owner_and_preserves_other_seats() {
    use automation_structures::compositions::select_then_actuate::SelectThenActuate;
    let mut pass = SelectThenActuate::new(2, 2);
    pass.update_score(1, 0, 7);
    pass.evaluate(1);
    proof {
        pass.expose();
        assert(pass.selections@[1].scores@[0] == 7);
        assert(pass.selections@[1].scores@[1] == 0);
        assert(pass.selections@[1].winner_optimality());
        if let Some(winner) = pass.selections@[1].allocation {
            assert(winner < 2);
            assert(pass.selections@[1].scores@[0]
                <= pass.selections@[1].scores@[winner as int]);
            if winner == 1 { assert(false); }
        }
        assert(pass.selections@[1].allocation == Some(0usize));
    }
    assert(pass.actuation.allocation@[1] == Some(0u64));
    let ghost other = pass.selections@[1];
    pass.update_score(0, 1, 5);
    assert(pass.selections@[1] == other);
    assert(pass.actuation.allocation@[1] == Some(0u64));
    pass.evaluate(0);
    proof {
        pass.expose();
        assert(pass.selections@[0].scores@[0] == 0);
        assert(pass.selections@[0].scores@[1] == 5);
        assert(pass.selections@[0].winner_optimality());
        if let Some(winner) = pass.selections@[0].allocation {
            assert(winner < 2);
            assert(pass.selections@[0].scores@[1]
                <= pass.selections@[0].scores@[winner as int]);
            if winner == 0 { assert(false); }
        }
        assert(pass.selections@[0].allocation == Some(1usize));
    }
    assert(pass.actuation.allocation@[0] == Some(1u64));
    assert(pass.selections@[1] == other);
    pass.update_score(0, 0, 9);
    assert(pass.actuation.allocation@[0] is None);
    assert(pass.actuation.allocation@[1] == Some(0u64));
    assert(pass.actuation.effects@ == seq![None, None]);
    assert(pass.selections@[1] == other);
    pass.evaluate(0);
    proof {
        pass.expose();
        assert(pass.selections@[0].scores@[0] == 9);
        assert(pass.selections@[0].scores@[1] == 5);
        assert(pass.selections@[0].winner_optimality());
        if let Some(winner) = pass.selections@[0].allocation {
            assert(winner < 2);
            assert(pass.selections@[0].scores@[0]
                <= pass.selections@[0].scores@[winner as int]);
            if winner == 1 { assert(false); }
        }
        assert(pass.selections@[0].allocation == Some(0usize));
    }
    assert(pass.actuation.allocation@[0] == Some(0u64));
    assert(pass.selections@[1] == other);
    pass.actuate(0);
    assert(pass.actuation.effects@ == seq![Some(0u64), None]);
    assert(pass.selections@[1] == other);
    pass.actuate(1);
    assert(pass.actuation.effects@ == seq![Some(0u64), Some(0u64)]);
    pass.finish();
    assert(pass.actuation.complete);
    assert(pass.selections@[1] == other);
    assert(pass.inv());
}

pub fn checked_actuation_initial_state_is_the_supplied_allocation(allocation: Vec<Option<u64>>) {
    let ghost supplied = allocation@;
    let _pass = automation_structures::ActuationPass::new(allocation);
    assert(_pass.state_spec().num_seats == supplied.len()) by {
        assert(_pass.state_spec().type_invariant());
    }
    assert(_pass.state_spec().allocation@ == supplied);
    assert(_pass.state_spec().effects@.len() == supplied.len()) by {
        assert(_pass.state_spec().type_invariant());
    }
    assert(forall|i: int| 0 <= i < supplied.len()
        ==> #[trigger] _pass.state_spec().effects@[i] is None);
    assert(!_pass.state_spec().complete);
    assert(_pass.state_spec().invariant()) by {
        assert(_pass.state_spec().type_invariant());
        assert(_pass.state_spec().effect_fidelity());
        assert(_pass.state_spec().actuation_scope());
        assert(_pass.state_spec().pass_completeness());
    }
}

/// A consumer proof over two projected records; it retains no owner or runtime state.
pub proof fn actuation_allocation_revision_preserves_fidelity(
    before: automation_structures::primitives::actuation_pass::ActuationPass,
    after: automation_structures::primitives::actuation_pass::ActuationPass,
    seat: usize, value: Option<u64>)
    requires
        before.invariant(), seat < before.num_seats,
        before.effects@[seat as int] is None,
        after.num_seats == before.num_seats,
        after.effects@ == before.effects@,
        after.allocation@ == before.allocation@.update(seat as int, value),
    ensures after.type_invariant(), after.effect_fidelity(), after.actuation_scope(),
{
    assert forall|i: int| 0 <= i < after.effects@.len() && after.effects@[i] is Some
        implies after.effects@[i] == after.allocation@[i] by {
        if i == seat as int {
            assert(after.effects@[i] is None);
        } else {
            assert(after.effects@[i] == before.effects@[i]);
            assert(after.allocation@[i] == before.allocation@[i]);
        }
    }
}

/// The effect update uses the resource from the same supplied pre-state record.
pub proof fn actuation_effect_revision_preserves_fidelity(
    before: automation_structures::primitives::actuation_pass::ActuationPass,
    after: automation_structures::primitives::actuation_pass::ActuationPass,
    seat: usize)
    requires
        before.invariant(), seat < before.num_seats,
        after.num_seats == before.num_seats,
        after.allocation@ == before.allocation@,
        after.effects@ == before.effects@.update(seat as int, before.allocation@[seat as int]),
    ensures after.type_invariant(), after.effect_fidelity(), after.actuation_scope(),
{
    assert forall|i: int| 0 <= i < after.effects@.len() && after.effects@[i] is Some
        implies after.effects@[i] == after.allocation@[i] by {
        if i == seat as int {
            assert(after.effects@[i] == before.allocation@[i]);
        } else {
            assert(after.effects@[i] == before.effects@[i]);
        }
        assert(after.allocation@[i] == before.allocation@[i]);
    }
}

/// Readiness and fidelity pair the two views, including an empty seat universe.
pub proof fn actuation_ready_views_agree(
    state: automation_structures::primitives::actuation_pass::ActuationPass)
    requires state.invariant(), state.ready_to_finish(),
    ensures state.allocation@ == state.effects@,
{
    assert forall|i: int| 0 <= i < state.allocation@.len()
        implies state.allocation@[i] == state.effects@[i] by {
        if state.allocation@[i] is Some {
            assert(state.effects@[i] is Some);
        } else if state.effects@[i] is Some {
            assert(state.effects@[i] == state.allocation@[i]);
        }
    }
    assert(state.allocation@ =~= state.effects@);
}

pub fn checked_actuation_observations_borrow_the_actual_owner(
    pass: &automation_structures::ActuationPass, seat: usize)
{
    let _allocations = pass.allocations();
    assert(_allocations@ == pass.state_spec().allocation@);
    assert(pass.state_spec().invariant());
    let _effects = pass.effects();
    assert(_effects@ == pass.state_spec().effects@);
    let _count = pass.len(); assert(_count == pass.state_spec().num_seats);
    let _empty = pass.is_empty(); assert(_empty == (_count == 0));
    let _complete = pass.is_complete(); assert(_complete == pass.state_spec().complete);
    let _allocation = pass.allocation(seat);
    assert(_allocation == if seat < _count { Some(_allocations@[seat as int]) } else { None });
    let _effect = pass.effect(seat);
    assert(_effect == if seat < _count { Some(_effects@[seat as int]) } else { None });
    let _ready = pass.ready_to_finish(); assert(_ready == pass.state_spec().ready_to_finish());
}

pub fn checked_actuation_allocation_exports_its_exact_commit_and_refusal(
    mut pass: automation_structures::ActuationPass, seat: usize, resource: u64)
{
    let _allocations = pass.allocations();
    let ghost before = pass;
    proof { assert(before.state_spec().invariant()); }
    let _result = pass.allocate(seat, resource);
    proof {
        use automation_structures::ActuationError;
        assert(_result == if seat >= before.state_spec().num_seats {
            Err(ActuationError::SeatOutOfRange)
        } else if before.state_spec().complete {
            Err(ActuationError::PassComplete)
        } else if before.state_spec().allocation@[seat as int] is Some {
            Err(ActuationError::SeatAlreadyAllocated)
        } else { Ok(()) });
        assert(pass.state_spec().num_seats == before.state_spec().num_seats) by {
            assert(pass.state_spec().effects@.len() == before.state_spec().effects@.len());
        }
        assert(pass.state_spec().effects@ == before.state_spec().effects@);
        if _result is Err { assert(pass == before); }
        if _result is Ok {
            assert(pass.state_spec().allocation@
                == before.state_spec().allocation@.update(seat as int, Some(resource)));
            assert(before.state_spec().effects@[seat as int] is None) by {
                if before.state_spec().effects@[seat as int] is Some {
                    assert(before.state_spec().effects@[seat as int]
                        == before.state_spec().allocation@[seat as int]);
                }
            }
            actuation_allocation_revision_preserves_fidelity(
                before.state_spec(), pass.state_spec(), seat, Some(resource));
        }
        assert(pass.state_spec().complete == before.state_spec().complete) by {
            if _result is Ok && pass.state_spec().complete {
                assert(pass.state_spec().ready_to_finish());
                assert(pass.state_spec().allocation@[seat as int] is Some);
                assert(pass.state_spec().effects@[seat as int] is None);
                assert(false);
            }
        }
        assert(pass.state_spec().invariant()) by {
            assert(pass.state_spec().pass_completeness());
        }
    }
}

pub fn checked_actuation_deallocation_exports_its_exact_commit_and_refusal(
    mut pass: automation_structures::ActuationPass, seat: usize)
{
    let _allocations = pass.allocations();
    let ghost before = pass;
    proof { assert(before.state_spec().invariant()); }
    let _result = pass.deallocate(seat);
    proof {
        use automation_structures::ActuationError;
        assert(_result == if seat >= before.state_spec().num_seats {
            Err(ActuationError::SeatOutOfRange)
        } else if before.state_spec().complete {
            Err(ActuationError::PassComplete)
        } else if before.state_spec().allocation@[seat as int] is None {
            Err(ActuationError::SeatUnallocated)
        } else if before.state_spec().effects@[seat as int] is Some {
            Err(ActuationError::SeatAlreadyActuated)
        } else { Ok(()) });
        assert(pass.state_spec().num_seats == before.state_spec().num_seats) by {
            assert(pass.state_spec().effects@.len() == before.state_spec().effects@.len());
        }
        assert(pass.state_spec().effects@ == before.state_spec().effects@);
        assert(pass.state_spec().complete == before.state_spec().complete);
        if _result is Err { assert(pass == before); }
        if _result is Ok {
            assert(pass.state_spec().allocation@
                == before.state_spec().allocation@.update(seat as int, None));
            actuation_allocation_revision_preserves_fidelity(
                before.state_spec(), pass.state_spec(), seat, None);
        }
        assert(pass.state_spec().invariant()) by {
            assert(pass.state_spec().pass_completeness());
        }
    }
}

pub fn checked_actuation_effect_exports_the_live_resource_and_refusal(
    mut pass: automation_structures::ActuationPass, seat: usize)
{
    let _allocations = pass.allocations();
    let ghost before = pass;
    proof { assert(before.state_spec().invariant()); }
    let _result = pass.actuate(seat);
    proof {
        use automation_structures::ActuationError;
        assert(_result == if seat >= before.state_spec().num_seats {
            Err(ActuationError::SeatOutOfRange)
        } else if before.state_spec().complete {
            Err(ActuationError::PassComplete)
        } else if before.state_spec().allocation@[seat as int] is None {
            Err(ActuationError::SeatUnallocated)
        } else if before.state_spec().effects@[seat as int] is Some {
            Err(ActuationError::SeatAlreadyActuated)
        } else { Ok(()) });
        assert(pass.state_spec().num_seats == before.state_spec().num_seats) by {
            assert(pass.state_spec().allocation@.len() == before.state_spec().allocation@.len());
        }
        assert(pass.state_spec().allocation@ == before.state_spec().allocation@);
        assert(pass.state_spec().complete == before.state_spec().complete);
        if _result is Err { assert(pass == before); }
        if _result is Ok {
            assert(pass.state_spec().effects@
                == before.state_spec().effects@.update(seat as int, before.state_spec().allocation@[seat as int]));
            actuation_effect_revision_preserves_fidelity(before.state_spec(), pass.state_spec(), seat);
        }
        assert(pass.state_spec().invariant()) by {
            assert(pass.state_spec().pass_completeness());
        }
    }
}

pub fn checked_actuation_closure_exports_completeness_and_refusal(
    mut pass: automation_structures::ActuationPass)
{
    let _allocations = pass.allocations();
    let ghost before = pass;
    proof { assert(before.state_spec().invariant()); }
    let _result = pass.finish();
    proof {
        use automation_structures::ActuationError;
        assert(_result == if before.state_spec().complete {
            Err(ActuationError::PassComplete)
        } else if !before.state_spec().ready_to_finish() {
            Err(ActuationError::PassIncomplete)
        } else { Ok(()) });
        if _result is Err { assert(pass == before); }
        if _result is Ok { assert(pass.state_spec().complete); }
        assert(pass.state_spec().num_seats == before.state_spec().num_seats) by {
            assert(pass.state_spec().allocation@.len() == before.state_spec().allocation@.len());
        }
        assert(pass.state_spec().invariant()) by {
            assert(pass.state_spec().type_invariant());
            assert(pass.state_spec().effect_fidelity());
            assert(pass.state_spec().actuation_scope());
            assert(pass.state_spec().pass_completeness());
        }
        if _result is Ok {
            actuation_ready_views_agree(before.state_spec());
            actuation_ready_views_agree(pass.state_spec());
        }
        assert(pass.state_spec().allocation@ == before.state_spec().allocation@);
        assert(pass.state_spec().effects@ == before.state_spec().effects@);
    }
}

pub fn checked_default_linear_stream_exports_fifo_and_refusal_frames() {
    use automation_structures::StreamGraph;
    let _created = StreamGraph::new(3, 1, 1, 4);
    assert(_created is Ok);
    let mut graph = match _created { Ok(graph) => graph, Err(_) => return };
    let _empty = graph.consume(); assert(_empty == None);
    let _accepted = graph.ingest(3); assert(_accepted);
    let _refused = graph.ingest(2); assert(!_refused);
    assert(graph.first_queue_spec() == seq![3u64]);
    let _unsupported = graph.advance_second(); assert(!_unsupported);
    assert(graph.first_queue_spec() == seq![3u64]);
    let _moved = graph.advance_first(); assert(_moved);
    assert(graph.first_queue_spec().len() == 0);
    assert(graph.second_queue_spec() == seq![3u64]);
    let _value = graph.consume(); assert(_value == Some(3u64));
    let _complete = graph.is_done(); assert(_complete);
    let _enabled = graph.has_enabled_action(); assert(_enabled);
    let _count = graph.emitted(); assert(_count == 1);
    let _input = graph.ingested(); assert(_input == 1);
    let _empty = graph.consume(); assert(_empty == None);
    assert(graph.config_spec() == (3usize, 1usize, 1usize, 4u64));
    assert(graph.emitted_spec() == 1);
}

pub fn checked_linear_storage_profiles_export_the_same_fifo_contracts<
    S: automation_structures::connectives::buffer::BufferLayout<u64>>()
{
    use automation_structures::StreamGraph;
    let mut graph = match StreamGraph::<S>::try_with_storage(4, 2, 2, 10) {
        Ok(graph) => graph,
        Err(_error) => { assert(_error == automation_structures::StreamGraphBuildError::StorageUnavailable); return; },
    };
    let _first = graph.ingest(3); assert(_first);
    let _second = graph.ingest(5); assert(_second);
    let _refused = graph.ingest(7); assert(!_refused);
    assert(graph.first_queue_spec() == seq![3u64, 5u64]);
    let _first = graph.advance_first(); assert(_first);
    let _second = graph.advance_first(); assert(_second);
    assert(graph.second_queue_spec() == seq![3u64, 5u64]);
    let _empty = graph.advance_first(); assert(!_empty);
    let _first = graph.advance_second(); assert(_first);
    let _second = graph.advance_second(); assert(_second);
    assert(graph.third_queue_spec() == seq![3u64, 5u64]);
    let _first = graph.consume(); assert(_first == Some(3u64));
    assert(graph.third_queue_spec() == seq![5u64]);
    assert(graph.emitted_spec() == 1 && graph.ingested_spec() == 2);
    let _premature = graph.is_done(); assert(!_premature);
    let _second = graph.consume(); assert(_second == Some(5u64));
    let _complete = graph.is_done(); assert(_complete);
    let _empty = graph.consume(); assert(_empty == None);
    let _stages = graph.chain_length(); assert(_stages == 4);
    let _capacity = graph.capacity(); assert(_capacity == 2);
    let _bound = graph.max_inputs(); assert(_bound == 2);
    let _domain = graph.record_domain_size(); assert(_domain == 10);
    let _first = graph.first_queue_len(); assert(_first == 0);
    let _second = graph.second_queue_len(); assert(_second == 0);
    let _third = graph.third_queue_len(); assert(_third == 0);
    let _input = graph.ingested();
    assert(graph.ingested_spec() == graph.emitted_spec());
}

pub fn fifo_linear_stream_retains_the_same_transfer_and_frame_contracts() {
    use automation_structures::connectives::buffer::{Buffer, FifoStorage};
    use automation_structures::modalities::stream_graph::StreamGraph;
    let q1 = match Buffer::<u64, FifoStorage>::try_with_storage(3) {
        Ok(queue) => queue, Err(_) => return,
    };
    let q2 = match Buffer::<u64, FifoStorage>::try_with_storage(3) {
        Ok(queue) => queue, Err(_) => return,
    };
    let q3 = match Buffer::<u64, FifoStorage>::try_with_storage(3) {
        Ok(queue) => queue, Err(_) => return,
    };
    let mut graph = StreamGraph::<FifoStorage>::with_buffers(4, q1, q2, q3, 2, 10);
    let _first = graph.source_ingest(3); assert(_first);
    let _second = graph.source_ingest(5); assert(_second);
    let _exhausted = graph.source_ingest(7); assert(!_exhausted);
    assert(graph.q1.values@ == seq![3u64, 5u64]);
    let _first = graph.middle2_fire(); assert(_first);
    let _second = graph.middle2_fire(); assert(_second);
    let _empty = graph.middle2_fire(); assert(!_empty);
    assert(graph.q1.values@.len() == 0);
    assert(graph.q2.values@ == seq![3u64, 5u64]);
    let _first = graph.middle3_fire(); assert(_first);
    let _second = graph.middle3_fire(); assert(_second);
    assert(graph.q2.values@.len() == 0);
    assert(graph.q3.values@ == seq![3u64, 5u64]);
    let _consumed = graph.sink_consume(); assert(_consumed);
    assert(graph.q3.values@ == seq![5u64]);
    assert(graph.emitted.value_spec() == 1);
    let _premature = graph.done_stuttering(); assert(!_premature);
    let _consumed = graph.sink_consume(); assert(_consumed);
    assert(graph.q3.values@.len() == 0);
    assert(graph.ingested.value_spec() == graph.emitted.value_spec());
    let _complete = graph.done_stuttering(); assert(_complete);
    let _enabled = graph.some_action_enabled_exec(); assert(_enabled);
    let _empty = graph.sink_consume(); assert(!_empty);
    assert(graph.inv());
}

/// The checked constructor and all runtime observations expose the existing empty ledger.
pub fn checked_budget_initial_observations(capacity: u64) {
    let budget = automation_structures::Budget::new(capacity);
    assert(budget.capacity_spec() == capacity);
    assert(budget.allocated_spec() == 0);
    assert(budget.reserved_spec() == 0);
    assert(budget.pending_eviction_spec() == 0);
    assert(budget.safety_invariant());
    proof { budget.expose_safety(); }
    assert(budget.used_spec() == 0);
    let ceiling = budget.capacity(); let allocated = budget.allocated();
    let reserved = budget.reserved(); let pending = budget.pending_eviction();
    let available = budget.available();
    assert(ceiling == capacity);
    assert(allocated == 0);
    assert(reserved == 0);
    assert(pending == 0);
    assert(available == capacity);
    let _ = (ceiling, allocated, reserved, pending, available);
}

/// An arbitrary valid checked owner exports the existing safety and exact observation relation.
pub proof fn checked_budget_safety_contract(tracked owner: &automation_structures::Budget) {
    owner.expose_safety();
    assert(owner.safety_invariant());
    assert(owner.used_spec() == owner.allocated_spec() as int + owner.reserved_spec() as int
        + owner.pending_eviction_spec() as int);
    assert(automation_structures::primitives::budget::budget_safety(owner.capacity_spec() as nat,
        owner.allocated_spec() as nat, owner.reserved_spec() as nat, owner.pending_eviction_spec() as nat));
}

/// Allocation exports its decision, credit, all other terms and complete refusal frame.
pub fn checked_budget_allocate_contract(owner: &mut automation_structures::Budget, amount: u64) {
    let ghost before = *owner;
    let accepted = owner.try_allocate(amount);
    assert(accepted == (before.used_spec() + amount as int <= before.capacity_spec() as int));
    assert(owner.capacity_spec() == before.capacity_spec());
    assert(owner.reserved_spec() == before.reserved_spec());
    assert(owner.pending_eviction_spec() == before.pending_eviction_spec());
    assert(owner.safety_invariant());
    if accepted {
        assert(owner.allocated_spec() as int == before.allocated_spec() as int + amount as int);
    } else { assert(*owner == before); }
    let _ = accepted;
}

/// Reservation exports its distinct credit and does not alter committed or evicting terms.
pub fn checked_budget_reserve_contract(owner: &mut automation_structures::Budget, amount: u64) {
    let ghost before = *owner;
    let accepted = owner.try_reserve(amount);
    assert(accepted == (before.used_spec() + amount as int <= before.capacity_spec() as int));
    assert(owner.capacity_spec() == before.capacity_spec());
    assert(owner.allocated_spec() == before.allocated_spec());
    assert(owner.pending_eviction_spec() == before.pending_eviction_spec());
    assert(owner.safety_invariant());
    if accepted {
        assert(owner.reserved_spec() as int == before.reserved_spec() as int + amount as int);
    } else { assert(*owner == before); }
    let _ = accepted;
}

/// Reservation commit exports both sides of the transfer and its exact error decision.
pub fn checked_budget_commit_contract(owner: &mut automation_structures::Budget, amount: u64) {
    let ghost before = *owner;
    let result = owner.commit_reservation(amount);
    assert(result is Ok <==> amount <= before.reserved_spec());
    assert(owner.capacity_spec() == before.capacity_spec());
    assert(owner.pending_eviction_spec() == before.pending_eviction_spec());
    assert(owner.safety_invariant());
    match result {
        Ok(()) => {
            assert(owner.allocated_spec() as int == before.allocated_spec() as int + amount as int);
            assert(owner.reserved_spec() as int == before.reserved_spec() as int - amount as int);
        },
        Err(error) => {
            assert(error == automation_structures::BudgetError::AmountExceedsReservation);
            assert(*owner == before); let _ = error;
        },
    }
}

/// Release exports its debit, exact refusal and every unaffected ledger term.
pub fn checked_budget_release_contract(owner: &mut automation_structures::Budget, amount: u64) {
    let ghost before = *owner;
    let result = owner.release(amount);
    assert(result is Ok <==> amount <= before.allocated_spec());
    assert(owner.capacity_spec() == before.capacity_spec());
    assert(owner.reserved_spec() == before.reserved_spec());
    assert(owner.pending_eviction_spec() == before.pending_eviction_spec());
    assert(owner.safety_invariant());
    match result {
        Ok(()) => { assert(owner.allocated_spec() as int == before.allocated_spec() as int - amount as int); },
        Err(error) => {
            assert(error == automation_structures::BudgetError::AmountExceedsAllocation);
            assert(*owner == before); let _ = error;
        },
    }
}

/// Eviction marking exports allocated debit and pending credit as one owner action.
pub fn checked_budget_mark_contract(owner: &mut automation_structures::Budget, amount: u64) {
    let ghost before = *owner;
    let result = owner.mark_eviction(amount);
    assert(result is Ok <==> amount <= before.allocated_spec());
    assert(owner.capacity_spec() == before.capacity_spec());
    assert(owner.reserved_spec() == before.reserved_spec());
    assert(owner.safety_invariant());
    match result {
        Ok(()) => {
            assert(owner.allocated_spec() as int == before.allocated_spec() as int - amount as int);
            assert(owner.pending_eviction_spec() as int == before.pending_eviction_spec() as int + amount as int);
        },
        Err(error) => {
            assert(error == automation_structures::BudgetError::AmountExceedsAllocation);
            assert(*owner == before); let _ = error;
        },
    }
}

/// Eviction completion exports pending debit and refuses an excessive quantity unchanged.
pub fn checked_budget_complete_contract(owner: &mut automation_structures::Budget, amount: u64) {
    let ghost before = *owner;
    let result = owner.complete_eviction(amount);
    assert(result is Ok <==> amount <= before.pending_eviction_spec());
    assert(owner.capacity_spec() == before.capacity_spec());
    assert(owner.allocated_spec() == before.allocated_spec());
    assert(owner.reserved_spec() == before.reserved_spec());
    assert(owner.safety_invariant());
    match result {
        Ok(()) => { assert(owner.pending_eviction_spec() as int == before.pending_eviction_spec() as int - amount as int); },
        Err(error) => {
            assert(error == automation_structures::BudgetError::AmountExceedsPendingEviction);
            assert(*owner == before); let _ = error;
        },
    }
}

/// Dynamic admission retains exact original custody; a visit exports stable level order.
pub fn dynamic_candidate_profile_exports_admission_and_visit<C, T>(
    owner: &mut automation_structures::CandidateTraversal<C, T>, value: T,
)
    requires old(owner).inv(),
{
    let ghost context = owner.context_spec();
    let ghost originals = owner.candidates_spec();
    match owner.admit(None, value, u64::MAX, 0) {
        Ok(id) => {
            assert(owner.inv() && owner.candidates_spec() == originals.push((id.index_spec(), value)));
            assert(!owner.visited_spec(id.index_spec()));
            let _ = id;
        },
        Err((_, returned)) => { assert(returned == value && owner.candidates_spec() == originals); let _ = returned; },
    }
    let ghost before = *owner;
    match owner.step() {
        Ok(Some(id)) => { assert(owner.visited_spec(id.index_spec())); assert(owner.pending_spec() == before.pending_spec() - 1); let _ = id; },
        Ok(None) => { assert(owner.pending_spec() == 0); },
        Err(_) => { assert(*owner == before); },
    }
    assert(owner.context_spec() == context);
}

/// Consuming completion proves the real frontier empty and retains all typed candidates.
pub fn dynamic_candidate_profile_exports_completion<C, T>(owner: automation_structures::CandidateTraversal<C, T>)
    requires owner.inv(),
{
    match owner.finish() {
        Ok(done) => {
            assert(done.inv());
            proof { done.expose_complete(); }
            assert(done.profile_spec().frontier_spec().len() == 0);
            assert(done.profile_spec().candidates_spec() == owner.candidates_spec());
            let _ = done;
        },
        Err(original) => { assert(original == owner); let _ = original; },
    }
}

/// Fallible construction retains the existing star's exact initialization contract.
pub fn admitted_traversal_storage() {
    if let Ok(engine) = automation_structures::compositions::traversal_engine::TraversalEngine::try_new(4, 0, 8) {
        assert(engine.inv() && engine.queue.values@ == seq![0usize]);
        assert(engine.accepted.accumulated@.len() == 0 && engine.budget.allocated == 0);
        let _ = engine;
    }
}

/// The existing forest actions preserve both directions of reachable edge correspondence.
pub fn admitted_hierarchy_storage_has_complete_parent_edges() {
    if let Ok(mut hierarchy) = automation_structures::primitives::quality_hierarchy::QualityHierarchy::try_new(4, u64::MAX) {
            hierarchy.set_node_properties(0, u64::MAX, 0);
            hierarchy.set_node_properties(1, 2, 0);
            hierarchy.set_node_properties(2, 1, 0);
            hierarchy.add_child(0, 1);
            hierarchy.add_child(1, 2);
            assert(hierarchy.parent_has_edge());
            assert(hierarchy.parent@[1] == 0 && hierarchy.parent@[2] == 1);
            proof { hierarchy.expose_parent_edge(1); hierarchy.expose_parent_edge(2); }
            assert(hierarchy.edge_exists(0, 1) && hierarchy.edge_exists(1, 2));
            assert(hierarchy.parent@[3] == 4 && hierarchy.cost@[2] == 0);
    }
}

/// A canonical step preserves the frozen context and exports its exact progress.
pub fn finite_rooted_profile_exports_nonbinding_step_and_completion(
    profile: &mut automation_structures::RootedTraversal,
)
    requires old(profile).inv(),
{
    let ghost context = profile.hierarchy_spec();
    let ghost before = profile.considered_spec();
    let node = profile.step();
    assert(profile.hierarchy_spec() == context && profile.inv());
    if let Some(node) = node {
        assert(profile.considered_spec() == before + 1);
        assert(profile.discovered_spec(node));
        let _ = node;
    } else {
        assert(profile.frontier_spec().len() == 0);
        assert(profile.considered_spec() == context.num_nodes);
    }
}

/// Completion consumes the canonical profile and refuses every unfinished frontier.
pub fn finite_rooted_profile_exports_seal(profile: automation_structures::RootedTraversal)
    requires profile.inv(),
{
    match profile.finish() {
        Ok(done) => {
            proof {
                done.expose_complete();
                assert forall|node: usize| node < profile.hierarchy_spec().num_nodes implies
                    #[trigger] done.profile_spec().discovered_spec(node) by {};
            }
            let _ = done;
        },
        Err(original) => { assert(original == profile && profile.frontier_spec().len() > 0); let _ = original; },
    }
}

/// Immutable signed domain content for the shared named projected fold.
pub struct SignedInputs { pub values: Vec<i64> }
impl automation_structures::ReductionProjection<automation_structures::CheckedSignedAdd> for SignedInputs {
    open spec fn domain_len(&self) -> nat { self.values@.len() }
    open spec fn item_spec(&self, position: int) -> i64 { self.values@[position] }
    fn len(&self) -> (length: usize) { self.values.len() }
    #[expect(clippy::indexing_slicing, reason = "ReductionProjection requires position inside this immutable domain before item is called")]
    fn item(&self, position: usize) -> (item: i64) { self.values[position] }
}

/// External construction proves ordered completion and the exact first-refused prefix.
pub fn named_projected_reduction_is_constructible() {
    use automation_structures::{CheckedSignedAdd, IncrementalReduction};
    reveal_with_fuel(automation_structures::compositions::reduction::projected_fold_to, 4);
    reveal_with_fuel(automation_structures::compositions::reduction::projected_prefix_admitted, 4);
    let mut values = Vec::new(); values.push(7i64); values.push(-4i64);
    let source = SignedInputs { values };
    match IncrementalReduction::try_from_projection(&source, CheckedSignedAdd) {
        Ok(_fold) => { assert(_fold.processed_spec() == 2 && _fold.result_spec() == 3i64); },
        Err(_) => { assert(false); },
    }
    let mut values = Vec::new(); values.push(i64::MAX); values.push(1i64); values.push(-1i64);
    let source = SignedInputs { values };
    match IncrementalReduction::try_from_projection(&source, CheckedSignedAdd) {
        Err((_reason, _fold)) => {
            assert(_reason == automation_structures::RecordRefusal::Domain);
            assert(_fold.processed_spec() == 1 && _fold.result_spec() == i64::MAX);
        },
        Ok(_) => { assert(false); },
    }
}

/// Pure size content for the external Buffer query control.
pub struct EncodedSize;
impl automation_structures::BufferSizeProjection<usize> for EncodedSize {
    open spec fn size_spec(&self, value: usize) -> usize { value }
    fn size(&self, value: &usize) -> (size: usize) { *value }
}

/// The exported owner query proves exact totals and overflow without changing FIFO state.
pub fn buffer_projected_size_is_constructible() -> (buffer: Buffer<usize>)
    ensures buffer.well_formed(), buffer.retained() == seq![usize::MAX, 0usize, 1usize],
{
    reveal_with_fuel(automation_structures::connectives::buffer::projected_size_to, 4);
    let mut buffer = Buffer::new(3);
    let _empty = buffer.projected_size(&EncodedSize);
    assert(_empty == Ok(0usize));
    let _pushed = buffer.push(usize::MAX); assert(_pushed is Ok);
    let _pushed = buffer.push(0usize); assert(_pushed is Ok);
    let _exact = buffer.projected_size(&EncodedSize);
    assert(_exact == Ok(usize::MAX));
    let _pushed = buffer.push(1usize); assert(_pushed is Ok);
    let ghost before = buffer;
    let _overflow = buffer.projected_size(&EncodedSize);
    assert(_overflow == Err(automation_structures::BufferSizeError::Overflow));
    assert(buffer == before);
    buffer
}

/// Named preparations bind the unchanged owner, exact commit and typed refusal across crates.
pub fn named_prepared_reduction_is_constructible() -> (fold:
    automation_structures::IncrementalReduction<automation_structures::CheckedSignedAdd>)
    ensures fold.inv(), fold.processed_spec() == 2, fold.result_spec() == 3i64,
{
    use automation_structures::{CheckedSignedAdd, IncrementalReduction};
    let mut fold = IncrementalReduction::new(2, CheckedSignedAdd);
    match fold.prepare(7i64) {
        Ok(prepared) => { let _item = prepared.cancel(); assert(_item == 7); },
        Err(_) => { assert(false); },
    }
    assert(fold.processed_spec() == 0 && fold.result_spec() == 0);
    match fold.prepare(7i64) {
        Ok(prepared) => { let _result = prepared.commit(); assert(_result == (1usize, 7i64)); },
        Err(_) => { assert(false); },
    }
    match fold.prepare(-4i64) {
        Ok(prepared) => { let _result = prepared.commit(); assert(_result == (2usize, 3i64)); },
        Err(_) => { assert(false); },
    }
    let ghost before = fold;
    match fold.prepare(9i64) {
        Err((_reason, _item)) => { assert(_reason == automation_structures::RecordRefusal::Capacity && _item == 9); },
        Ok(prepared) => { let _ = prepared.cancel(); assert(false); },
    }
    assert(fold == before);
    fold
}

/// Borrowed preparation exposes both early stutters and the exact refused prefix.
pub fn reduction_workspace_preparation_and_cancel<
    O: automation_structures::TypedChainOperation,
    S: automation_structures::connectives::buffer::BufferLayout<(O::Item, O::Carry)>,
>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
    pending: &mut automation_structures::connectives::buffer::Buffer<(O::Item, O::Carry), S>,
)
    requires old(owner).inv(), old(pending).well_formed(),
    ensures final(owner).inv(), final(pending).well_formed(),
{
    let ghost before = *owner;
    let ghost workspace_before = *pending;
    match owner.prepare_row_in(items, pending) {
        Ok(prepared) => {
            assert(prepared.inv());
            assert(prepared.before_spec() == before);
            assert(prepared.items_spec() == items@);
            let ghost prepared_workspace = prepared.workspace_before_spec();
            assert(prepared_workspace.capacity == workspace_before.capacity);
            prepared.cancel();
            assert(*owner == before);
            assert(*pending == prepared_workspace);
        },
        Err(error) => {
            assert(*owner == before);
            assert(pending.well_formed());
            assert(pending.capacity == workspace_before.capacity);
            match error {
                automation_structures::ReductionWorkspaceError::CapacityMismatch { expected: _expected, actual: _actual } => {
                    assert(items@.len() == before.columns_spec().len());
                    assert(_expected == items@.len());
                    assert(_actual == workspace_before.capacity && _actual != _expected);
                    assert(*pending == workspace_before);
                },
                automation_structures::ReductionWorkspaceError::Row(row) => match row {
                    automation_structures::ReductionRowError::WidthMismatch => {
                        assert(items@.len() != before.columns_spec().len());
                        assert(*pending == workspace_before);
                    },
                    automation_structures::ReductionRowError::StorageUnavailable => { assert(false); },
                    automation_structures::ReductionRowError::Column { column: _column, reason } => {
                        assert(items@.len() == before.columns_spec().len());
                        assert(workspace_before.capacity == items@.len() && _column < items@.len());
                        assert(pending.values@.len() == _column);
                        assert forall|i: int| 0 <= i < _column implies
                            (#[trigger] pending.values@[i]).0 == items@[i]
                            && pending.values@[i].1 == before.columns_spec()[i].1.operator_spec().combined(
                                before.columns_spec()[i].1.result_spec(), items@[i])
                            && before.columns_spec()[i].1.processed_spec() < before.columns_spec()[i].1.limit_spec()
                            && before.columns_spec()[i].1.operator_spec().accepts(
                                before.columns_spec()[i].1.result_spec(), items@[i]) by {}
                        match reason {
                            automation_structures::RecordRefusal::Capacity => {
                                assert(before.columns_spec()[_column as int].1.processed_spec()
                                    >= before.columns_spec()[_column as int].1.limit_spec());
                            },
                            automation_structures::RecordRefusal::Domain => {
                                assert(before.columns_spec()[_column as int].1.processed_spec()
                                    < before.columns_spec()[_column as int].1.limit_spec());
                                assert(!before.columns_spec()[_column as int].1.operator_spec().accepts(
                                    before.columns_spec()[_column as int].1.result_spec(), items@[_column as int]));
                            },
                            _ => {},
                        }
                    },
                    _ => {},
                },
                _ => {},
            }
        },
    }
}

/// Consuming borrowed commit preserves the complete prepared workspace and publishes every column.
pub fn reduction_workspace_commit_exports_complete_row<
    O: automation_structures::TypedChainOperation,
    S: automation_structures::connectives::buffer::BufferLayout<(O::Item, O::Carry)>,
>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
    pending: &mut automation_structures::connectives::buffer::Buffer<(O::Item, O::Carry), S>,
)
    requires old(owner).inv(), old(pending).well_formed(),
    ensures final(owner).inv(), final(pending).well_formed(),
{
    let ghost before = *owner;
    match owner.prepare_row_in(items, pending) {
        Ok(prepared) => {
            assert(prepared.before_spec() == before);
            assert(prepared.items_spec() == items@);
            let ghost prepared_workspace = prepared.workspace_before_spec();
            prepared.commit();
            assert(*pending == prepared_workspace);
            assert(owner.inv());
            assert(owner.columns_spec().len() == before.columns_spec().len());
            assert forall|i: int| 0 <= i < before.columns_spec().len() implies
                (#[trigger] owner.columns_spec()[i]).0 == before.columns_spec()[i].0
                && owner.columns_spec()[i].1.operator_spec() == before.columns_spec()[i].1.operator_spec()
                && owner.columns_spec()[i].1.limit_spec() == before.columns_spec()[i].1.limit_spec()
                && owner.columns_spec()[i].1.processed_spec() == before.columns_spec()[i].1.processed_spec() + 1
                && owner.columns_spec()[i].1.result_spec() == before.columns_spec()[i].1.operator_spec().combined(
                    before.columns_spec()[i].1.result_spec(), items@[i]) by {}
        },
        Err(_) => { assert(*owner == before); },
    }
}

/// An actual implicit scope drop resolves both borrows without changing either token-creation owner.
pub fn reduction_workspace_implicit_drop_preserves_both_owners<
    O: automation_structures::TypedChainOperation,
    S: automation_structures::connectives::buffer::BufferLayout<(O::Item, O::Carry)>,
>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
    pending: &mut automation_structures::connectives::buffer::Buffer<(O::Item, O::Carry), S>,
)
    requires old(owner).inv(), old(pending).well_formed(),
    ensures final(owner).inv(), final(pending).well_formed(),
{
    let ghost before = *owner;
    match owner.prepare_row_in(items, pending) {
        Ok(prepared) => {
            assert(prepared.before_spec() == before);
            let ghost prepared_workspace = prepared.workspace_before_spec();
            {
                let _prepared = prepared;
                assert(has_resolved(_prepared));
            }
            assert(*owner == before);
            assert(*pending == prepared_workspace);
        },
        Err(_) => { assert(*owner == before); },
    }
}

/// The reusable heap profile instantiates each generic borrowed contract.
pub fn reduction_workspace_fifo_contracts<O: automation_structures::TypedChainOperation>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
    pending: &mut automation_structures::connectives::buffer::Buffer<(O::Item, O::Carry), automation_structures::FifoStorage>,
)
    requires old(owner).inv(), old(pending).well_formed(),
{
    reduction_workspace_preparation_and_cancel(owner, items, pending);
    reduction_workspace_implicit_drop_preserves_both_owners(owner, items, pending);
    reduction_workspace_commit_exports_complete_row(owner, items, pending);
}

/// Row preparation exports the entire unchanged owner and exact refusal guards.
pub fn reduction_columns_preparation_and_cancel_preserve_owner<
    O: automation_structures::TypedChainOperation,
    S: automation_structures::connectives::buffer::BufferLayout<(O::Item, O::Carry)>,
>(owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    match owner.prepare_row_with_storage::<S>(items) {
        Ok(prepared) => {
            assert(prepared.inv());
            assert(prepared.before_spec() == before);
            assert(prepared.items_spec() == items@);
            prepared.cancel();
            assert(*owner == before);
        },
        Err(error) => {
            assert(*owner == before);
            match error {
                automation_structures::ReductionRowError::WidthMismatch => {
                    assert(items@.len() != before.columns_spec().len());
                },
                automation_structures::ReductionRowError::StorageUnavailable => {
                    assert(items@.len() == before.columns_spec().len());
                },
                automation_structures::ReductionRowError::Column { column: _column, reason } => {
                    assert(items@.len() == before.columns_spec().len() && _column < items@.len());
                    assert forall|i: int| 0 <= i < _column implies
                        (#[trigger] before.columns_spec()[i]).1.processed_spec()
                            < before.columns_spec()[i].1.limit_spec()
                        && before.columns_spec()[i].1.operator_spec().accepts(
                            before.columns_spec()[i].1.result_spec(), items@[i]) by {}
                    match reason {
                        automation_structures::RecordRefusal::Capacity => {
                            assert(before.columns_spec()[_column as int].1.processed_spec()
                                >= before.columns_spec()[_column as int].1.limit_spec());
                        },
                        automation_structures::RecordRefusal::Domain => {
                            assert(before.columns_spec()[_column as int].1.processed_spec()
                                < before.columns_spec()[_column as int].1.limit_spec());
                            assert(!before.columns_spec()[_column as int].1.operator_spec().accepts(
                                before.columns_spec()[_column as int].1.result_spec(), items@[_column as int]));
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
    }
}

/// One-use row commit publishes every admitted column through the existing contract.
pub fn reduction_columns_commit_exports_complete_row<
    O: automation_structures::TypedChainOperation,
    S: automation_structures::connectives::buffer::BufferLayout<(O::Item, O::Carry)>,
>(owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    match owner.prepare_row_with_storage::<S>(items) {
        Ok(prepared) => {
            assert(prepared.before_spec() == before);
            assert(prepared.items_spec() == items@);
            prepared.commit();
            assert(owner.inv());
            assert(owner.columns_spec().len() == before.columns_spec().len());
            assert forall|i: int| 0 <= i < before.columns_spec().len() implies
                (#[trigger] owner.columns_spec()[i]).0 == before.columns_spec()[i].0
                && owner.columns_spec()[i].1.operator_spec() == before.columns_spec()[i].1.operator_spec()
                && owner.columns_spec()[i].1.limit_spec() == before.columns_spec()[i].1.limit_spec()
                && owner.columns_spec()[i].1.processed_spec() == before.columns_spec()[i].1.processed_spec() + 1
                && owner.columns_spec()[i].1.result_spec() == before.columns_spec()[i].1.operator_spec().combined(
                    before.columns_spec()[i].1.result_spec(), items@[i]) by {}
        },
        Err(_) => { assert(*owner == before); },
    }
}

/// Instantiate the unchanged preparation/refusal/cancel law for the inline profile.
pub fn reduction_columns_inline_preparation<O: automation_structures::TypedChainOperation>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
)
    requires old(owner).inv(),
{
    reduction_columns_preparation_and_cancel_preserve_owner::<O, automation_structures::connectives::buffer::InlineStorage<4>>(owner, items);
}

/// Instantiate the unchanged complete-row publication law for the inline profile.
pub fn reduction_columns_inline_commit<O: automation_structures::TypedChainOperation>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
)
    requires old(owner).inv(),
{
    reduction_columns_commit_exports_complete_row::<O, automation_structures::connectives::buffer::InlineStorage<4>>(owner, items);
}

/// Instantiate the unchanged preparation/refusal/cancel law for the contiguous profile.
pub fn reduction_columns_contiguous_preparation<O: automation_structures::TypedChainOperation>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    match owner.prepare_row(items) {
        Ok(prepared) => {
            assert(prepared.inv());
            assert(prepared.before_spec() == before);
            assert(prepared.items_spec() == items@);
            prepared.cancel();
            assert(*owner == before);
        },
        Err(error) => {
            assert(*owner == before);
            match error {
                automation_structures::ReductionRowError::WidthMismatch => {
                    assert(items@.len() != before.columns_spec().len());
                },
                automation_structures::ReductionRowError::StorageUnavailable => {
                    assert(items@.len() == before.columns_spec().len());
                },
                automation_structures::ReductionRowError::Column { column: _column, reason } => {
                    assert(items@.len() == before.columns_spec().len() && _column < items@.len());
                    assert forall|i: int| 0 <= i < _column implies
                        (#[trigger] before.columns_spec()[i]).1.processed_spec()
                            < before.columns_spec()[i].1.limit_spec()
                        && before.columns_spec()[i].1.operator_spec().accepts(
                            before.columns_spec()[i].1.result_spec(), items@[i]) by {}
                    match reason {
                        automation_structures::RecordRefusal::Capacity => {
                            assert(before.columns_spec()[_column as int].1.processed_spec()
                                >= before.columns_spec()[_column as int].1.limit_spec());
                        },
                        automation_structures::RecordRefusal::Domain => {
                            assert(before.columns_spec()[_column as int].1.processed_spec()
                                < before.columns_spec()[_column as int].1.limit_spec());
                            assert(!before.columns_spec()[_column as int].1.operator_spec().accepts(
                                before.columns_spec()[_column as int].1.result_spec(), items@[_column as int]));
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
    }
}

/// Instantiate the unchanged complete-row publication law for the contiguous profile.
pub fn reduction_columns_contiguous_commit<O: automation_structures::TypedChainOperation>(
    owner: &mut automation_structures::ReductionColumns<O>, items: &Vec<O::Item>,
)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    match owner.prepare_row(items) {
        Ok(prepared) => {
            assert(prepared.before_spec() == before);
            assert(prepared.items_spec() == items@);
            prepared.commit();
            assert(owner.inv());
            assert(owner.columns_spec().len() == before.columns_spec().len());
            assert forall|i: int| 0 <= i < before.columns_spec().len() implies
                (#[trigger] owner.columns_spec()[i]).0 == before.columns_spec()[i].0
                && owner.columns_spec()[i].1.operator_spec() == before.columns_spec()[i].1.operator_spec()
                && owner.columns_spec()[i].1.limit_spec() == before.columns_spec()[i].1.limit_spec()
                && owner.columns_spec()[i].1.processed_spec() == before.columns_spec()[i].1.processed_spec() + 1
                && owner.columns_spec()[i].1.result_spec() == before.columns_spec()[i].1.operator_spec().combined(
                    before.columns_spec()[i].1.result_spec(), items@[i]) by {}
        },
        Err(_) => { assert(*owner == before); },
    }
}

/// Moving a head preserves the other retained prefix and pending suffix.
pub fn accumulator_preserves_prefix_and_pending_suffix() {
    use automation_structures::connectives::accumulator::Accumulator;
    let mut values = Vec::new();
    values.push(7u64); values.push(9u64); values.push(11u64);
    let mut owner = Accumulator::new(values);
    let _first = owner.advance(); assert(_first == Some(7u64));
    let ghost original = owner.original@;
    let ghost prefix = owner.accumulated@;
    let ghost pending = owner.pending@;
    assert(prefix == seq![7u64] && pending == seq![9u64, 11u64]);
    let _second = owner.advance(); assert(_second == Some(9u64));
    assert(owner.original@ == original);
    assert(owner.accumulated@ == prefix.push(pending[0]));
    assert(owner.pending@ == pending.skip(1));
    assert(owner.pending@ == seq![11u64]);
    let _third = owner.advance(); assert(_third == Some(11u64));
    let ghost complete = owner.accumulated@;
    assert(complete == seq![7u64, 9u64, 11u64] && owner.pending@.len() == 0);
    owner.append(13u64);
    assert(owner.original@ == original.push(13u64));
    assert(owner.accumulated@ == complete.push(13u64));
    assert(owner.pending@.len() == 0);
}

/// The external consumer receives the actual ordered permutation, with its contract.
pub fn immutable_arrangement_exports_both_directions() {
    use automation_structures::connectives::ordering_pass::{IndexArrangement, SignedRowOrder};
    use automation_structures::NullableSigned::Value;
    let mut values = Vec::new(); values.push(Value(2)); values.push(Value(3)); values.push(Value(2));
    let order = SignedRowOrder { values: &values, descending: true, nulls_first: false };
    if let Ok(arranged) = IndexArrangement::try_new(3, &order) {
        assert(arranged.inv());
        let ghost positions = arranged.positions_spec();
        assert(positions[0] < 3 && positions[1] < 3 && positions[2] < 3);
        assert(positions[0] != positions[1] && positions[0] != positions[2] && positions[1] != positions[2]);
        assert(positions == seq![1usize, 0usize, 2usize]);
        assert(arranged.inverse_spec()[0] == 1 && arranged.inverse_spec()[1] == 0
            && arranged.inverse_spec()[2] == 2);
        let _rank = arranged.rank_of(0); assert(_rank == Some(1usize));
        let _original = arranged.original_at(0); assert(_original == Some(1usize));
        let _foreign = arranged.rank_of(3); assert(_foreign == None);
    }
}

/// Complete minimum membership is usable by an external consumer without selecting K.
pub fn complete_minimum_selection_is_constructible<C: automation_structures::PositionOrder>(order: C) {
    if let Ok(owner) = automation_structures::CompetitiveSelectionMinimum::try_new(order) {
        proof { owner.expose_minima(); owner.expose_arrangement(); owner.expose_scores(); }
        let _scores = owner.scores();
        assert(_scores@ == owner.scores_spec());
        assert forall|left: usize, right: usize| left < order.domain_len() && right < order.domain_len() implies
            (#[trigger] order.key_le(left, right) == (_scores@[left as int] >= _scores@[right as int])) by {}
        let _winner = owner.winner();
        assert(_winner == owner.winner_spec());
        let _hard = owner.selection();
        assert(_hard.inv() && _hard.allocation == _winner && _hard.scores@ == _scores@);
        proof {
            if let Some(winner) = _winner {
                assert forall|candidate: int| 0 <= candidate < _scores.len() implies
                    (#[trigger] _scores@[candidate] <= _scores@[winner as int]
                        && (_scores@[candidate] == _scores@[winner as int] ==> winner <= candidate)) by {}
            }
        }
        assert forall|item: usize| owner.selected_spec().contains(item) <==>
            (item < order.domain_len() && forall|other: usize| other < order.domain_len()
                ==> #[trigger] order.key_le(item, other)) by {}
        let _selected = owner.selected();
        assert(_selected@ == owner.selected_spec());
    }
}

/// The external consumer receives the actual ordered permutation, with its contract.
///
/// # Errors
/// Returns the arrangement's domain or storage refusal.
pub fn finite_ordering_is_constructible()
    -> (result: Result<Vec<usize>, automation_structures::connectives::ordering_pass::ArrangementError>)
    ensures result is Ok ==> result.unwrap()@ == seq![1usize, 0usize, 2usize],
{
    use automation_structures::connectives::ordering_pass::{try_arrange_indices, SignedRowOrder};
    use automation_structures::primitives::audit_sink::NullableSigned::Value;
    let mut values = Vec::new(); values.push(Value(2)); values.push(Value(3)); values.push(Value(1));
    let order = SignedRowOrder { values: &values, descending: true, nulls_first: false };
    let result = try_arrange_indices(3, &order);
    if let Ok(ref _positions) = result {
        assert(_positions@[0] < 3 && _positions@[1] < 3 && _positions@[2] < 3);
        assert(_positions@[0] != _positions@[1] && _positions@[0] != _positions@[2] && _positions@[1] != _positions@[2]);
        assert(_positions@ == seq![1usize, 0usize, 2usize]);
    }
    result
}



/// An external client borrows the actual retained AuditSink and mutates only that owner.
pub fn indexed_summary_owner_is_borrowable() -> (result: Option<i64>)
    ensures result is Some ==> result.unwrap() == 7,
{
    use automation_structures::primitives::audit_sink::{AuditSink, CheckedSignedAdd};
    let mut registry = resource_registry::ResourceRegistry::new_indexed();
    let mut bytes = Vec::new(); bytes.push(17u8);
    let fold = AuditSink::with_summary(2, CheckedSignedAdd);
    let inserted = registry.try_register_key(resource_registry::ByteKey::from_bytes(bytes), fold);
    if inserted.is_err() { return None; }
    let mut probe = Vec::new(); probe.push(17u8);
    {
        let borrowed = registry.lookup_query_mut(&probe.as_slice());
        match borrowed {
            Some(value) => {
                assert(value.chain_valid());
                let _accepted = value.record_typed(7i64);
                assert(_accepted);
            }
            None => { assert(false); }
        }
    }
    match registry.lookup_query(&probe.as_slice()) {
        Some(value) => { let carry = value.carry(); assert(carry == 7); Some(carry) }
        None => { assert(false); None }
    }
}



/// The external proof consumer can retain a typed nullable summary without a copied reducer.
pub fn nullable_summary_is_constructible() -> (fold:
    automation_structures::primitives::audit_sink::AuditSink<
        automation_structures::primitives::audit_sink::CheckedSignedSumCount,
        automation_structures::primitives::audit_sink::SummaryHistory<
            automation_structures::primitives::audit_sink::NullableSigned,
            automation_structures::primitives::audit_sink::SignedSumCount>>)
    ensures fold.chain_valid(), fold.history_spec().len() == 3,
        fold.last_hash.sum == -4i64, fold.last_hash.count == 2u64,
{
    use automation_structures::primitives::audit_sink::{AuditSink, CheckedSignedSumCount, NullableSigned};
    let mut fold = AuditSink::with_summary(3, CheckedSignedSumCount);
    let _first = fold.record_typed(NullableSigned::Value(7));
    assert(_first);
    let _second = fold.record_typed(NullableSigned::Missing);
    assert(_second);
    let ghost prefix = fold.history_spec();
    let ghost prior_carry = fold.last_hash;
    let _third = fold.record_typed(NullableSigned::Value(-11));
    assert(_third);
    assert(fold.history_spec() == prefix.push(automation_structures::primitives::audit_sink::AuditEntry {
        operation: NullableSigned::Value(-11i64), prev_hash: prior_carry, hash: fold.last_hash,
    }));
    let ghost before_refusal = fold.history_spec();
    let _refused = fold.record_typed(NullableSigned::Value(1));
    assert(!_refused);
    assert(fold.history_spec() == before_refusal);
    fold
}



/// Connective and primitive relations remain usable across the crate boundary.
pub proof fn structure_relations_are_importable()
    ensures
        automation_structures::connectives::counter::nonnegative(0),
        automation_structures::connectives::ordering_pass::strictly_before(0, 1),
        automation_structures::primitives::budget::budget_safety(1, 0, 0, 0),
        resource_registry::unique_keys(Seq::<u64>::empty()),
{
}

/// Equal encoded contents from distinct allocations share one canonical registry identity.
pub fn byte_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<resource_registry::ByteKey, u64>)
    ensures registry.unique_identities(), registry.entries@.len() == 1,
        registry.maps_identity(seq![1u8, 0u8, 2u8], 22),
{
    let mut registry = resource_registry::ResourceRegistry::new();
    let mut bytes = Vec::new();
    bytes.push(1u8); bytes.push(0u8); bytes.push(2u8);
    registry.register_key(resource_registry::ByteKey::from_bytes(bytes), 11u64);
    let mut replacement = Vec::new();
    replacement.push(1u8); replacement.push(0u8); replacement.push(2u8);
    let key = resource_registry::ByteKey::from_bytes(replacement);
    assert(resource_registry::KeyIdentity::identity(&key) == seq![1u8, 0u8, 2u8]);
    proof { resource_registry::without_identity_to_remove_unique(registry.entries@, key, 1, 0); }
    registry.register_key(key, 22u64);
    assert(registry.maps_key(key, 22u64));
    assert(registry.maps_identity(seq![1u8, 0u8, 2u8], 22u64));
    let mut query_bytes = Vec::new();
    query_bytes.push(1u8); query_bytes.push(0u8); query_bytes.push(2u8);
    let query = query_bytes.as_slice();
    match registry.lookup_query(&query) {
        Some(_value) => { assert(*_value == 22); }
        None => { assert(false); }
    }
    registry
}

/// An external caller takes an original non-Copy value through the identity owner.
pub fn registry_take_frames_owned_bindings() {
    let mut owner = resource_registry::ResourceRegistry::<u64, Vec<u8>>::new();
    let mut first = Vec::new(); first.push(7u8);
    let mut second = Vec::new(); second.push(2u8);
    owner.register_key(7, first); owner.register_key(2, second);
    let _removed = owner.take_query(&7u64);
    assert(_removed == Some((7u64, first)));
    assert(owner.maps_key(2, second) && !owner.contains_key_identity(7));
    assert(owner.entries@.len() == 1);
    let ghost before = owner.entries@;
    let _absent = owner.take_query(&7u64);
    assert(_absent is None && owner.entries@ == before);
}

/// Typed latest-value and registration/notification contracts cross the package boundary.
pub fn summary_signal_is_constructible() {
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 1, 2);
    assert(signal.inv() && signal.value_spec() == 7 && signal.history_spec().len() == 0);
    if let Ok(token) = signal.register() {
        assert(token.scope_spec() == 41 && token.generation_spec() == 1);
        let _changed = signal.set_value(9u64);
        match _changed {
            Ok(true) => { assert(signal.value_spec() == 9 && signal.history_spec().len() == 1); },
            _ => { assert(false); },
        }
        proof { signal.expose_listener_state(token); }
        let _pending = signal.pending(token); assert(_pending == Ok(true));
        let _observed = signal.notify(token);
        assert(_observed is Ok);
        assert(_observed->Ok_0.value == 9 && _observed->Ok_0.head == 1 && _observed->Ok_0.changed);
        assert(signal.caught_up_spec(token));
        proof { signal.expose_listener_state(token); }
        let _repeated = signal.notify(token);
        assert(_repeated is Ok && !_repeated->Ok_0.changed);
        let _removed = signal.remove(token);
        assert(_removed is Ok && !signal.registered_spec(token));
        let _stale = signal.pending(token);
        assert(_stale == Err(automation_structures::SignalProfileError::UnknownListener));
        if let Ok(_next) = signal.register() {
            assert(_next.generation_spec() == 2);
            assert(signal.registered_spec(_next));
        }
    }
}

/// Catch-up and removal preserve another live listener's unobserved changes.
pub fn summary_signal_notify_frames_other_listener() {
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 2, 2);
    let first = match signal.register() { Ok(token) => token, Err(_) => return };
    let _second = match signal.register() { Ok(token) => token, Err(_) => return };
    assert(first.generation_spec() == 1 && _second.generation_spec() == 2);
    assert(signal.listeners_spec() == seq![
        (first.generation_spec(), automation_structures::connectives::cursor::Cursor { position: 0 }),
        (_second.generation_spec(), automation_structures::connectives::cursor::Cursor { position: 0 })]);
    let _changed = signal.set_value(9u64);
    assert(_changed == Ok(true));
    let ghost before_notify = signal.listeners_spec();
    assert(signal.listeners_spec()[0].0 == first.generation_spec());
    assert(first.scope_spec() == signal.scope_spec());
    proof { signal.expose_listener_state(first); }
    assert(signal.registered_spec(first));
    assert(signal.pending_spec(first));
    let _first_observation = signal.notify(first);
    assert(_first_observation is Ok && _first_observation->Ok_0.changed);
    proof {
        signal.expose_listener_state(first); signal.expose_listener_state(_second);
    }
    assert(signal.listeners_spec().len() >= 2);
    assert(signal.listeners_spec()[1] == before_notify[1]);
}

/// Removal preserves the exact remaining listener and its unobserved change.
pub fn summary_signal_remove_frames_other_listener() {
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 2, 2);
    let first = match signal.register() { Ok(token) => token, Err(_) => return };
    let second = match signal.register() { Ok(token) => token, Err(_) => return };
    assert(first.generation_spec() == 1 && second.generation_spec() == 2);
    let _changed = signal.set_value(9u64);
    assert(_changed == Ok(true));
    assert(signal.listeners_spec()[0].0 == first.generation_spec());
    assert(first.scope_spec() == signal.scope_spec());
    proof { signal.expose_listener_state(first); }
    assert(signal.registered_spec(first));
    let _removed = signal.remove(first);
    assert(_removed is Ok);
    assert(signal.listeners_spec() == seq![
        (second.generation_spec(), automation_structures::connectives::cursor::Cursor { position: 0 })]);
    assert(signal.listeners_spec()[0].0 == second.generation_spec());
    assert(second.scope_spec() == signal.scope_spec());
    proof { signal.expose_listener_state(second); }
    assert(signal.registered_spec(second));
    let _still_pending = signal.pending(second);
    assert(_still_pending == Ok(true));
    let _second_observation = signal.notify(second);
    assert(_second_observation is Ok && _second_observation->Ok_0.changed
        && _second_observation->Ok_0.value == 9 && _second_observation->Ok_0.head == 1);
    proof { signal.expose_listener_state(second); }
    let _caught_up = signal.pending(second);
    assert(_caught_up == Ok(false));
}

/// Configuration remains under the original Budget and AuditSink through every action.
pub proof fn summary_signal_owned_limits_follow_from_invariant(
    signal: &automation_structures::SummarySignal<u64>)
    requires signal.inv(),
    ensures signal.listeners_spec().len() <= signal.listener_limit_spec() as nat,
        signal.history_spec().len() <= signal.change_limit_spec(),
        signal.issued_spec() <= u64::MAX as nat,
{
    signal.expose_limits();
}

/// A registered Cursor has a complete state and an issued positive generation.
pub proof fn summary_signal_registered_cursor_state_is_complete(
    signal: &automation_structures::SummarySignal<u64>, token: automation_structures::SignalListener)
    requires signal.inv(), signal.registered_spec(token),
    ensures signal.pending_spec(token) || signal.caught_up_spec(token),
        0 < token.generation_spec() as nat && token.generation_spec() as nat <= signal.issued_spec(),
{
    signal.expose_listener_state(token);
}

/// The typed owner reconstructs the existing Signal delivery-state model per live listener.
pub proof fn summary_signal_registered_listener_refines_signal_model(
    signal: &automation_structures::SummarySignal<u64>, token: automation_structures::SignalListener)
    requires signal.inv(), signal.registered_spec(token),
    ensures automation_structures::compositions::signal::model_valid(
        automation_structures::compositions::signal::SignalModel {
            current_value: signal.value_spec(),
            change_observed: signal.history_spec().len() > 0,
            pending: signal.pending_spec(token),
            notified: signal.history_spec().len() > 0 && signal.caught_up_spec(token),
        }),
{
    signal.expose_listener_state(token);
}

/// The opaque logical refusal frame exports both configured ceilings unchanged.
pub proof fn summary_signal_refusal_preserves_limits(
    signal: &automation_structures::SummarySignal<u64>,
    before: &automation_structures::SummarySignal<u64>)
    requires signal.same_state(*before),
    ensures signal.listener_limit_spec() == before.listener_limit_spec(),
        signal.change_limit_spec() == before.change_limit_spec(),
{
    signal.expose_state_frame(before);
}

/// Configuration remains under the original Budget and AuditSink through every action.
pub fn summary_signal_preserves_configured_limits() {
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 2, 2);
    assert(signal.listener_limit_spec() == 2 && signal.change_limit_spec() == 2);
    let _change = signal.set_value(9u64);
    assert(signal.listener_limit_spec() == 2 && signal.change_limit_spec() == 2);
    let first = signal.register();
    assert(signal.listener_limit_spec() == 2 && signal.change_limit_spec() == 2);
    if let Ok(token) = first {
        let _observation = signal.notify(token);
        assert(signal.listener_limit_spec() == 2 && signal.change_limit_spec() == 2);
        let _removed = signal.remove(token);
        assert(signal.listener_limit_spec() == 2 && signal.change_limit_spec() == 2);
    }
    proof { signal.expose_limits(); }
    assert(signal.listeners_spec().len() <= 2 && signal.history_spec().len() <= 2);
}

/// Full, foreign and removed tokens return their exact documented refusal variants.
pub fn summary_signal_refusals_are_exact() {
    let mut empty = automation_structures::SummarySignal::new(40, 0u64, 0, 0);
    let _full = empty.register();
    assert(_full == Err(automation_structures::SignalProfileError::ListenerCapacity));
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 1, 2);
    if let Ok(token) = signal.register() {
        proof { signal.expose_listener_state(token); }
        let ghost before_full = signal;
        let _full = signal.register();
        assert(_full == Err(automation_structures::SignalProfileError::ListenerCapacity));
        proof { signal.expose_state_frame(&before_full); signal.expose_listener_state(token); }
        let mut other = automation_structures::SummarySignal::new(42, 0u64, 1, 2);
        let _foreign_notify = other.notify(token);
        assert(_foreign_notify == Err(automation_structures::SignalProfileError::ForeignScope));
        let _foreign_remove = other.remove(token);
        assert(_foreign_remove == Err(automation_structures::SignalProfileError::ForeignScope));
        let _removed = signal.remove(token);
        assert(_removed is Ok);
        let _stale_notify = signal.notify(token);
        assert(_stale_notify == Err(automation_structures::SignalProfileError::UnknownListener));
        let _stale_remove = signal.remove(token);
        assert(_stale_remove == Err(automation_structures::SignalProfileError::UnknownListener));
    }
}

/// A changed value appends the exact AuditSink entry without rewriting earlier changes.
pub fn summary_signal_preserves_change_history_prefix() {
    let mut signal = automation_structures::SummarySignal::new(41, 7u64, 0, 2);
    let _first = signal.set_value(9u64);
    assert(_first == Ok(true));
    let ghost prefix = signal.history_spec();
    let _second = signal.set_value(11u64);
    assert(_second == Ok(true));
    assert(signal.history_spec() == prefix.push(automation_structures::primitives::audit_sink::AuditEntry {
        operation: 11u64, prev_hash: 9u64, hash: 11u64
    }));
}

/// Change admission is the exact immutable query of the same owner's Record guard.
pub fn summary_signal_change_admission_matches_owner(
    signal: &automation_structures::SummarySignal<u64>, value: u64)
    requires signal.inv(),
{
    let _admitted = signal.can_set_value(value);
    assert(_admitted == (value == signal.value_spec()
        || signal.history_spec().len() < signal.change_limit_spec()));
}

/// Exhausted generation refuses without publication; available generation cannot report exhaustion.
pub fn summary_signal_exhausted_generation_refuses(
    signal: &mut automation_structures::SummarySignal<u64>,
    available: &mut automation_structures::SummarySignal<u64>)
    requires old(signal).inv(), old(signal).listeners_spec().len() == 0,
        old(signal).listener_limit_spec() > 0,
        old(signal).issued_spec() == u64::MAX as nat,
        old(available).inv(), old(available).issued_spec() < u64::MAX as nat,
{
    let ghost before = *signal;
    let _registered = signal.register();
    assert(_registered == Err(automation_structures::SignalProfileError::GenerationExhausted));
    assert(signal.same_state(before));
    let _not_exhausted = available.register();
    assert(_not_exhausted != Err(automation_structures::SignalProfileError::GenerationExhausted));
}

/// Listener capacity is the first refusal even when generation is exhausted.
pub fn summary_signal_capacity_precedes_exhaustion(
    signal: &mut automation_structures::SummarySignal<u64>)
    requires old(signal).inv(), old(signal).listeners_spec().len() == 0,
        old(signal).listener_limit_spec() == 0,
        old(signal).issued_spec() == u64::MAX as nat,
{
    let ghost before = *signal;
    let _registered = signal.register();
    assert(_registered == Err(automation_structures::SignalProfileError::ListenerCapacity));
    assert(signal.same_state(before));
}

/// Original non-Copy payload custody, admission, FIFO, and closure cross the public boundary.
pub fn typed_stream_preserves_owned_fifo_contracts() {
    if let Ok(mut stream) = automation_structures::TypedStream::try_new(73, 2, 5) {
        let _empty = stream.receive();
        assert(_empty == Err(automation_structures::TypedStreamError::Empty));
        let mut first = Vec::new(); first.push(7u8);
        let mut second = Vec::new(); second.push(9u8);
        proof { stream.expose_admission(2); }
        let _first = stream.publish(first, 2);
        assert(_first == Ok(0u64));
        proof { stream.expose_admission(3); }
        let _second = stream.publish(second, 3);
        assert(_second == Ok(1u64));
        let _charged = stream.retained_bytes();
        assert(_charged == 5);
        let _closed = stream.close_input();
        assert(_closed && stream.closed_spec());
        let _received = stream.receive();
        assert(_received is Ok && _received->Ok_0.sequence == 0
            && _received->Ok_0.value == first && _received->Ok_0.encoded_bytes == 2);
        let _received = stream.receive();
        assert(_received is Ok && _received->Ok_0.sequence == 1
            && _received->Ok_0.value == second && _received->Ok_0.encoded_bytes == 3);
        let _drained = stream.is_drained(); assert(_drained);
        let _terminal = stream.receive();
        assert(_terminal == Err(automation_structures::TypedStreamError::Closed));
    }
}

/// The existing default public constructor retains usize inference and its exact position.
pub fn cursor_default_constructor_exports_position(position: usize) {
    let _cursor = automation_structures::Cursor::new(position);
    assert(_cursor.position_spec() == position as nat);
}

/// The existing default carrier constructor retains its exact field.
pub fn cursor_carrier_default_constructor_exports_position(position: usize) {
    let _cursor = automation_structures::connectives::cursor::Cursor::new(position);
    assert(_cursor.position == position);
}

/// Either sealed integer profile uses the same checked public constructor.
pub fn cursor_profile_constructor_exports_position<P: automation_structures::CursorPosition>(position: P) {
    let _cursor = automation_structures::Cursor::<P>::from_position(position);
    assert(_cursor.position_spec() == position.ordinal());
}

/// Observation reads the actual retained position of an arbitrary public Cursor.
pub fn cursor_profile_observation_exports_position<P: automation_structures::CursorPosition>(cursor: &automation_structures::Cursor<P>) {
    let _position = cursor.position();
    assert(_position.ordinal() == cursor.position_spec());
}

/// Checked movement exports its exact guard, destination and complete refusal frame.
pub fn cursor_profile_movement_exports_guard_and_frame<P: automation_structures::CursorPosition>(cursor: &mut automation_structures::Cursor<P>, position: P) {
    let ghost before = *cursor;
    let result = cursor.advance_to(position);
    assert((result is Ok) == (before.position_spec() <= position.ordinal()));
    match result {
        Ok(()) => { assert(cursor.position_spec() == position.ordinal()); },
        Err(error) => {
            assert(error == automation_structures::CursorError::Regression);
            assert(*cursor == before);
            let _ = error;
        },
    }
}

/// Profile construction exports both the retained field and its mathematical observation.
pub fn cursor_carrier_profile_constructor_exports_position<P: automation_structures::CursorPosition>(position: P) {
    let _cursor = automation_structures::connectives::cursor::Cursor::<P>::from_position(position);
    assert(_cursor.position == position);
    assert(_cursor.position_spec() == position.ordinal());
}

/// An arbitrary carrier exposes the selected integer bound without a caller-owned count.
pub proof fn cursor_carrier_profile_exports_bound<P: automation_structures::CursorPosition>(cursor: &automation_structures::connectives::cursor::Cursor<P>) {
    cursor.expose_position_bound();
    assert(cursor.position_spec() == cursor.position.ordinal());
    assert(cursor.position_spec() <= P::max_ordinal());
    assert(P::max_ordinal() <= u64::MAX as nat);
}

/// The carrier's one movement action preserves monotonicity in the selected integer profile.
pub fn cursor_carrier_profile_movement_exports_position<P: automation_structures::CursorPosition>(cursor: &mut automation_structures::connectives::cursor::Cursor<P>, position: P)
    requires old(cursor).position.ordinal() <= position.ordinal(),
{
    let ghost before = *cursor;
    cursor.advance_to(position);
    assert(cursor.position == position);
    assert(cursor.position_spec() == position.ordinal());
    assert(cursor.position_spec() >= before.position_spec());
}

/// Pure integer laws export their actual checked results for both sealed representations.
pub fn cursor_integer_profile_exports_laws<P: automation_structures::CursorPosition>(position: P, other: P) {
    proof { position.expose_integer_bound(); }
    assert(position.ordinal() <= P::max_ordinal());
    assert(P::max_ordinal() <= u64::MAX as nat);
    let zero = P::zero();
    assert(zero.ordinal() == 0);
    let limit = P::limit();
    assert(limit as nat == P::max_ordinal());
    let less = position.less_than(other);
    assert(less == (position.ordinal() < other.ordinal()));
    let successor = position.checked_successor();
    assert((successor is Some) == (position.ordinal() < P::max_ordinal()));
    if let Some(_next) = successor {
        assert(_next.ordinal() == position.ordinal() + 1);
    }
    let _ = (zero, limit, less);
}

/// The default usize profile exports its own empty canonical-owner observations.
pub fn typed_stream_default_constructor_exports_initial_state<T>(scope: u64, slots: usize, bytes: u64) {
    if let Ok(stream) = automation_structures::TypedStream::<T>::try_new(scope, slots, bytes) {
        assert(stream.inv());
        assert(stream.scope_spec() == scope);
        assert(stream.entries_spec().len() == 0);
        assert(stream.published_spec() == 0);
        assert(stream.consumed_spec() == 0);
        assert(!stream.closed_spec());
        assert(stream.encoded_bytes_spec() == 0);
        assert(stream.slot_limit_spec() == slots as nat);
        assert(stream.byte_limit_spec() == bytes as nat);
        let _ = stream;
    }
}

/// Either selected lifetime profile starts with the same empty canonical owners.
pub fn typed_stream_profile_constructor_exports_initial_state<T, P: automation_structures::CursorPosition>(scope: u64, slots: usize, bytes: u64) {
    if let Ok(stream) = automation_structures::TypedStream::<T, P>::try_with_position(scope, slots, bytes) {
        assert(stream.inv());
        assert(stream.scope_spec() == scope);
        assert(stream.entries_spec().len() == 0);
        assert(stream.published_spec() == 0);
        assert(stream.consumed_spec() == 0);
        assert(!stream.closed_spec());
        assert(stream.encoded_bytes_spec() == 0);
        assert(stream.slot_limit_spec() == slots as nat);
        assert(stream.byte_limit_spec() == bytes as nat);
        let count = stream.received_count();
        assert(count.ordinal() == 0);
        let _ = count;
    }
}

/// A refused default construction exports the existing storage error class.
pub fn typed_stream_default_constructor_exports_refusal<T>(scope: u64, slots: usize, bytes: u64) {
    if let Err(error) = automation_structures::TypedStream::<T>::try_new(scope, slots, bytes) {
        assert(error == automation_structures::TypedStreamError::StorageUnavailable);
        let _ = error;
    }
}

/// Either selected profile exports the same physical-reservation refusal class.
pub fn typed_stream_profile_constructor_exports_refusal<T, P: automation_structures::CursorPosition>(scope: u64, slots: usize, bytes: u64) {
    if let Err(error) = automation_structures::TypedStream::<T, P>::try_with_position(scope, slots, bytes) {
        assert(error == automation_structures::TypedStreamError::StorageUnavailable);
        let _ = error;
    }
}

/// Arbitrary valid profiles export publication custody and the same owner frames.
pub fn typed_stream_profile_publication_exports_custody<T, P: automation_structures::CursorPosition>(stream: &mut automation_structures::TypedStream<T, P>, value: T, bytes: u64)
    requires old(stream).inv(),
{
    let ghost before = *stream;
    let result = stream.publish(value, bytes);
    assert(stream.inv());
    assert(stream.scope_spec() == before.scope_spec());
    assert(stream.slot_limit_spec() == before.slot_limit_spec());
    assert(stream.byte_limit_spec() == before.byte_limit_spec());
    assert((result is Ok) == before.publish_admitted_spec(bytes));
    match result {
        Ok(_sequence) => {
            assert(_sequence as nat == before.published_spec());
            assert(stream.entries_spec() == before.entries_spec().push((_sequence, (value, bytes))));
            assert(stream.encoded_bytes_spec() == before.encoded_bytes_spec() + bytes as nat);
            assert(stream.published_spec() == before.published_spec() + 1);
            assert(stream.consumed_spec() == before.consumed_spec());
            assert(stream.closed_spec() == before.closed_spec());
        },
        Err(_refusal) => {
            assert(_refusal.value == value);
            assert(stream.same_state(before));
            assert(stream.entries_spec() == before.entries_spec());
            assert(stream.encoded_bytes_spec() == before.encoded_bytes_spec());
            assert(stream.published_spec() == before.published_spec());
            assert(stream.consumed_spec() == before.consumed_spec());
            assert(stream.closed_spec() == before.closed_spec());
            let _ = _refusal;
        },
    }
}

/// Receipt transfers the FIFO original and advances this profile's same retained Cursor.
pub fn typed_stream_profile_receipt_exports_custody<T, P: automation_structures::CursorPosition>(stream: &mut automation_structures::TypedStream<T, P>)
    requires old(stream).inv(),
{
    let ghost before = *stream;
    let result = stream.receive();
    assert(stream.inv());
    assert(stream.scope_spec() == before.scope_spec());
    assert(stream.slot_limit_spec() == before.slot_limit_spec());
    assert(stream.byte_limit_spec() == before.byte_limit_spec());
    assert(stream.published_spec() == before.published_spec());
    assert(stream.closed_spec() == before.closed_spec());
    assert((result is Ok) == (before.entries_spec().len() > 0));
    match result {
        Ok(_received) => {
            assert(_received.sequence == before.entries_spec()[0].0);
            assert(_received.value == before.entries_spec()[0].1.0);
            assert(_received.encoded_bytes == before.entries_spec()[0].1.1);
            assert(_received.scope == before.scope_spec());
            assert(stream.entries_spec() == before.entries_spec().skip(1));
            assert(stream.encoded_bytes_spec() + _received.encoded_bytes as nat == before.encoded_bytes_spec());
            assert(stream.consumed_spec() == before.consumed_spec() + 1);
            let _ = _received;
        },
        Err(_error) => {
            assert((_error == automation_structures::TypedStreamError::Empty) == !before.closed_spec());
            assert((_error == automation_structures::TypedStreamError::Closed) == before.closed_spec());
            assert(stream.same_state(before));
            assert(stream.entries_spec() == before.entries_spec());
            assert(stream.encoded_bytes_spec() == before.encoded_bytes_spec());
            assert(stream.consumed_spec() == before.consumed_spec());
            let _ = _error;
        },
    }
}

/// Receipt count observes the actual selected Cursor representation of any valid owner.
pub fn typed_stream_profile_count_exports_position<T, P: automation_structures::CursorPosition>(stream: &automation_structures::TypedStream<T, P>)
    requires stream.inv(),
{
    let count = stream.received_count();
    assert(count.ordinal() == stream.consumed_spec());
    let _ = count;
}

/// Closing the existing Marker exports every retained-content and ceiling frame.
pub fn typed_stream_profile_closure_exports_retained_state<T, P: automation_structures::CursorPosition>(stream: &mut automation_structures::TypedStream<T, P>)
    requires old(stream).inv(),
{
    let ghost before = *stream;
    let changed = stream.close_input();
    assert(stream.inv());
    assert(stream.closed_spec());
    assert(changed == !before.closed_spec());
    assert(stream.entries_spec() == before.entries_spec());
    assert(stream.encoded_bytes_spec() == before.encoded_bytes_spec());
    assert(stream.published_spec() == before.published_spec());
    assert(stream.consumed_spec() == before.consumed_spec());
    assert(stream.scope_spec() == before.scope_spec());
    assert(stream.slot_limit_spec() == before.slot_limit_spec());
    assert(stream.byte_limit_spec() == before.byte_limit_spec());
    let _ = changed;
}

/// The owner exports each necessary admission guard and their joint sufficiency.
pub proof fn typed_stream_profile_admission_exports_guards<T, P: automation_structures::CursorPosition>(stream: &automation_structures::TypedStream<T, P>, bytes: u64, position: P)
    requires stream.inv(),
{
    position.expose_integer_bound();
    assert(P::max_ordinal() <= u64::MAX as nat);
    stream.expose_admission(bytes);
    assert(stream.publish_admitted_spec(bytes) ==> !stream.closed_spec());
    assert(stream.publish_admitted_spec(bytes) ==> stream.entries_spec().len() < stream.slot_limit_spec());
    assert(stream.publish_admitted_spec(bytes) ==> stream.encoded_bytes_spec() + bytes as nat <= stream.byte_limit_spec());
    assert(stream.publish_admitted_spec(bytes) ==> stream.published_spec() < u64::MAX as nat);
    assert(stream.publish_admitted_spec(bytes) ==> stream.published_spec() < P::max_ordinal());
    assert((!stream.closed_spec() && stream.entries_spec().len() < stream.slot_limit_spec()
        && stream.encoded_bytes_spec() + bytes as nat <= stream.byte_limit_spec()
        && stream.published_spec() < u64::MAX as nat && stream.published_spec() < P::max_ordinal())
        ==> stream.publish_admitted_spec(bytes));
}

/// Arbitrary valid owners export their actual FIFO observations and ordered admission.
pub fn typed_stream_queries_match_owner_state<T, P: automation_structures::CursorPosition>(stream: &automation_structures::TypedStream<T, P>, bytes: u64, policy: automation_structures::TypedStreamPublicationPolicy)
    requires stream.inv(),
{
    let length = stream.len();
    assert(length as nat == stream.entries_spec().len());
    let empty = stream.is_empty();
    assert(empty == (stream.entries_spec().len() == 0));
    let retained = stream.retained_bytes();
    assert(retained as nat == stream.encoded_bytes_spec());
    assert(retained as int == automation_structures::modalities::stream_graph::stream_bytes_to(
        stream.entries_spec(), stream.entries_spec().len() as int));
    let drained = stream.is_drained();
    assert(drained == (stream.closed_spec() && stream.entries_spec().len() == 0));
    let front = stream.front();
    assert((front is Some) == (stream.entries_spec().len() > 0));
    if let Some(_head) = front {
        assert(*_head == stream.entries_spec()[0].1);
    }
    let slots = stream.slot_capacity();
    assert(slots as nat == stream.slot_limit_spec());
    let capacity = stream.byte_capacity();
    assert(capacity as nat == stream.byte_limit_spec());
    let closed = stream.is_closed();
    assert(closed == stream.closed_spec());
    let publication = stream.check_publish(bytes);
    assert((publication is Ok) == stream.publish_admitted_spec(bytes));
    assert((publication == Err(automation_structures::TypedStreamError::Closed)) == stream.closed_spec());
    assert((publication == Err(automation_structures::TypedStreamError::SlotCapacity)) == (!stream.closed_spec()
        && stream.entries_spec().len() >= stream.slot_limit_spec()));
    assert((publication == Err(automation_structures::TypedStreamError::ByteCapacity)) == (!stream.closed_spec()
        && stream.entries_spec().len() < stream.slot_limit_spec()
        && stream.encoded_bytes_spec() + bytes as nat > stream.byte_limit_spec()));
    assert((publication == Err(automation_structures::TypedStreamError::SequenceExhausted)) == (!stream.closed_spec()
        && stream.entries_spec().len() < stream.slot_limit_spec()
        && stream.encoded_bytes_spec() + bytes as nat <= stream.byte_limit_spec()
        && (stream.published_spec() >= u64::MAX as nat
            || stream.published_spec() >= P::max_ordinal())));
    let profiled = stream.check_publish_with_policy(bytes, policy);
    assert((profiled is Ok) == stream.publish_admitted_spec(bytes));
    assert((profiled == Err(automation_structures::TypedStreamError::Closed)) == stream.closed_spec());
    assert((profiled == Err(automation_structures::TypedStreamError::ItemTooLarge)) == (!stream.closed_spec()
        && policy == automation_structures::TypedStreamPublicationPolicy::ItemSizeFirst
        && bytes as nat > stream.byte_limit_spec()));
    assert((profiled == Err(automation_structures::TypedStreamError::SlotCapacity)) == (!stream.closed_spec()
        && (policy == automation_structures::TypedStreamPublicationPolicy::SlotFirst
            || bytes as nat <= stream.byte_limit_spec())
        && stream.entries_spec().len() >= stream.slot_limit_spec()));
    assert((profiled == Err(automation_structures::TypedStreamError::ByteCapacity)) == (!stream.closed_spec()
        && (policy == automation_structures::TypedStreamPublicationPolicy::SlotFirst
            || bytes as nat <= stream.byte_limit_spec())
        && stream.entries_spec().len() < stream.slot_limit_spec()
        && stream.encoded_bytes_spec() + bytes as nat > stream.byte_limit_spec()));
    assert((profiled == Err(automation_structures::TypedStreamError::SequenceExhausted)) == (!stream.closed_spec()
        && stream.entries_spec().len() < stream.slot_limit_spec()
        && stream.encoded_bytes_spec() + bytes as nat <= stream.byte_limit_spec()
        && (stream.published_spec() >= u64::MAX as nat
            || stream.published_spec() >= P::max_ordinal())));
    let receipt = stream.check_receive();
    assert((receipt is Ok) == (stream.entries_spec().len() > 0));
    assert((receipt == Err(automation_structures::TypedStreamError::Empty)) == (stream.entries_spec().len() == 0
        && !stream.closed_spec()));
    assert((receipt == Err(automation_structures::TypedStreamError::Closed)) == (stream.entries_spec().len() == 0
        && stream.closed_spec()));
    let _ = (length, empty, retained, drained, slots, capacity, closed, publication, profiled, receipt);
}

/// Shared original custody, retained charges and stale refusals cross the public boundary.
pub fn typed_fanout_preserves_shared_original_and_refusal_contracts() {
    use automation_structures::{FanoutBranch, TypedFanout};
    if let Ok(mut stream) = TypedFanout::try_new(74, 2, 5) {
        let mut original = Vec::new(); original.push(7u8);
        match stream.publish(original, 3) {
            Err(_refusal) => { assert(_refusal.value == original && stream.entries_spec().len() == 0); },
            Ok(_sequence) => {
                proof { stream.expose_custody(); }
                assert(_sequence == 0 && stream.entries_spec().len() == 1);
                let ghost before_second = stream.entries_spec();
                let mut second = Vec::new(); second.push(9u8);
                let _second_sequence = match stream.publish(second, 2) {
                    Ok(sequence) => sequence,
                    Err(_refusal) => {
                        assert(_refusal.value == second && stream.entries_spec() == before_second);
                        return;
                    },
                };
                assert(_second_sequence == 1);
                proof { stream.expose_custody(); }
                assert(stream.entries_spec().len() == 2);
                assert(stream.entries_spec()[1].0 == 1 && stream.entries_spec()[1].1.0.0 == second
                    && stream.entries_spec()[1].1.1 == 2);
                assert(stream.entries_spec()[1].1.0.1.value_spec() == 2);
                assert(stream.entries_spec()[1].1.0.1.value_spec()
                    == stream.references_spec(stream.entries_spec()[1].0));
                assert(stream.references_spec(1) == 2);
                assert(stream.entries_spec()[0].1.0.1.value_spec() == 2);
                assert(stream.entries_spec()[0].1.0.1.value_spec()
                    == stream.references_spec(stream.entries_spec()[0].0));
                assert(stream.entries_spec()[0].0 == 0 && stream.references_spec(0) == 2);
                assert(stream.queue_spec(FanoutBranch::Left) == seq![0u64, 1u64]);
                assert(stream.queue_spec(FanoutBranch::Right) == seq![0u64, 1u64]);
                let _charge = stream.retained_bytes(); assert(_charge == 5);
                let _left = stream.observe(FanoutBranch::Left);
                assert(_left is Ok && *_left->Ok_0.value == original);
                if let Ok(left) = _left {
                    let token = left.token;
                    let _consumed = stream.consume(token); assert(_consumed is Ok);
                    proof { stream.expose_custody(); }
                    assert(stream.consumed_spec(FanoutBranch::Left) == 1);
                    assert(stream.consumed_spec(FanoutBranch::Right) == 0);
                    assert(stream.queue_spec(FanoutBranch::Left).len() == 1);
                    assert(stream.entries_spec().len() == 2 && stream.references_spec(0) == 1);
                    assert(stream.entries_spec()[1].1.0.0 == second && stream.entries_spec()[1].1.1 == 2);
                    let _charge = stream.retained_bytes(); assert(_charge == 5);
                    let _right = stream.observe(FanoutBranch::Right);
                    assert(_right is Ok && *_right->Ok_0.value == original);
                    if let Ok(right) = _right {
                        let token = right.token;
                        let ghost before_close = stream.entries_spec();
                        let _closed = stream.close_input(); assert(_closed);
                        proof { stream.expose_custody(); }
                        assert(stream.consumed_spec(FanoutBranch::Left) == 1);
                        assert(stream.consumed_spec(FanoutBranch::Right) == 0);
                        assert(stream.entries_spec() == before_close);
                        assert(stream.entries_spec().len() == 2 && stream.references_spec(0) == 1);
                        let _consumed = stream.consume(token); assert(_consumed is Ok);
                        proof { stream.expose_custody(); }
                        assert(stream.consumed_spec(FanoutBranch::Right) == 1);
                        assert(stream.entries_spec().len() == 1 && stream.entries_spec()[0].0 == 1
                            && stream.entries_spec()[0].1.0.0 == second && stream.entries_spec()[0].1.1 == 2);
                        let _charge = stream.retained_bytes(); assert(_charge == 2);
                        let _left = stream.observe(FanoutBranch::Left);
                        assert(_left is Ok && *_left->Ok_0.value == second);
                        if let Ok(left) = _left {
                            let token = left.token;
                            let _consumed = stream.consume(token); assert(_consumed is Ok);
                            proof { stream.expose_custody(); }
                            assert(stream.consumed_spec(FanoutBranch::Left) == 2);
                            assert(stream.consumed_spec(FanoutBranch::Right) == 1);
                            assert(stream.entries_spec().len() == 1);
                            let ghost after_left = stream;
                            let _stale = stream.consume(token);
                            assert(_stale == Err(automation_structures::TypedFanoutError::StaleObservation) && stream == after_left);
                        }
                        let _right = stream.observe(FanoutBranch::Right);
                        assert(_right is Ok && *_right->Ok_0.value == second);
                        if let Ok(right) = _right {
                            let _consumed = stream.consume(right.token); assert(_consumed is Ok);
                            proof { stream.expose_custody(); }
                            assert(stream.consumed_spec(FanoutBranch::Left) == 2);
                            assert(stream.consumed_spec(FanoutBranch::Right) == 2);
                            assert(stream.entries_spec().len() == 0);
                        }
                        let _length = stream.retained_len(); assert(_length == 0);
                        let _charge = stream.retained_bytes(); assert(_charge == 0);
                        let _drained = stream.is_drained(); assert(_drained);
                        let _terminal = stream.observe(FanoutBranch::Left);
                        assert(_terminal == Err(automation_structures::TypedFanoutError::Closed));
                    }
                }
            },
        }
    }
}

/// A key whose ownership cannot be copied into a rebuilt registry.
pub struct OwnedRegistryKey {
    /// Exact scalar identity for this move-only witness, not a hash of a domain key.
    pub code: u64,
}

impl resource_registry::RegistryKey for OwnedRegistryKey {
    fn value_eq(&self, other: &Self) -> (equal: bool)
        ensures equal == (*self == *other),
    {
        self.code == other.code
    }
}

/// Owned entries and borrowed observations preserve the same unique-key contract.
pub fn owned_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<OwnedRegistryKey, Vec<u64>>)
    ensures
        registry.unique_mapping(),
        registry.entries@.len() == 1,
        registry.contains_key(OwnedRegistryKey { code: 7 }),
{
    let mut registry = resource_registry::ResourceRegistry::new();
    let mut first = Vec::new();
    first.push(11u64);
    registry.register(OwnedRegistryKey { code: 7 }, first);
    let observed = registry.lookup_ref(&OwnedRegistryKey { code: 7 });
    match observed {
        Some(_value) => { assert(_value@ == seq![11u64]); }
        None => { assert(false); }
    }
    let mut replacement = Vec::new();
    replacement.push(22u64);
    proof {
        resource_registry::without_key_to_remove_unique(
            registry.entries@, OwnedRegistryKey { code: 7 }, 1, 0);
    }
    registry.register(OwnedRegistryKey { code: 7 }, replacement);
    assert(registry.entries@.len() == 1);
    registry.register(OwnedRegistryKey { code: 8 }, Vec::new());
    assert(registry.entries@.len() == 2);
    proof {
        resource_registry::without_key_to_remove_unique(
            registry.entries@, OwnedRegistryKey { code: 8 }, 2, 1);
    }
    registry.deregister(OwnedRegistryKey { code: 8 });
    let observed = registry.lookup_ref(&OwnedRegistryKey { code: 7 });
    match observed {
        Some(_value) => { assert(_value@ == seq![22u64]); }
        None => { assert(false); }
    }
    registry
}

/// A downstream proof crate can instantiate the registry with a composition key.
pub fn typed_registry_is_constructible()
    -> (registry: resource_registry::ResourceRegistry<(usize, usize, u64), ()>)
    ensures registry.entries@.len() == 0,
{
    resource_registry::ResourceRegistry::new()
}

/// A downstream proof crate can construct and update the checked Buffer facade.
pub fn checked_buffer_is_constructible() -> (buffer: Buffer<u64>)
    ensures buffer.well_formed(), buffer.distinct(),
{
    let mut buffer = Buffer::new(2);
    let _accepted = buffer.push_unique(7);
    assert(_accepted);
    buffer
}

/// Preallocation and FIFO ownership compose across the published carrier boundary.
///
/// # Errors
/// Returns the Buffer storage reservation failure.
pub fn reserved_carrier_fifo(value: u64)
    -> (result: Result<Option<u64>, std::collections::TryReserveError>)
    ensures result is Ok ==> result->Ok_0 == Some(value),
{
    let mut buffer = automation_structures::connectives::buffer::Buffer::try_new(1)?;
    let _accepted = buffer.push(value);
    assert(_accepted is Ok);
    Ok(buffer.pop())
}

/// The checked facade exposes the same fallible construction without a second owner.
///
/// # Errors
/// Returns the Buffer storage reservation failure.
pub fn reserved_checked_buffer()
    -> (result: Result<Buffer<u64>, std::collections::TryReserveError>)
    ensures
        result is Ok ==> result->Ok_0.well_formed(),
        result is Ok ==> result->Ok_0.retained() == seq![7u64],
{
    let mut buffer = Buffer::try_new(1)?;
    let _accepted = buffer.push_unique(7);
    assert(_accepted);
    Ok(buffer)
}

}

verus! {
/// Reservation preserves an owned mapping on both outcomes before graph/node admission.
pub fn linear_registry_reservation_frames_owned_bindings(additional: usize) {
    use automation_structures::primitives::resource_registry::ResourceRegistry;
    let mut owner = ResourceRegistry::<u64, Vec<u8>>::new();
    let mut payload = Vec::new(); payload.push(3u8); payload.push(1u8);
    owner.register(7, payload);
    let ghost before = owner.entries@;
    let reserved = owner.try_reserve_entries(additional);
    assert(owner.entries@ == before);
    assert(owner.unique_identities());
    assert(owner.entries@[0].0 == 7);
    assert(owner.entries@[0].1@ == seq![3u8, 1u8]);
    if let Ok(()) = reserved {
        owner.register(2, Vec::<u8>::new());
        assert(owner.entries@.len() == 2);
        assert(owner.entries@[0] == before[0]);
    }
}
}

verus! {
/// A reserved selection instance has the same canonical score domain and tie behavior.
pub fn fallible_selection_is_constructible() {
    use automation_structures::primitives::competitive_selection::CompetitiveSelectionHard;
    if let Ok(mut owner) = CompetitiveSelectionHard::try_new(2) {
        assert(owner.scores@ == seq![0u64, 0u64]);
        owner.update_score(1, 1);
        assert(owner.scores@ == seq![0u64,1u64]);
        owner.evaluate();
        proof {
            assert(owner.winner_optimality());
            if let Some(winner) = owner.allocation {
                assert(winner < 2);
                assert(owner.scores@[1] <= owner.scores@[winner as int]);
                if winner == 0 { assert(false); }
            }
        }
        assert(owner.allocation == Some(1usize));
    }
}
/// State allocation cannot alter the dependency relation or admit a blocked start.
pub fn fallible_step_graph_is_constructible() {
    use automation_structures::modalities::step_graph::StepGraph;
    let mut edges = Vec::new(); edges.push((0usize, 1usize));
    if let Ok(mut owner) = StepGraph::try_new(2, edges) {
        assert(owner.edges@ == seq![(0usize,1usize)]);
        assert(StepGraph::has_predecessor_in(owner.edges@,1)) by {
            assert(owner.edges@[0].1 == 1);
        }
        assert(owner.nstate@[1] == automation_structures::StepState::NotReady);
        let _blocked = owner.start_running(1); assert(!_blocked);
        let _started = owner.start_running(0); assert(_started);
        let _completed = owner.complete_node(0); assert(_completed);
        let _ready = owner.become_ready(1); assert(_ready);
    }
}
/// Effect reservation preserves the actual assignments; actuation still records the selected resource.
pub fn fallible_actuation_is_constructible() {
    use automation_structures::primitives::actuation_pass::ActuationPass;
    let mut assignments = Vec::new(); assignments.push(Some(7u64));
    if let Ok(mut owner) = ActuationPass::try_new(assignments, 1) {
        assert(owner.effects@ == seq![Option::<u64>::None]);
        owner.actuate(0); assert(owner.effects@ == seq![Some(7u64)]);
        owner.finish(); assert(owner.complete);
    }
}
}

verus! {
/// Reserved scalar history still records exactly the completed sequence.
pub fn reserved_sequence_is_constructible() {
    use automation_structures::modalities::sequential::Sequential;
    if let Ok(mut s) = Sequential::try_new(1, 10, 0) {
        let _begun = s.begin_step(); assert(_begun);
        let _done = s.complete_step(7); assert(_done);
        assert(s.history@ == seq![7u64]);
    }
}
/// A reserved fork cannot cross its barrier before completion.
pub fn reserved_fork_is_constructible() {
    use automation_structures::modalities::fork_join::ForkJoin;
    if let Ok(mut s) = ForkJoin::try_new(1, 10, 0) {
        let _early = s.barrier(); assert(!_early);
        let _start = s.start_worker(0); assert(_start);
        let _done = s.complete_worker(0,7); assert(_done);
        let _joined = s.barrier(); assert(_joined);
        let _output = s.produce_output(); assert(_output);
        assert(s.output_snapshot@ == seq![7u64]);
    }
}
/// Reservation cannot add an audit record or change its carried result.
pub fn reserved_audit_frames_chain(additional: usize) {
    use automation_structures::primitives::audit_sink::AuditSink;
    let mut s = AuditSink::new(3);
    let _accepted = s.record(7); assert(_accepted);
    let ghost before = s;
    let _result = s.try_reserve_records(additional);
    assert(s.history_spec() == before.history_spec());
    assert(s.last_hash == before.last_hash && s.operator == before.operator
        && s.max_log_len == before.max_log_len);
}

/// Arbitrary Record preserves the primary laws and the exact accepted prefix.
pub fn audit_sink_record_exports_primary_chain_laws(
    sink: &mut automation_structures::primitives::audit_sink::AuditSink, operation: u64)
    requires old(sink).inv(),
{
    let ghost before = *sink;
    let accepted = sink.record(operation);
    assert(sink.chain_integrity());
    assert(sink.hash_consistency());
    assert(sink.hash_binds_content());
    assert(accepted == (before.log@.len() < before.max_log_len));
    if accepted {
        assert(sink.log@.len() == before.log@.len() + 1);
        assert forall|entry: int| 0 <= entry < before.log@.len() implies
            #[trigger] sink.log@[entry] == before.log@[entry] by {}
        assert(sink.log@[before.log@.len() as int].operation == operation);
        assert(sink.log@[before.log@.len() as int].prev_hash == before.last_hash);
        assert(sink.last_hash == sink.log@[before.log@.len() as int].hash);
    } else {
        assert(sink.log@ == before.log@);
        assert(sink.last_hash == before.last_hash);
        assert(sink.operator == before.operator && sink.max_log_len == before.max_log_len);
    }
}

/// A clock observation neither grants work nor changes the window anchor.
pub fn observed_clock_frames_rate_ledger() {
    use automation_structures::compositions::rate_limit::RateLimit;
    let mut r = RateLimit::new(2,5,100);
    let _accepted = r.advance_clock_to(27); assert(_accepted);
    assert(r.clock == 27 && r.window_start == 0 && r.budget.allocated == 0);
    let ghost before = r;
    let _backwards = r.advance_clock_to(26); assert(!_backwards); assert(r == before);
}
}

/// Shared pure domain adapters and their external proof witnesses.
pub mod domains;

verus! {
/// Membership and domain admission are observable in both resource profiles.
pub proof fn typed_allocation_exports_membership<K: automation_structures::KeyIdentity, V,
    P: automation_structures::AllocationDomain<K, V>>(
    owner: &automation_structures::TypedAllocation<K, V, P>, entry: int,
)
    requires owner.inv(), 0 <= entry < owner.entries_spec().len(),
    ensures
        resource_registry::unique_mapping_entries(resource_registry::identity_entries(owner.entries_spec())),
        owner.entries_spec()[entry].1.1@.len() == owner.budgets_spec().len(),
        owner.budgets_spec().len() > 0 ==> owner.entries_spec()[entry].1.1@[0] == 1,
        owner.domain_spec().admits(owner.entries_spec()[entry].0, owner.entries_spec()[entry].1.0, owner.entries_spec()[entry].1.1@),
{
    owner.expose_coupling();
}

/// Every resource observation comes from its actual scoped Budget owner.
pub proof fn typed_allocation_exports_resources<K: automation_structures::KeyIdentity, V,
    P: automation_structures::AllocationDomain<K, V>>(
    owner: &automation_structures::TypedAllocation<K, V, P>, dimension: int,
)
    requires owner.inv(), 0 <= dimension < owner.budgets_spec().len(),
    ensures
        resource_registry::unique_mapping_entries(resource_registry::identity_entries(owner.budgets_spec())),
        owner.budgets_spec()[dimension].0 == dimension,
        owner.budgets_spec()[dimension].1.safety_invariant(),
        owner.budgets_spec()[dimension].1.reserved == 0,
        owner.budgets_spec()[dimension].1.pending_eviction == 0,
        owner.budgets_spec()[dimension].1.allocated as int
            == automation_structures::compositions::allocation_snapshot::typed_charge_to(owner.entries_spec(), owner.entries_spec().len() as int, dimension),
{
    owner.expose_coupling();
}

/// Sealing retains the same membership, domain and resource facts.
pub proof fn sealed_typed_allocation_exports_coupling<K: automation_structures::KeyIdentity, V,
    P: automation_structures::AllocationDomain<K, V>>(
    owner: &automation_structures::SealedTypedAllocation<K, V, P>, entry: int, dimension: int,
)
    requires owner.inv(), 0 <= entry < owner.entries_spec().len(), 0 <= dimension < owner.budgets_spec().len(),
    ensures
        resource_registry::unique_mapping_entries(resource_registry::identity_entries(owner.entries_spec())),
        resource_registry::unique_mapping_entries(resource_registry::identity_entries(owner.budgets_spec())),
        owner.entries_spec()[entry].1.1@.len() == owner.budgets_spec().len(),
        owner.entries_spec()[entry].1.1@[0] == 1,
        owner.domain_spec().admits(owner.entries_spec()[entry].0, owner.entries_spec()[entry].1.0, owner.entries_spec()[entry].1.1@),
        owner.budgets_spec()[dimension].0 == dimension,
        owner.budgets_spec()[dimension].1.safety_invariant(),
        owner.budgets_spec()[dimension].1.reserved == 0,
        owner.budgets_spec()[dimension].1.pending_eviction == 0,
        owner.budgets_spec()[dimension].1.allocated as int
            == automation_structures::compositions::allocation_snapshot::typed_charge_to(owner.entries_spec(), owner.entries_spec().len() as int, dimension),
{
    owner.expose_coupling();
}
}

verus! {
/// The quota-free profile exports exact batch custody and sealed membership.
pub fn unbudgeted_allocation_exports_exact_batch<K: automation_structures::KeyIdentity, V,
    P: automation_structures::AllocationDomain<K,V>>(domain: P, items: Vec<(K,(V,Vec<u64>))>) {
    let mut owner = automation_structures::TypedAllocation::unbudgeted(domain);
    assert(owner.entries_spec().len() == 0 && owner.budgets_spec().len() == 0);
    match owner.prepare_batch(items) {
        Ok(prepared) => {
            assert(prepared.items_spec() == items@);
            prepared.commit();
            assert(owner.entries_spec() =~= items@);
            assert(owner.budgets_spec().len() == 0);
            let sealed = owner.seal();
            assert(sealed.entries_spec() == items@ && sealed.budgets_spec().len() == 0);
            assert(sealed.domain_spec() == domain);
            proof {
                sealed.expose_coupling();
                assert(resource_registry::unique_mapping_entries(resource_registry::identity_entries(sealed.entries_spec())));
                assert forall|entry: int| 0 <= entry < items@.len() implies
                    (#[trigger] items@[entry]).1.1@.len() == 0
                    && domain.admits(items@[entry].0, items@[entry].1.0, items@[entry].1.1@) by {}
            }
            let _length = sealed.len(); assert(_length == items@.len());
            let _outside = sealed.budget(0); assert(_outside is None);
        },
        Err(_refused) => {
            assert(_refused.items == items);
            assert(owner.entries_spec().len() == 0 && owner.budgets_spec().len() == 0);
        },
    }
}
}

verus! {
/// The public owning profile preserves every input on refusal and exports both joint views.
///
/// # Errors
/// Returns graph/domain inputs unchanged on topology, handle or storage refusal.
pub fn owning_adjacency_is_constructible<H: Copy + automation_structures::value_eq::ValueEq,
    D: automation_structures::EdgeHandleDomain<H>,
    P: resource_registry::RegistryPredicate<automation_structures::compositions::relationship_graph::EdgeKey, ()>>(
    graph: automation_structures::RelationshipGraph, domain: D, predicate: P,
) -> (result: automation_structures::MaterializationResult<H, D, P>)
    ensures
        result is Ok ==> result->Ok_0.inv()
            && result->Ok_0.edges_spec() == graph.bindings()
            && result->Ok_0.node_universe() == graph.node_universe()
            && result->Ok_0.handle_domain_spec() == domain
            && result->Ok_0.predicate_spec() == predicate,
        result matches Err((_, returned, returned_domain, returned_predicate)) ==>
            returned.bindings() == graph.bindings()
            && returned.node_universe() == graph.node_universe()
            && returned.weight_ceiling() == graph.weight_ceiling()
            && returned_domain == domain && returned_predicate == predicate,
{
    let result = graph.materialize(domain, predicate);
    if let Ok(view) = &result {
        proof {
            view.expose_adjacency(automation_structures::EdgeDirection::Outgoing);
            view.expose_adjacency(automation_structures::EdgeDirection::Incoming);
            assert(automation_structures::connectives::ordering_pass::inverse_permutation(view.positions_spec(automation_structures::EdgeDirection::Outgoing),
                view.inverse_spec(automation_structures::EdgeDirection::Outgoing)));
            assert(automation_structures::connectives::ordering_pass::inverse_permutation(view.positions_spec(automation_structures::EdgeDirection::Incoming),
                view.inverse_spec(automation_structures::EdgeDirection::Incoming)));
        }
        let _outside = view.incident(view.num_nodes(), automation_structures::EdgeDirection::Outgoing);
        assert(_outside is None);
    }
    result
}

/// Exact exported boundaries characterize selected incidence, not just array lengths.
pub proof fn owning_adjacency_span_membership<H: Copy + automation_structures::value_eq::ValueEq,
    D: automation_structures::EdgeHandleDomain<H>,
    P: resource_registry::RegistryPredicate<automation_structures::compositions::relationship_graph::EdgeKey, ()>>(
    view: &automation_structures::MaterializedAdjacency<H, D, P>,
    node: usize, rank: int, direction: automation_structures::EdgeDirection,
)
    requires view.inv(), node < view.node_universe(), 0 <= rank < view.edges_spec().len(),
    ensures
        (view.offsets_spec(direction)[node as int] <= rank
            && rank < view.offsets_spec(direction)[node as int + 1]) <==>
        (view.predicate_spec().selected(view.edges_spec()[view.positions_spec(direction)[rank] as int].0, ())
            && automation_structures::compositions::relationship_graph::incidence_endpoint(
                view.edges_spec()[view.positions_spec(direction)[rank] as int].0, direction) == node),
{
    view.expose_adjacency(direction);
    assert(automation_structures::compositions::relationship_graph::incidence_boundary(
        view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
        node as int, view.offsets_spec(direction)[node as int]));
    assert(automation_structures::compositions::relationship_graph::incidence_boundary(
        view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
        node as int + 1, view.offsets_spec(direction)[node as int + 1]));
    assert((rank < view.offsets_spec(direction)[node as int]) <==>
        automation_structures::compositions::relationship_graph::incidence_before(
            view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
            node as int, rank));
    assert((rank < view.offsets_spec(direction)[node as int + 1]) <==>
        automation_structures::compositions::relationship_graph::incidence_before(
            view.edges_spec(), view.positions_spec(direction), view.predicate_spec(), direction,
            node as int + 1, rank));
}

/// A representation absent from every retained handle is rejected even if its ordinal decodes.
pub fn owning_adjacency_foreign_handle<H: Copy + automation_structures::value_eq::ValueEq,
    D: automation_structures::EdgeHandleDomain<H>,
    P: resource_registry::RegistryPredicate<automation_structures::compositions::relationship_graph::EdgeKey, ()>>(
    view: &automation_structures::MaterializedAdjacency<H, D, P>, handle: H,
)
    requires view.inv(), forall|i: int| 0 <= i < view.original_handles_spec().len() ==>
        #[trigger] view.original_handles_spec()[i] != handle,
{
    proof {
        view.expose_handle_resolution(handle);
        if let Some(original) = view.handle_domain_spec().ordinal_spec(handle) {
            if original < view.original_handles_spec().len() {
                assert(view.original_handles_spec()[original as int] != handle);
            }
        }
        assert(view.resolve_spec(handle) is None);
    }
    let _edge = view.edge(&handle); assert(_edge is None);
    let _outgoing = view.rank_of(&handle, automation_structures::EdgeDirection::Outgoing);
    let _incoming = view.rank_of(&handle, automation_structures::EdgeDirection::Incoming);
    assert(_outgoing is None && _incoming is None);
}

/// Consumer construction witness: temporary issuance composes existing owners.
/// The enclosing identity Registry must bind this permanent listener, Counter and
/// Buffer to one identity for its lifetime. This does not strengthen Signal.
pub fn stable_listener_temporary_registration(
    signal: &mut automation_structures::SummarySignal<u64>,
    listener: automation_structures::SignalListener,
    generation: &mut automation_structures::connectives::counter::Counter,
    temporary: &mut Buffer<u64>, observed_head: usize,
) -> (accepted: bool)
    requires old(signal).inv(), old(signal).registered_spec(listener),
        old(temporary).well_formed(), old(temporary).admitted_capacity() == 1,
    ensures final(signal).inv(), final(temporary).well_formed(), final(temporary).admitted_capacity() == 1,
        final(signal).scope_spec() == old(signal).scope_spec(),
        final(signal).history_spec() == old(signal).history_spec(),
        final(signal).value_spec() == old(signal).value_spec(),
        final(signal).issued_spec() == old(signal).issued_spec(),
        final(signal).listener_limit_spec() == old(signal).listener_limit_spec(),
        final(signal).change_limit_spec() == old(signal).change_limit_spec(),
        forall|other: automation_structures::SignalListener|
            #[trigger] final(signal).registered_spec(other) == old(signal).registered_spec(other),
        accepted == (observed_head == old(signal).history_spec().len()
            && old(temporary).retained().len() == 0
            && old(generation).value_spec() < u64::MAX as nat),
        !accepted ==> final(signal).listeners_spec() == old(signal).listeners_spec()
            && final(generation).value_spec() == old(generation).value_spec()
            && final(temporary).retained() == old(temporary).retained(),
        accepted ==> final(signal).caught_up_spec(listener)
            && final(generation).value_spec() == old(generation).value_spec() + 1
            && final(temporary).retained().len() == 1
            && final(temporary).retained()[0] as nat == final(generation).value_spec(),
{
    if signal.change_count() != observed_head || !temporary.is_empty()
        || !generation.can_increment() { return false; }
    match signal.notify(listener) {
        Ok(_) => {},
        Err(_) => { proof { assert(false); } return false; },
    }
    let advanced = generation.try_increment();
    assert(advanced);
    let issued = generation.value();
    let retained = temporary.push(issued);
    assert(retained is Ok);
    let _ = (advanced, retained);
    true
}

/// One identity's refusal cannot consume another identity's generation capacity.
/// Arbitrary valid Signal issuance, including global exhaustion, is unchanged.
pub fn stable_listener_independent_generation_capacity(
    signal: &mut automation_structures::SummarySignal<u64>,
    first_listener: automation_structures::SignalListener,
    second_listener: automation_structures::SignalListener,
)
    requires old(signal).inv(), old(signal).registered_spec(first_listener),
        old(signal).registered_spec(second_listener),
        first_listener.generation_spec() != second_listener.generation_spec(),
{
    let mut exhausted = automation_structures::connectives::counter::Counter::new(u64::MAX);
    let mut available = automation_structures::connectives::counter::Counter::new(0);
    let mut first = Buffer::<u64>::new(1); let mut second = Buffer::<u64>::new(1);
    let head = signal.change_count(); let ghost before = *signal;
    let refused = stable_listener_temporary_registration(signal, first_listener, &mut exhausted, &mut first, head);
    assert(!refused && exhausted.value_spec() == u64::MAX && first.retained().len() == 0);
    assert(signal.listeners_spec() == before.listeners_spec());
    let admitted = stable_listener_temporary_registration(signal, second_listener, &mut available, &mut second, head);
    assert(admitted && available.value_spec() == 1 && second.retained() == seq![1u64]);
    assert(signal.issued_spec() == before.issued_spec());
    let _ = (refused, admitted);
}

pub fn checked_linear_stream_exports_its_owner_invariant<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    assert(graph.state_spec().inv());
}

pub fn checked_linear_stream_exports_source_count_bound<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    let _count = graph.ingested();
    let _bound = graph.max_inputs();
    assert(_count <= _bound);
}

pub fn checked_linear_stream_exports_sink_count_bound<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    let _count = graph.emitted();
    let _bound = graph.max_inputs();
    assert(_count <= _bound);
}

pub fn checked_linear_stream_exports_first_queue_bound<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    proof {
        graph.state_spec().q1.expose_capacity_bound();
    }
    let _length = graph.first_queue_len();
    assert(_length <= _capacity);
}

pub fn checked_linear_stream_exports_second_queue_bound<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    proof {
        graph.state_spec().q2.expose_capacity_bound();
    }
    let _length = graph.second_queue_len();
    assert(_length <= _capacity);
}

pub fn checked_linear_stream_exports_third_queue_bound<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    proof {
        graph.state_spec().q3.expose_capacity_bound();
    }
    let _length = graph.third_queue_len();
    assert(_length <= _capacity);
}

pub fn checked_linear_stream_exports_state_enabledness<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    let _enabled = graph.has_enabled_action();
    assert(_enabled);
}

/// Arbitrary default configurations retain each initialization and refusal law.
pub fn checked_linear_stream_default_construction(
    stages: usize, capacity: usize, inputs: usize, domain: u64)
{
    use automation_structures::StreamGraph;
    let _result = StreamGraph::new(stages, capacity, inputs, domain);
    assert(_result is Ok ==> _result->Ok_0.config_spec().0 == stages);
    assert(_result is Ok ==> _result->Ok_0.config_spec().1 == capacity);
    assert(_result is Ok ==> _result->Ok_0.config_spec().2 == inputs);
    assert(_result is Ok ==> _result->Ok_0.config_spec().3 == domain);
    assert(_result is Ok ==> _result->Ok_0.first_queue_spec() == Seq::<u64>::empty());
    assert(_result is Ok ==> _result->Ok_0.second_queue_spec() == Seq::<u64>::empty());
    assert(_result is Ok ==> _result->Ok_0.third_queue_spec() == Seq::<u64>::empty());
    assert(_result is Ok ==> _result->Ok_0.ingested_spec() == 0);
    assert(_result is Ok ==> _result->Ok_0.emitted_spec() == 0);
    assert(_result is Ok ==> (stages == 3 || stages == 4));
    assert(_result is Ok ==> capacity > 0);
    assert(_result is Ok ==> domain > 0);
    assert((stages == 3 || stages == 4) && capacity > 0 && domain > 0
        ==> _result is Ok);
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::UnsupportedChainLength))
        <==> (stages != 3 && stages != 4));
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::ZeroCapacity))
        <==> ((stages == 3 || stages == 4) && capacity == 0));
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::EmptyRecordDomain))
        <==> ((stages == 3 || stages == 4) && capacity > 0 && domain == 0));
}

/// Valid generic configurations may still encounter physical reservation refusal.
pub fn checked_linear_stream_fallible_construction<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    stages: usize, capacity: usize, inputs: usize, domain: u64)
{
    use automation_structures::StreamGraph;
    let _result = StreamGraph::<S>::try_with_storage(stages, capacity, inputs, domain);
    assert(_result is Ok ==> _result->Ok_0.config_spec().0 == stages);
    assert(_result is Ok ==> _result->Ok_0.config_spec().1 == capacity);
    assert(_result is Ok ==> _result->Ok_0.config_spec().2 == inputs);
    assert(_result is Ok ==> _result->Ok_0.config_spec().3 == domain);
    assert(_result is Ok ==> _result->Ok_0.first_queue_spec() == Seq::<u64>::empty());
    assert(_result is Ok ==> _result->Ok_0.second_queue_spec() == Seq::<u64>::empty());
    assert(_result is Ok ==> _result->Ok_0.third_queue_spec() == Seq::<u64>::empty());
    assert(_result is Ok ==> _result->Ok_0.ingested_spec() == 0);
    assert(_result is Ok ==> _result->Ok_0.emitted_spec() == 0);
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::UnsupportedChainLength))
        <==> (stages != 3 && stages != 4));
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::ZeroCapacity))
        <==> ((stages == 3 || stages == 4) && capacity == 0));
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::EmptyRecordDomain))
        <==> ((stages == 3 || stages == 4) && capacity > 0 && domain == 0));
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::StorageUnavailable))
        ==> (stages == 3 || stages == 4));
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::StorageUnavailable)) ==> capacity > 0);
    assert(matches!(_result, Err(automation_structures::StreamGraphBuildError::StorageUnavailable)) ==> domain > 0);
}

/// Each executable observation is tied to the same checked owner's projection.
pub fn checked_linear_stream_observations<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _stages = graph.chain_length();
    assert(_stages == graph.config_spec().0);
    let _capacity = graph.capacity();
    assert(_capacity == graph.config_spec().1);
    let _inputs = graph.max_inputs();
    assert(_inputs == graph.config_spec().2);
    let _domain = graph.record_domain_size();
    assert(_domain == graph.config_spec().3);
    let _ingested = graph.ingested();
    assert(_ingested == graph.ingested_spec());
    let _emitted = graph.emitted();
    assert(_emitted == graph.emitted_spec());
    let _first = graph.first_queue_len();
    assert(_first == graph.first_queue_spec().len());
    let _second = graph.second_queue_len();
    assert(_second == graph.second_queue_spec().len());
    let _third = graph.third_queue_len();
    assert(_third == graph.third_queue_spec().len());
}

/// The exported carrier projections agree with the one retained owner.
pub fn checked_linear_stream_owner_projection<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _capacity = graph.capacity();
    assert(graph.config_spec().0 == graph.state_spec().chain_length);
    assert(graph.config_spec().1 == graph.state_spec().q1.capacity);
    assert(graph.config_spec().2 == graph.state_spec().max_inputs);
    assert(graph.config_spec().3 == graph.state_spec().record_domain_size);
    assert(graph.ingested_spec() == graph.state_spec().ingested.value_spec());
    assert(graph.emitted_spec() == graph.state_spec().emitted.value_spec());
    assert(graph.first_queue_spec() == graph.state_spec().q1.values@);
    assert(graph.second_queue_spec() == graph.state_spec().q2.values@);
    assert(graph.third_queue_spec() == graph.state_spec().q3.values@);
}

/// Conservation is obtained from count/length exports without another invariant export.
pub fn checked_linear_stream_count_conservation<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _ingested = graph.ingested();
    let _emitted = graph.emitted();
    let _first = graph.first_queue_len();
    let _second = graph.second_queue_len();
    let _third = graph.third_queue_len();
    assert(_ingested as nat == _first as nat + _second as nat + _third as nat + _emitted as nat);
}

/// Done has four necessary conditions and their joint sufficiency.
pub fn checked_linear_stream_terminal_decision<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _done = graph.is_done();
    assert(_done ==> graph.ingested_spec() == graph.config_spec().2);
    assert(_done ==> graph.first_queue_spec().len() == 0);
    assert(_done ==> graph.second_queue_spec().len() == 0);
    assert(_done ==> graph.third_queue_spec().len() == 0);
    assert(graph.ingested_spec() == graph.config_spec().2
        && graph.first_queue_spec().len() == 0
        && graph.second_queue_spec().len() == 0
        && graph.third_queue_spec().len() == 0 ==> _done);
}

/// Enabledness observes the declared transition disjunction, not scheduler progress.
pub fn checked_linear_stream_enabled_decision<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &automation_structures::StreamGraph<S>)
{
    let _enabled = graph.has_enabled_action();
    assert(_enabled ==> (
        (graph.ingested_spec() < graph.config_spec().2
            && graph.first_queue_spec().len() < graph.config_spec().1)
        || (graph.first_queue_spec().len() > 0 && graph.second_queue_spec().len() < graph.config_spec().1)
        || (graph.config_spec().0 == 3 && graph.second_queue_spec().len() > 0)
        || (graph.config_spec().0 == 4 && graph.second_queue_spec().len() > 0
            && graph.third_queue_spec().len() < graph.config_spec().1)
        || (graph.config_spec().0 == 4 && graph.third_queue_spec().len() > 0)
        || (graph.ingested_spec() == graph.config_spec().2
            && graph.first_queue_spec().len() == 0 && graph.second_queue_spec().len() == 0
            && graph.third_queue_spec().len() == 0)));
    assert(graph.ingested_spec() < graph.config_spec().2
        && graph.first_queue_spec().len() < graph.config_spec().1 ==> _enabled);
    assert(graph.first_queue_spec().len() > 0
        && graph.second_queue_spec().len() < graph.config_spec().1 ==> _enabled);
    assert(graph.config_spec().0 == 3 && graph.second_queue_spec().len() > 0 ==> _enabled);
    assert(graph.config_spec().0 == 4 && graph.second_queue_spec().len() > 0
        && graph.third_queue_spec().len() < graph.config_spec().1 ==> _enabled);
    assert(graph.config_spec().0 == 4 && graph.third_queue_spec().len() > 0 ==> _enabled);
    assert(graph.ingested_spec() == graph.config_spec().2
        && graph.first_queue_spec().len() == 0 && graph.second_queue_spec().len() == 0
        && graph.third_queue_spec().len() == 0 ==> _enabled);
}

/// Source admission, successful updates and refusal frames are separate assertions.
pub fn checked_linear_stream_ingest_contract<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &mut automation_structures::StreamGraph<S>, value: u64)
{
    let ghost before = *graph;
    let _accepted = graph.ingest(value);
    assert(_accepted ==> value < before.config_spec().3);
    assert(_accepted ==> before.ingested_spec() < before.config_spec().2);
    assert(_accepted ==> before.first_queue_spec().len() < before.config_spec().1);
    assert(value < before.config_spec().3 && before.ingested_spec() < before.config_spec().2
        && before.first_queue_spec().len() < before.config_spec().1 ==> _accepted);
    assert(graph.config_spec().0 == before.config_spec().0);
    assert(graph.config_spec().1 == before.config_spec().1);
    assert(graph.config_spec().2 == before.config_spec().2);
    assert(graph.config_spec().3 == before.config_spec().3);
    assert(_accepted ==> graph.first_queue_spec() == before.first_queue_spec().push(value));
    assert(!_accepted ==> graph.first_queue_spec() == before.first_queue_spec());
    assert(graph.second_queue_spec() == before.second_queue_spec());
    assert(graph.third_queue_spec() == before.third_queue_spec());
    assert(_accepted ==> graph.ingested_spec() == before.ingested_spec() + 1);
    assert(!_accepted ==> graph.ingested_spec() == before.ingested_spec());
    assert(graph.emitted_spec() == before.emitted_spec());
}

/// The first internal transfer preserves FIFO order and every unselected field.
pub fn checked_linear_stream_first_transfer_contract<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &mut automation_structures::StreamGraph<S>)
{
    let ghost before = *graph;
    let _accepted = graph.advance_first();
    assert(_accepted ==> before.first_queue_spec().len() > 0);
    assert(_accepted ==> before.second_queue_spec().len() < before.config_spec().1);
    assert(before.first_queue_spec().len() > 0
        && before.second_queue_spec().len() < before.config_spec().1 ==> _accepted);
    assert(graph.config_spec().0 == before.config_spec().0);
    assert(graph.config_spec().1 == before.config_spec().1);
    assert(graph.config_spec().2 == before.config_spec().2);
    assert(graph.config_spec().3 == before.config_spec().3);
    assert(_accepted ==> graph.first_queue_spec() == before.first_queue_spec().skip(1));
    assert(!_accepted ==> graph.first_queue_spec() == before.first_queue_spec());
    assert(_accepted ==> graph.second_queue_spec()
        == before.second_queue_spec().push(before.first_queue_spec()[0]));
    assert(!_accepted ==> graph.second_queue_spec() == before.second_queue_spec());
    assert(graph.third_queue_spec() == before.third_queue_spec());
    assert(graph.ingested_spec() == before.ingested_spec());
    assert(graph.emitted_spec() == before.emitted_spec());
}

/// The optional transfer requires its four-stage profile and preserves its frame.
pub fn checked_linear_stream_second_transfer_contract<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &mut automation_structures::StreamGraph<S>)
{
    let ghost before = *graph;
    let _accepted = graph.advance_second();
    assert(_accepted ==> before.config_spec().0 == 4);
    assert(_accepted ==> before.second_queue_spec().len() > 0);
    assert(_accepted ==> before.third_queue_spec().len() < before.config_spec().1);
    assert(before.config_spec().0 == 4 && before.second_queue_spec().len() > 0
        && before.third_queue_spec().len() < before.config_spec().1 ==> _accepted);
    assert(graph.config_spec().0 == before.config_spec().0);
    assert(graph.config_spec().1 == before.config_spec().1);
    assert(graph.config_spec().2 == before.config_spec().2);
    assert(graph.config_spec().3 == before.config_spec().3);
    assert(graph.first_queue_spec() == before.first_queue_spec());
    assert(_accepted ==> graph.second_queue_spec() == before.second_queue_spec().skip(1));
    assert(!_accepted ==> graph.second_queue_spec() == before.second_queue_spec());
    assert(_accepted ==> graph.third_queue_spec()
        == before.third_queue_spec().push(before.second_queue_spec()[0]));
    assert(!_accepted ==> graph.third_queue_spec() == before.third_queue_spec());
    assert(graph.ingested_spec() == before.ingested_spec());
    assert(graph.emitted_spec() == before.emitted_spec());
}

/// Sink selection, returned head, successful removal and refusal frames stay distinct.
pub fn checked_linear_stream_consume_contract<S: automation_structures::connectives::buffer::BufferLayout<u64>>(
    graph: &mut automation_structures::StreamGraph<S>)
{
    let ghost before = *graph;
    let _value = graph.consume();
    assert(before.config_spec().0 == 3 && _value is Some ==> before.second_queue_spec().len() > 0);
    assert(before.config_spec().0 == 3 && before.second_queue_spec().len() > 0 ==> _value is Some);
    assert(before.config_spec().0 == 3 && _value is Some ==> _value->Some_0 == before.second_queue_spec()[0]);
    assert(before.config_spec().0 != 3 && _value is Some ==> before.third_queue_spec().len() > 0);
    assert(before.config_spec().0 != 3 && before.third_queue_spec().len() > 0 ==> _value is Some);
    assert(before.config_spec().0 != 3 && _value is Some ==> _value->Some_0 == before.third_queue_spec()[0]);
    assert(graph.config_spec().0 == before.config_spec().0);
    assert(graph.config_spec().1 == before.config_spec().1);
    assert(graph.config_spec().2 == before.config_spec().2);
    assert(graph.config_spec().3 == before.config_spec().3);
    assert(graph.first_queue_spec() == before.first_queue_spec());
    assert(_value is Some && before.config_spec().0 == 3
        ==> graph.second_queue_spec() == before.second_queue_spec().skip(1));
    assert(_value is None || before.config_spec().0 != 3
        ==> graph.second_queue_spec() == before.second_queue_spec());
    assert(_value is Some && before.config_spec().0 == 4
        ==> graph.third_queue_spec() == before.third_queue_spec().skip(1));
    assert(_value is None || before.config_spec().0 != 4
        ==> graph.third_queue_spec() == before.third_queue_spec());
    assert(graph.ingested_spec() == before.ingested_spec());
    assert(_value is Some ==> graph.emitted_spec() == before.emitted_spec() + 1);
    assert(_value is None ==> graph.emitted_spec() == before.emitted_spec());
}

pub fn checked_fork_join_exports_initialization(workers: usize, domain: u64, initial: u64)
    requires domain > 0, initial < domain,
{
    let result = automation_structures::ForkJoin::new(workers, domain, initial);
    assert(result is Ok);
    if let Ok(_execution) = result {
        assert(_execution.state_spec().inv());
        assert(_execution.state_spec().wstate@.len() == workers);
        assert(_execution.state_spec().wvalue@.len() == workers);
        assert(_execution.state_spec().phase == automation_structures::ForkJoinPhase::Fork);
        assert(!_execution.state_spec().output_ready);
        assert forall|i: int| 0 <= i < workers implies #[trigger] _execution.state_spec().wstate@[i]
            == automation_structures::WorkerState::Ready by {}
        assert forall|i: int| 0 <= i < workers implies #[trigger] _execution.state_spec().wvalue@[i] == initial by {}
        assert forall|i: int| 0 <= i < workers implies #[trigger] _execution.state_spec().snapshot_spec()[i] == initial by {}
    }
}

pub fn checked_fork_join_exports_worker_count(execution: &automation_structures::ForkJoin) {
    let _count = execution.len();
    assert(_count == execution.state_spec().wstate@.len());
}
pub fn checked_fork_join_exports_empty(execution: &automation_structures::ForkJoin) {
    let _empty = execution.is_empty();
    assert(_empty == (execution.state_spec().wstate@.len() == 0));
}
pub fn checked_fork_join_exports_completion(execution: &automation_structures::ForkJoin) {
    let _complete = execution.all_complete();
    assert(_complete == execution.state_spec().all_complete());
    assert(execution.state_spec().inv());
}
pub fn checked_fork_join_exports_phase(execution: &automation_structures::ForkJoin) {
    let _phase = execution.phase();
    assert(_phase == execution.state_spec().phase);
}
pub fn checked_fork_join_exports_readiness(execution: &automation_structures::ForkJoin) {
    let _ready = execution.output_ready();
    assert(_ready == execution.state_spec().output_ready);
}
pub fn checked_fork_join_exports_worker_state(execution: &automation_structures::ForkJoin, worker: usize) {
    let _state = execution.worker_state(worker);
    assert(_state == automation_structures::modalities::fork_join::worker_at(execution.state_spec().wstate@, worker as int));
}
pub fn checked_fork_join_exports_worker_value(execution: &automation_structures::ForkJoin, worker: usize) {
    let _value = execution.worker_value(worker);
    assert(_value == if worker < execution.state_spec().wvalue@.len()
        { Some(execution.state_spec().wvalue@[worker as int]) } else { None });
}
pub fn checked_fork_join_exports_output(execution: &automation_structures::ForkJoin, worker: usize) {
    let _value = execution.output(worker);
    assert(_value == if execution.state_spec().output_ready && worker < execution.state_spec().wvalue@.len()
        { Some(execution.state_spec().snapshot_spec()[worker as int]) } else { None });
}
pub fn checked_fork_join_exports_start(execution: &mut automation_structures::ForkJoin, worker: usize) {
    let ghost before = execution.state_spec();
    let _accepted = execution.start_worker(worker);
    assert(automation_structures::modalities::fork_join::start_worker_action(before.wstate@,
        execution.state_spec().wstate@, before.phase, worker as int, true, _accepted));
    assert(execution.state_spec().wvalue@ == before.wvalue@);
    assert(execution.state_spec().snapshot_spec() == before.snapshot_spec());
    assert(execution.state_spec().phase == before.phase);
}
pub fn checked_fork_join_exports_complete(execution: &mut automation_structures::ForkJoin, worker: usize, value: u64) {
    let ghost before = execution.state_spec();
    let _accepted = execution.complete_worker(worker, value);
    assert(automation_structures::modalities::fork_join::complete_worker_action(before.wstate@,
        execution.state_spec().wstate@, before.phase, worker as int, true, value < before.value_domain_size, _accepted));
    assert(execution.state_spec().wvalue@ == if _accepted { before.wvalue@.update(worker as int, value) } else { before.wvalue@ });
    assert(execution.state_spec().snapshot_spec() == before.snapshot_spec());
    assert(execution.state_spec().phase == before.phase);
}
pub fn checked_fork_join_exports_barrier(execution: &mut automation_structures::ForkJoin) {
    let ghost before = execution.state_spec();
    let _accepted = execution.barrier();
    assert(automation_structures::modalities::fork_join::barrier_action(before.phase,
        execution.state_spec().phase, true, before.all_complete(), _accepted));
    assert(execution.state_spec().wstate@ == before.wstate@);
    assert(execution.state_spec().wvalue@ == before.wvalue@);
    assert(execution.state_spec().snapshot_spec() == before.snapshot_spec());
}
pub fn checked_fork_join_exports_publication(execution: &mut automation_structures::ForkJoin) {
    let ghost before = execution.state_spec();
    let _accepted = execution.produce_output();
    assert(automation_structures::modalities::fork_join::produce_output_action(before.phase,
        execution.state_spec().phase, true, _accepted));
    assert(execution.state_spec().wstate@ == before.wstate@);
    assert(execution.state_spec().wvalue@ == before.wvalue@);
    assert(_accepted ==> execution.state_spec().snapshot_spec() == before.wvalue@);
    assert(!_accepted ==> execution.state_spec().snapshot_spec() == before.snapshot_spec());
}

/// Fixed Signal exports delivery disjointness for every admitted listener.
pub proof fn fixed_signal_exports_delivery_disjointness(
    signal: &automation_structures::compositions::signal::Signal, listener: int)
    requires signal.inv(), 0 <= listener < signal.num_listeners,
    ensures !(signal.pending_spec(listener) && signal.notified_spec(listener)),
{
}

/// Primary notification provenance includes the initial empty delivery state.
pub proof fn fixed_signal_exports_notification_provenance(
    signal: &automation_structures::compositions::signal::Signal, listener: int)
    requires signal.inv(), 0 <= listener < signal.num_listeners,
    ensures signal.audit.log@.len() == 0 ==>
        !signal.pending_spec(listener) && !signal.notified_spec(listener),
        signal.audit.log@.len() > 0 ==> signal.pending_spec(listener) || signal.notified_spec(listener),
{
}

/// A real change restarts the same fixed listener universe through Record.
pub fn fixed_signal_change_restarts_notifications(
    signal: &mut automation_structures::compositions::signal::Signal, value: u64)
    requires old(signal).inv(), value < old(signal).num_values,
        value != old(signal).current_value_spec(),
        old(signal).audit.log@.len() < old(signal).audit.max_log_len,
{
    let ghost head = signal.audit.log@.len();
    let ghost cursors = signal.cursors@;
    signal.set_value(value);
    assert(signal.current_value_spec() == value);
    assert forall|listener: int| 0 <= listener < signal.num_listeners implies
        signal.pending_spec(listener) && !signal.notified_spec(listener) by {
        assert(signal.cursors@[listener] == cursors[listener]);
        assert(cursors[listener].position <= head);
    }
}

/// One notification preserves another listener's pending/notified projection.
pub fn fixed_signal_notification_frames_other_listener(
    signal: &mut automation_structures::compositions::signal::Signal,
    listener: usize, other: usize)
    requires old(signal).inv(), listener < old(signal).num_listeners,
        other < old(signal).num_listeners, listener != other,
        old(signal).pending_spec(listener as int),
{
    let _ = other;
    let ghost before = *signal;
    signal.notify_listener(listener);
    assert(!signal.pending_spec(listener as int) && signal.notified_spec(listener as int));
    assert(signal.pending_spec(other as int) == before.pending_spec(other as int));
    assert(signal.notified_spec(other as int) == before.notified_spec(other as int));
    assert(signal.current_value_spec() == before.current_value_spec());
}

/// Arbitrary admitted Update preserves the primary phase, history and state-edge laws.
pub fn governor_update_exports_primary_laws<H: automation_structures::primitives::convergence_governor_phase_aware::GovernorHistory>(
    governor: &mut automation_structures::primitives::convergence_governor_phase_aware::ConvergenceGovernorPhaseAware<H>,
    delta: u64)
    requires old(governor).inv(), delta <= old(governor).max_delta,
{
    let ghost before = *governor;
    let _average = governor.update(delta);
    proof {
        use automation_structures::primitives::convergence_governor_phase_aware::{
            ConvergenceGovernorPhaseAware, GovState,
        };
        assert(governor.type_invariant());
        assert(governor.no_cooling_from_cold());
        assert(governor.convergence_requires_history());
        assert(governor.converged_requires_peak());
        assert(governor.delta_history@ == before.slide_window(delta));
        assert(_average as int == before.window_avg(delta));
        assert(governor.gradient_phase == ConvergenceGovernorPhaseAware::classify_phase_spec(
            delta, before.peak_observed, before.threshold));
        assert(governor.peak_observed == (before.peak_observed || delta >= before.threshold));
        assert(governor.threshold == before.threshold);
        assert(governor.awaken_threshold == before.awaken_threshold);
        assert(governor.window == before.window);
        assert(governor.max_delta == before.max_delta);
        assert(governor.state == ConvergenceGovernorPhaseAware::next_state_spec(
            before.state, _average,
            before.peak_observed || delta >= before.threshold,
            before.threshold, before.awaken_threshold));
        assert(match before.state {
            GovState::Active => governor.state == GovState::Active
                || governor.state == GovState::Cooling,
            GovState::Cooling => governor.state == GovState::Cooling
                || governor.state == GovState::Converged || governor.state == GovState::Active,
            GovState::Converged => governor.state == GovState::Converged
                || governor.state == GovState::Awakened,
            GovState::Awakened => governor.state == GovState::Awakened
                || governor.state == GovState::Converged,
        });
    }
}

/// A canonical probe contracts the interval and charges its existing Budget once.
pub fn bisection_probe_exports_primary_laws(
    search: &mut automation_structures::compositions::bisection::Bisection)
    requires old(search).invariant(), old(search).hi - old(search).lo >= 2,
{
    let ghost before = *search;
    search.probe();
    assert(search.monotonicity());
    assert(search.probe_bound());
    assert(search.hi - search.lo <= (before.hi - before.lo) / 2);
    assert(search.budget.allocated == before.budget.allocated + 1);
    assert(search.budget.capacity == before.budget.capacity);
    assert(search.domain_size == before.domain_size);
    assert(search.threshold == before.threshold);
    assert((search.hi as int == before.mid() && search.lo == before.lo)
        || (search.lo as int == before.mid() + 1 && search.hi == before.hi));
}

/// Driving the existing probe loop returns a converged, still-contained interval.
pub fn bisection_loop_exports_convergence(
    search: &mut automation_structures::compositions::bisection::Bisection)
    requires old(search).invariant(),
{
    let ghost before = *search;
    search.bisect();
    assert(search.monotonicity());
    assert(search.probe_bound());
    assert(search.hi - search.lo < 2);
    assert(search.domain_size == before.domain_size);
    assert(search.threshold == before.threshold);
    assert(search.budget.capacity == before.budget.capacity);
}

/// A proposal's guard, accepted effect and refusal frame come from the same Sampler.
pub fn sampler_weighted_draw_exports_primary_laws(
    sampler: &mut automation_structures::compositions::sampler::Sampler,
    item: usize, entropy: u64)
    requires old(sampler).inv(), item < old(sampler).actuation.num_seats,
{
    let ghost before = *sampler;
    let _accepted = sampler.draw_weighted(item, entropy);
    assert(_accepted == before.weighted_draw_enabled(item, entropy));
    assert(sampler.bounded_sample());
    assert(sampler.support_consistency());
    if _accepted {
        assert(sampler.budget.allocated == before.budget.allocated + 1);
        assert(sampler.actuation.effects@ == before.actuation.effects@
            .update(item as int, before.actuation.allocation@[item as int]));
    } else {
        assert(sampler.budget.allocated == before.budget.allocated);
        assert(sampler.actuation.effects@ == before.actuation.effects@);
    }
    assert(sampler.actuation.allocation@ == before.actuation.allocation@);
}

/// Arbitrary admitted AddChild preserves the three primary hierarchy laws.
pub fn hierarchy_add_exports_primary_laws(
    hierarchy: &mut automation_structures::primitives::quality_hierarchy::QualityHierarchy,
    parent: usize, child: usize)
    requires
        old(hierarchy).type_invariant(),
        old(hierarchy).strict_level_descent(),
        old(hierarchy).parent_edge_agreement(),
        old(hierarchy).cost_monotonicity(),
        parent < old(hierarchy).num_nodes, child < old(hierarchy).num_nodes,
        parent != child,
        !old(hierarchy).edge_exists(parent, child),
        old(hierarchy).parent@[child as int] == old(hierarchy).num_nodes,
        old(hierarchy).level@[parent as int] > old(hierarchy).level@[child as int],
        old(hierarchy).cost@[parent as int] <= old(hierarchy).cost@[child as int],
{
    hierarchy.add_child(parent, child);
    assert(hierarchy.type_invariant());
    assert(hierarchy.strict_level_descent());
    assert(hierarchy.parent_edge_agreement());
    assert(hierarchy.cost_monotonicity());
}

/// Arbitrary admitted isolated-property update preserves the same primary laws.
pub fn hierarchy_properties_export_primary_laws(
    hierarchy: &mut automation_structures::primitives::quality_hierarchy::QualityHierarchy,
    node: usize, level: u64, cost: u64)
    requires
        old(hierarchy).type_invariant(),
        old(hierarchy).strict_level_descent(),
        old(hierarchy).parent_edge_agreement(),
        old(hierarchy).cost_monotonicity(),
        node < old(hierarchy).num_nodes,
        level <= old(hierarchy).max_level,
        cost <= old(hierarchy).max_level,
        old(hierarchy).parent@[node as int] == old(hierarchy).num_nodes,
        !old(hierarchy).has_children_spec(node),
{
    hierarchy.set_node_properties(node, level, cost);
    assert(hierarchy.type_invariant());
    assert(hierarchy.strict_level_descent());
    assert(hierarchy.parent_edge_agreement());
    assert(hierarchy.cost_monotonicity());
}
/// An arbitrary admitted Registry exports the complete Register value frame.
pub fn registry_register_exports_partial_function<K: resource_registry::RegistryKey, V,
    S: resource_registry::RegistryLayout<K, V>>(
    registry: &mut resource_registry::ResourceRegistry<K, V, S>, key: K, value: V,
    Ghost(other): Ghost<K>, Ghost(other_value): Ghost<V>)
    where S::Entries: resource_registry::RegistrySearch<K, V, K>,
    requires old(registry).unique_mapping(), other != key,
{
    let ghost previous = *registry;
    registry.register(key, value);
    assert(registry.unique_mapping());
    assert(registry.maps_to(key, value));
    assert(registry.maps_to(other, other_value) == previous.maps_to(other, other_value));
    assert(registry.entries@ == resource_registry::without_key_sequence(previous.entries@, key)
        .push((key, value)));
}

/// An arbitrary admitted Registry exports Deregister and every other value frame.
pub fn registry_deregister_exports_partial_function<K: resource_registry::RegistryKey, V,
    S: resource_registry::RegistryLayout<K, V>>(
    registry: &mut resource_registry::ResourceRegistry<K, V, S>, key: K,
    Ghost(other): Ghost<K>, Ghost(other_value): Ghost<V>)
    where S::Entries: resource_registry::RegistrySearch<K, V, K>,
    requires old(registry).unique_mapping(), old(registry).contains_key(key), other != key,
{
    let ghost previous = *registry;
    registry.deregister(key);
    assert(registry.unique_mapping());
    assert(!registry.contains_key(key));
    assert(registry.maps_to(other, other_value) == previous.maps_to(other, other_value));
    assert(registry.entries@ == resource_registry::without_key_sequence(previous.entries@, key));
}

/// Arbitrary multi-member, multi-dimension owner: single prepare, resolution and reuse.
pub fn typed_allocation_single_exports_lifecycle<
    K: automation_structures::KeyIdentity,
    V,
    P: automation_structures::AllocationDomain<K, V>,
>(
    owner: &mut automation_structures::TypedAllocation<K, V, P>,
    key: K,
    value: V,
    charges: Vec<u64>,
    publish: bool,
)
    requires
        old(owner).inv(),
        old(owner).entries_spec().len() >= 2,
        old(owner).budgets_spec().len() >= 2,
{
    let ghost before = *owner;
    let ghost original_charges = charges;
    proof { owner.expose_coupling(); }
    match owner.prepare(key, value, charges) {
        Ok(prepared) => {
            assert(prepared.inv());
            assert(prepared.before_spec().entries_spec() == before.entries_spec());
            assert(prepared.before_spec().budgets_spec() == before.budgets_spec());
            assert(prepared.before_spec().domain_spec() == before.domain_spec());
            assert(prepared.key_spec() == key);
            assert(prepared.value_spec() == value);
            assert(prepared.charges_spec() == original_charges@);
            assert(prepared.charge_data_spec() == original_charges);
            assert(automation_structures::compositions::allocation_snapshot::typed_member_charge(
                before.budgets_spec().len() as int, original_charges@));
            assert(!before.contains_spec(key));
            assert(before.domain_spec().admits(key, value, original_charges@));
            assert(forall|d: int| 0 <= d < original_charges@.len() ==>
                original_charges@[d] as int
                    + #[trigger] before.budgets_spec()[d].1.allocated as int
                    <= before.budgets_spec()[d].1.capacity as int);

            let ghost prepared_charges = prepared.charge_data_spec();
            if publish {
                prepared.commit();
                assert(owner.inv());
                assert(owner.entries_spec()
                    == before.entries_spec().push((key, (value, original_charges))));
                assert(owner.domain_spec() == before.domain_spec());
                assert(owner.budgets_spec().len() == before.budgets_spec().len());
                assert(forall|d: int| 0 <= d < before.budgets_spec().len() ==>
                    #[trigger] owner.budgets_spec()[d].1.capacity
                        == before.budgets_spec()[d].1.capacity
                    && owner.budgets_spec()[d].1.allocated as int
                        == before.budgets_spec()[d].1.allocated as int
                            + original_charges@[d] as int);
                proof { owner.expose_coupling(); }
                assert(forall|d: int| 0 <= d < before.budgets_spec().len() ==>
                    #[trigger] owner.budgets_spec()[d].0
                        == before.budgets_spec()[d].0
                    && owner.budgets_spec()[d].1.reserved
                        == before.budgets_spec()[d].1.reserved
                    && owner.budgets_spec()[d].1.pending_eviction
                        == before.budgets_spec()[d].1.pending_eviction);
            } else {
                let _returned = prepared.cancel();
                assert(owner.inv());
                assert(_returned.reason == None && _returned.dimension == None);
                assert(_returned.key == key && _returned.value == value);
                assert(_returned.charges == prepared_charges);
                assert(_returned.charges == original_charges);
                assert(owner.entries_spec() == before.entries_spec());
                assert(owner.budgets_spec() == before.budgets_spec());
                assert(owner.domain_spec() == before.domain_spec());
            }
        },
        Err(_refused) => {
            assert(owner.inv());
            assert(_refused.key == key && _refused.value == value);
            assert(_refused.charges == original_charges);
            assert(owner.entries_spec() == before.entries_spec());
            assert(owner.budgets_spec() == before.budgets_spec());
            assert(owner.domain_spec() == before.domain_spec());
            proof {
            use automation_structures::TypedAllocationError;
            use automation_structures::compositions::allocation_snapshot::typed_member_charge;
            assert(match _refused.reason {
                Some(TypedAllocationError::WidthMismatch) =>
                    original_charges@.len() != before.budgets_spec().len()
                        && _refused.dimension == None,
                Some(TypedAllocationError::MembershipCharge) =>
                    original_charges@.len() == before.budgets_spec().len()
                        && before.budgets_spec().len() > 0
                        && original_charges@[0] != 1
                        && _refused.dimension == None,
                Some(TypedAllocationError::DuplicateKey) =>
                    typed_member_charge(
                        before.budgets_spec().len() as int, original_charges@)
                        && before.contains_spec(key) && _refused.dimension == None,
                Some(TypedAllocationError::OutsideDomain) =>
                    typed_member_charge(
                        before.budgets_spec().len() as int, original_charges@)
                        && !before.contains_spec(key)
                        && !before.domain_spec().admits(key, value, original_charges@)
                        && _refused.dimension == None,
                Some(TypedAllocationError::Capacity) =>
                    _refused.dimension is Some
                        && typed_member_charge(
                            before.budgets_spec().len() as int, original_charges@)
                        && !before.contains_spec(key)
                        && before.domain_spec().admits(key, value, original_charges@)
                        && _refused.dimension.unwrap() < original_charges@.len()
                        && original_charges@[_refused.dimension.unwrap() as int] as int
                            + before.budgets_spec()[
                                _refused.dimension.unwrap() as int].1.allocated as int
                            > before.budgets_spec()[
                                _refused.dimension.unwrap() as int].1.capacity as int
                        && forall|d: int| 0 <= d < _refused.dimension.unwrap() ==>
                            original_charges@[d] as int
                                + #[trigger] before.budgets_spec()[d].1.allocated as int
                                <= before.budgets_spec()[d].1.capacity as int,
                Some(TypedAllocationError::StorageUnavailable) =>
                    _refused.dimension == None
                        && typed_member_charge(
                            before.budgets_spec().len() as int, original_charges@)
                        && !before.contains_spec(key)
                        && before.domain_spec().admits(key, value, original_charges@)
                        && forall|d: int| 0 <= d < original_charges@.len() ==>
                            original_charges@[d] as int
                                + #[trigger] before.budgets_spec()[d].1.allocated as int
                                <= before.budgets_spec()[d].1.capacity as int,
                _ => false,
            });
            }
        },
    }
    let _members = owner.len();
    assert(_members == owner.entries_spec().len());
    let _dimensions = owner.dimension_count();
    assert(_dimensions == before.budgets_spec().len());
}

/// Arbitrary retained members and at least two pending items use the original batch owner.
pub fn typed_allocation_batch_exports_lifecycle<
    K: automation_structures::KeyIdentity,
    V,
    P: automation_structures::AllocationDomain<K, V>,
>(
    owner: &mut automation_structures::TypedAllocation<K, V, P>,
    items: Vec<(K, (V, Vec<u64>))>,
    publish: bool,
)
    requires
        old(owner).inv(),
        old(owner).entries_spec().len() >= 2,
        old(owner).budgets_spec().len() >= 2,
        items@.len() >= 2,
{
    let ghost before = *owner;
    let ghost original_items = items@;
    match owner.prepare_batch(items) {
        Ok(prepared) => {
            assert(prepared.inv());
            assert(prepared.before_spec().entries_spec() == before.entries_spec());
            assert(prepared.before_spec().budgets_spec() == before.budgets_spec());
            assert(prepared.before_spec().domain_spec() == before.domain_spec());
            assert(prepared.items_spec() == original_items);
            assert(automation_structures::compositions::allocation_snapshot::typed_batch_admitted(
                before, original_items, original_items.len() as int));
            if publish {
                prepared.commit();
                assert(owner.inv());
                assert(owner.entries_spec() == before.entries_spec() + original_items);
                assert(owner.domain_spec() == before.domain_spec());
                assert(owner.budgets_spec().len() == before.budgets_spec().len());
                assert(forall|d: int| 0 <= d < before.budgets_spec().len() ==>
                    #[trigger] owner.budgets_spec()[d].0
                        == before.budgets_spec()[d].0
                    && owner.budgets_spec()[d].1.capacity
                        == before.budgets_spec()[d].1.capacity
                    && owner.budgets_spec()[d].1.reserved
                        == before.budgets_spec()[d].1.reserved
                    && owner.budgets_spec()[d].1.pending_eviction
                        == before.budgets_spec()[d].1.pending_eviction
                    && owner.budgets_spec()[d].1.allocated as int
                        == before.budgets_spec()[d].1.allocated as int
                            + automation_structures::compositions::allocation_snapshot::typed_charge_to(
                                original_items, original_items.len() as int, d));
            } else {
                let _returned = prepared.cancel();
                assert(owner.inv());
                assert(_returned.reason == None);
                assert(_returned.entry == None && _returned.dimension == None);
                assert(_returned.items@ == original_items);
                assert(owner.entries_spec() == before.entries_spec());
                assert(owner.budgets_spec() == before.budgets_spec());
                assert(owner.domain_spec() == before.domain_spec());
            }
        },
        Err(_refused) => {
            assert(owner.inv());
            assert(_refused.items == items);
            assert(_refused.reason is Some);
            assert(automation_structures::compositions::allocation_snapshot::typed_batch_refusal(
                before, original_items, _refused.reason.unwrap(),
                _refused.entry, _refused.dimension));
            assert(owner.entries_spec() == before.entries_spec());
            assert(owner.budgets_spec() == before.budgets_spec());
            assert(owner.domain_spec() == before.domain_spec());
        },
    }
    let _members = owner.len();
    assert(_members == owner.entries_spec().len());
    let _dimensions = owner.dimension_count();
    assert(_dimensions == before.budgets_spec().len());
}

/// A successful or refused ordinary owned preparation can cancel and reuse its retained owner.
pub fn owned_reduction_cancellation_reuses_owner<
    V, O: automation_structures::OwnedReductionOperation<V>,
>(owner: &mut automation_structures::VersionedReduction<V, O>, input: V)
    -> (returned: V)
    requires
        old(owner).inv(),
        old(owner).processed_spec() >= 2,
        old(owner).processed_spec() < old(owner).limit_spec(),
        old(owner).processed_spec() < usize::MAX - 1,
        old(owner).operator_spec().accepts(
            old(owner).value_spec(old(owner).processed_spec() as int), input),
    ensures returned == input, final(owner).inv(), final(owner).same_state(*old(owner)),
{
    let ghost before = *owner;
    let returned = match owner.prepare(input) {
        Ok(prepared) => prepared.cancel(),
        Err((_reason, returned)) => returned,
    };
    assert(owner.inv());
    assert(owner.same_state(before));
    proof { owner.expose_state_frame(&before); }
    let _count = owner.processed_len();
    assert(_count == before.processed_spec());
    returned
}

/// A sorted-slice query exports its bound, hit relation and absence sentinel.
pub fn sorted_slice_query_exports_membership_and_absence(
    sorted: &[u64], target: u64)
    requires automation_structures::compositions::bisection::is_sorted(sorted@),
{
    let _index =
        automation_structures::compositions::bisection::bisection_find(sorted, target);
    assert(_index as int <= sorted@.len() as int);
    if _index < sorted.len() {
        assert(sorted@[_index as int] == target);
    }
    if _index == sorted.len() {
        assert(forall|index: int| 0 <= index < sorted@.len()
            ==> #[trigger] sorted@[index] != target);
    }
}

/// Raw fanout configuration and default construction export their exact initial state.
pub fn raw_fanout_default_constructor_exports_configuration(
    capacity: usize, max_inputs: usize, record_domain_size: u64,
) {
    use automation_structures::modalities::stream_graph_fanout::StreamGraphFanout;
    let _valid = StreamGraphFanout::valid_config(capacity, record_domain_size);
    assert(_valid == (capacity > 0 && record_domain_size > 0));
    if _valid {
        let _flow = StreamGraphFanout::new(capacity, max_inputs, record_domain_size);
        assert(_flow.left_queue.capacity == capacity);
        assert(_flow.right_queue.capacity == capacity);
        assert(_flow.max_inputs == max_inputs);
        assert(_flow.record_domain_size == record_domain_size);
        assert(_flow.left_queue.values@.len() == 0);
        assert(_flow.right_queue.values@.len() == 0);
        assert(_flow.ingested.value_spec() == 0);
        assert(_flow.left_emitted.value_spec() == 0);
        assert(_flow.right_emitted.value_spec() == 0);
        assert(_flow.inv());
    }
}

/// Raw fanout termination observes its exact retained input and branch state.
pub fn raw_fanout_terminal_exports_state<
    S: automation_structures::BufferLayout<u64>,
>(flow: &automation_structures::modalities::stream_graph_fanout::StreamGraphFanout<S>)
    requires flow.inv(),
{
    let _terminal = flow.terminal();
    assert(_terminal == (flow.ingested.value_spec() == flow.max_inputs as nat
        && flow.left_queue.values@.len() == 0
        && flow.right_queue.values@.len() == 0));
}

/// Scalar admission exports the joint Registry/Budget commit.
pub fn allocation_accept_exports_coupled_membership(
    owner: &mut automation_structures::compositions::allocation_snapshot::AllocationSnapshot,
    node: u64,
    cost: u64,
)
    requires
        old(owner).type_invariant(),
        old(owner).budget_consistency(),
        node < old(owner).num_nodes,
        !old(owner).contains(node),
        1 <= cost,
        old(owner).budget.used() + cost as int
            <= old(owner).budget.capacity as int,
{
    let ghost before = *owner;
    owner.accept_node(node, cost);
    assert(owner.registry.entries@
        == before.registry.entries@.push((node, cost)));
    assert(owner.contains(node));
    assert(owner.budget.allocated == before.budget.allocated + cost);
    assert(owner.num_nodes == before.num_nodes);
    assert(owner.budget.capacity == before.budget.capacity);
    assert(owner.type_invariant());
    assert(owner.budget_consistency());
    assert(owner.budget.allocated as int
        == automation_structures::compositions::allocation_snapshot::cost_sum_to(
            owner.registry.entries@,
            owner.registry.entries@.len() as int,
        ));
}

/// Existing root observations identify the exact union branches.
pub fn equivalence_union_exports_parent_rank_and_roots(
    owner: &mut automation_structures::compositions::equivalence_class::EquivalenceClass,
    left: usize,
    right: usize,
)
    requires
        old(owner).inv(),
        left < old(owner).n,
        right < old(owner).n,
{
    let ghost before = *owner;
    let _left_root = owner.find(left);
    let _right_root = owner.find(right);
    assert(owner.rooted_at(left, _left_root));
    assert(owner.rooted_at(right, _right_root));
    assert(owner.parent_of(_left_root) == _left_root);
    assert(owner.parent_of(_right_root) == _right_root);
    let merged = owner.union(left, right);
    assert(owner.inv());
    assert(owner.n == before.n);
    assert(owner.budget.capacity == before.budget.capacity);
    assert(owner.budget.reserved == before.budget.reserved);
    assert(owner.budget.pending_eviction == before.budget.pending_eviction);
    assert(merged == (before.budget.allocated < before.budget.capacity
        && !before.same_class(left, right)));
    if merged {
        assert(owner.budget.allocated == before.budget.allocated + 1);
        proof {
            assert forall|root: usize|
                #[trigger] before.rooted_at(left, root)
                implies root == _left_root by {
                before.rooted_at_unique(left, root, _left_root);
            }
            assert forall|root: usize|
                #[trigger] before.rooted_at(right, root)
                implies root == _right_root by {
                before.rooted_at_unique(right, root, _right_root);
            }
        assert(_left_root != _right_root);
        if before.rank_of(_left_root) < before.rank_of(_right_root) {
            assert(owner.parents.entries@
                == before.parents.entries@.push((_left_root, _right_root)));
            assert(owner.ranks.entries@ == before.ranks.entries@);
        } else if before.rank_of(_left_root) > before.rank_of(_right_root) {
            assert(owner.parents.entries@
                == before.parents.entries@.push((_right_root, _left_root)));
            assert(owner.ranks.entries@ == before.ranks.entries@);
        } else {
            assert(owner.parents.entries@
                == before.parents.entries@.push((_right_root, _left_root)));
            assert(owner.ranks.entries@
                == resource_registry::without_key_sequence(
                    before.ranks.entries@, _left_root,
                ).push((
                    _left_root,
                    (before.rank_of(_left_root) + 1) as u64,
                )));
        }
        }
    } else {
        assert(owner.budget.allocated == before.budget.allocated);
        assert(*owner == before);
    }
}

/// Raw additive Reduction exports the next arbitrary consumed prefix and carry.
pub fn raw_reduction_process_exports_prefix_and_carry(
    owner: &mut automation_structures::compositions::reduction::Reducer,
)
    requires
        old(owner).inv(),
        old(owner).audit.log@.len() < old(owner).source@.len(),
{
    let ghost before = *owner;
    let ghost position = before.audit.log@.len();
    owner.process();
    assert(owner.inv());
    assert(owner.source@ == before.source@);
    assert(owner.audit.log@.len() == position + 1);
    assert(owner.audit.last_hash
        == before.audit.last_hash + before.source@[position as int]);
    assert(owner.prefix_binding());
    assert(owner.audit.log@[position as int].operation
        == before.source@[position as int]);
    assert(owner.aggregate());
    assert(owner.audit.last_hash as int
        == automation_structures::compositions::reduction::sum_to(
            before.source@, owner.audit.log@.len() as int));
}

/// Raw Visit exports the retained Cost2/root-star profile's coupled owner actions.
pub fn raw_traversal_visit_exports_fixed_profile(
    owner: &mut automation_structures::compositions::traversal_engine::TraversalEngine,
    node: usize,
)
    requires
        old(owner).inv(),
        node < old(owner).num_nodes,
        old(owner).queue_contains_spec(node),
        !old(owner).visited_contains_spec(node),
{
    let ghost before = *owner;
    let ghost admitted =
        before.budget.allocated as int + 2 <= before.budget.capacity as int;
    owner.visit_node(node);
    proof {
        owner.expose();
        assert(owner.inv() && owner.full_topology());
        assert(owner.num_nodes == before.num_nodes && owner.root == before.root);
        assert(owner.graph == before.graph);
        assert(owner.budget.capacity == before.budget.capacity);
        assert(owner.budget.reserved == before.budget.reserved);
        assert(owner.budget.pending_eviction == before.budget.pending_eviction);
        assert(owner.accepted.pending@ == before.accepted.pending@);
        assert(owner.queue.capacity == before.queue.capacity);
        if admitted {
            assert(owner.budget.allocated as int == before.budget.allocated as int + 2);
            assert(owner.accepted.original@ == before.accepted.original@.push(node));
            assert(owner.accepted.accumulated@
                == before.accepted.accumulated@.push(node));
        } else {
            assert(owner.budget.allocated == before.budget.allocated);
            assert(owner.accepted.original@ == before.accepted.original@);
            assert(owner.accepted.accumulated@ == before.accepted.accumulated@);
        }
        assert forall|candidate: usize| candidate < before.num_nodes implies
            #[trigger] owner.visited_contains_spec(candidate)
                == (before.visited_contains_spec(candidate) || candidate == node) by {}
        if admitted && node == before.root {
            assert(owner.queue.values@.len() == before.num_nodes - 1);
            assert forall|index: int| 0 <= index < owner.queue.values@.len() implies
                #[trigger] owner.queue.values@[index]
                    == if index < before.root as int {
                        index as usize
                    } else {
                        (index + 1) as usize
                    } by {}
        } else {
            assert(exists|index: int|
                0 <= index < before.queue.values@.len()
                    && before.queue.values@[index] == node
                    && owner.queue.values@ == before.queue.values@.remove(index));
        }
        assert(owner.accepted_subset_visited());
        assert(owner.accepted_cost_accounting());
        assert(owner.budget.allocated as int
            == owner.accepted.accumulated@.len() * 2);
    }
}

/// Raw Skip removes only the queued node and preserves the other actual owners.
pub fn raw_traversal_skip_exports_owner_frames(
    owner: &mut automation_structures::compositions::traversal_engine::TraversalEngine,
    node: usize,
)
    requires
        old(owner).inv(),
        node < old(owner).num_nodes,
        old(owner).queue_contains_spec(node),
{
    let ghost before = *owner;
    owner.skip(node);
    assert(owner.inv());
    assert(owner.num_nodes == before.num_nodes && owner.root == before.root);
    assert(owner.graph == before.graph && owner.budget == before.budget);
    assert(owner.visited@ == before.visited@ && owner.accepted == before.accepted);
    assert(owner.queue.capacity == before.queue.capacity);
    assert(exists|index: int|
        0 <= index < before.queue.values@.len()
            && before.queue.values@[index] == node
            && owner.queue.values@ == before.queue.values@.remove(index));
    assert forall|candidate: usize|
        #[trigger] owner.queue_contains_spec(candidate)
            == (before.queue_contains_spec(candidate) && candidate != node) by {}
}

/// Raw termination is an exact stutter at the empty frontier.
pub fn raw_traversal_terminate_exports_exact_stutter(
    owner: &mut automation_structures::compositions::traversal_engine::TraversalEngine,
)
    requires old(owner).inv(), old(owner).queue.values@.len() == 0,
{
    let ghost before = *owner;
    owner.terminate();
    assert(owner.inv());
    assert(*owner == before);
}

/// The selected K profile exports cardinality/ranking and revision invalidation.
pub fn raw_ranked_selection_exports_selected_profile(
    owner: &mut automation_structures::primitives::competitive_selection::CompetitiveSelectionRanked,
    new_scores: Vec<u64>,
)
    requires
        old(owner).type_invariant(),
        1 <= old(owner).k,
        old(owner).k as int <= old(owner).scores@.len(),
        new_scores@.len() == old(owner).scores@.len(),
        forall|i: int| 0 <= i < new_scores@.len()
            ==> #[trigger] new_scores@[i] <= old(owner).max_score,
{
    let ghost before = *owner;
    let ghost replacement = new_scores@;
    owner.select();
    let _count = owner.selected_len();
    assert(_count == before.k);
    assert(owner.scores@ == before.scores@);
    assert(owner.threshold_optimality());
    assert(owner.ranked_tie_break());
    owner.update_scores(new_scores);
    assert(owner.scores@ == replacement);
    assert(forall|i: int| 0 <= i < owner.selected@.len()
        ==> !#[trigger] owner.selected@[i]);
    assert(owner.inv());
}

/// Available-pool evaluation frames other seats; score revision clears all seats.
pub fn raw_exclusive_selection_exports_selected_profile(
    owner: &mut automation_structures::primitives::competitive_selection::CompetitiveSelectionHardExclusive,
    seat: usize, candidate: usize, score: u64,
)
    requires
        old(owner).inv(),
        old(owner).num_seats >= 2,
        old(owner).num_candidates >= 2,
        old(owner).max_score >= 1,
        seat < old(owner).num_seats,
        candidate < old(owner).num_candidates,
        score <= old(owner).max_score,
        old(owner).allocation@[seat as int] is None,
        exists|c: int| old(owner).available(seat as int, c),
{
    let ghost before = *owner;
    owner.evaluate(seat);
    assert(owner.allocation@[seat as int] is Some);
    assert(owner.scores@ == before.scores@);
    assert(forall|other: int| 0 <= other < owner.num_seats
        && other != seat as int
        ==> #[trigger] owner.allocation@[other] == before.allocation@[other]);
    assert(owner.mutual_exclusion());
    assert(owner.winner_optimality());
    assert(owner.winner_tie_break());
    let ghost before_revision = *owner;
    owner.update_score(seat, candidate, score);
    assert(owner.scores@[seat as int]@
        == before_revision.scores@[seat as int]@.update(candidate as int, score));
    assert(forall|other: int| 0 <= other < owner.num_seats
        ==> #[trigger] owner.allocation@[other] is None);
    assert(owner.inv());
}

/// One enabled Webster award and terminal normalization retain revision safety.
pub fn raw_soft_selection_exports_selected_profile(
    owner: &mut automation_structures::primitives::competitive_selection::CompetitiveSelectionSoft,
    candidate: usize, score: u64,
)
    requires
        old(owner).mutable_score_inv(),
        candidate < old(owner).scores@.len(),
        1 <= score <= old(owner).max_score,
{
    let _assigned = owner.assigned_weight();
    if _assigned < owner.weight_total {
        let ghost before = *owner;
        let _winner = owner.assign_next();
        assert(automation_structures::primitives::competitive_selection::priority_winner(
            before.scores@, before.extra@, _winner as int));
        assert(owner.extra@ == before.extra@.update(
            _winner as int, (before.extra@[_winner as int] + 1) as u64));
        assert(owner.scores@ == before.scores@);
    }
    assert(owner.universal_contribution());
    assert(owner.bounded_total());
    assert(owner.score_order_preservation());
    assert(owner.tie_boundedness());
    let _assigned_after = owner.assigned_weight();
    if _assigned_after == owner.weight_total {
        assert(owner.terminal());
        assert(owner.normalization());
    }
    let ghost before_revision = *owner;
    owner.update_score(candidate, score);
    assert(owner.scores@ == before_revision.scores@.update(candidate as int, score));
    assert(forall|i: int| 0 <= i < owner.extra@.len()
        ==> #[trigger] owner.extra@[i] == 0);
    assert(owner.mutable_score_inv());
}

/// Observe enabled default-u64 transitions without a scheduler or convergence claim.
pub fn raw_default_propagation_exports_round_transitions(
    pass: &mut automation_structures::primitives::propagation_pass::PropagationPass,
    node: usize,
)
    requires old(pass).inv(),
{
    use automation_structures::primitives::propagation_pass::Round;
    match pass.round {
        Round::Idle => {
            let ghost before = *pass;
            if pass.changed && pass.iteration < pass.max_iterations {
                pass.start_round();
                assert(pass.values@ == before.values@);
                assert(pass.snapshot@ == before.values@);
                assert(pass.iteration == before.iteration);
                assert(forall|i: int| 0 <= i < pass.updated@.len()
                    ==> !#[trigger] pass.updated@[i]);
                assert(pass.round == Round::Running);
            } else {
                assert(pass.settled_or_iteration_limit());
                pass.terminate();
                assert(pass.num_nodes == before.num_nodes);
                assert(pass.max_iterations == before.max_iterations);
                assert(pass.max_value == before.max_value);
                assert(pass.edges@ == before.edges@);
                assert(pass.values@ == before.values@);
                assert(pass.snapshot@ == before.snapshot@);
                assert(pass.updated@ == before.updated@);
                assert(pass.iteration == before.iteration);
                assert(pass.changed == before.changed);
                assert(pass.round == before.round);
            }
        },
        Round::Running => {
            assert(pass.type_invariant());
            let already_updated = match pass.updated.get(node) {
                Some(updated) => *updated,
                None => true,
            };
            if node < pass.num_nodes && !already_updated {
                let ghost before = *pass;
                pass.update_node(node);
                assert(pass.values@ == before.values@.update(node as int,
                    automation_structures::primitives::propagation_pass::local_combine(
                        before.edges@, before.snapshot@, node) as u64));
                assert(pass.updated@ == before.updated@.update(node as int, true));
                assert(pass.snapshot@ == before.snapshot@);
                assert(pass.iteration == before.iteration);
                assert(pass.snapshot_locality());
            }
            let _covered = pass.all_nodes_updated();
            if _covered {
                let ghost before_closure = *pass;
                pass.end_round();
                assert(pass.iteration as int == before_closure.iteration as int + 1);
                assert(pass.changed
                    == (before_closure.values@ != before_closure.snapshot@));
                assert(pass.values@ == before_closure.values@);
                assert(pass.snapshot@ == before_closure.snapshot@);
                assert(pass.updated@ == before_closure.updated@);
                assert(pass.round == Round::Idle);
            }
        },
    }
    assert(pass.iteration_bound());
    assert(pass.snapshot_locality());
}

/// Arbitrary valid Sequential states export begin/complete guards and history frames.
pub fn raw_sequential_exports_step_history_frames(
    owner: &mut automation_structures::modalities::sequential::Sequential,
    next_value: u64,
)
    requires old(owner).inv(),
{
    let ghost before_begin = *owner;
    let _begun = owner.begin_step();
    proof {
        assert(_begun
            == (before_begin.pc < before_begin.steps && !before_begin.active));
        assert(owner.pc == before_begin.pc);
        assert(owner.value == before_begin.value);
        assert(owner.history@ == before_begin.history@);
        assert(owner.active == if _begun { true } else { before_begin.active });
    }
    let ghost before_completion = *owner;
    let _completed = owner.complete_step(next_value);
    proof {
        assert(_completed
            == (before_completion.active
                && next_value < before_completion.value_domain_size));
        if _completed {
            assert(owner.pc as int == before_completion.pc as int + 1);
            assert(owner.value == next_value);
            assert(!owner.active);
            assert(owner.history@ == before_completion.history@.push(next_value));
        } else {
            assert(owner.pc == before_completion.pc);
            assert(owner.value == before_completion.value);
            assert(owner.active == before_completion.active);
            assert(owner.history@ == before_completion.history@);
        }
        assert(owner.history_position_agreement());
        assert(owner.inv());
    }
}

/// Readiness, start and completion preserve predecessor eligibility and other nodes.
pub fn raw_step_graph_exports_guarded_state_transitions<
    S: automation_structures::modalities::step_graph::StepGraphStates,
>(
    graph: &mut automation_structures::modalities::step_graph::StepGraph<S>,
    node: usize,
)
    requires old(graph).inv(),
{
    let ghost before_ready = *graph;
    let _ready = graph.become_ready(node);
    proof {
        assert(_ready == (
            node < before_ready.num_nodes
            && before_ready.nstate@[node as int]
                == automation_structures::StepState::NotReady
            && automation_structures::modalities::step_graph::StepGraph::has_predecessor_in(
                before_ready.edges@, node)
            && automation_structures::modalities::step_graph::StepGraph::predecessors_complete_in(
                before_ready.edges@, before_ready.nstate@, node)));
        assert(graph.nstate@ == if _ready {
            before_ready.nstate@.update(node as int, automation_structures::StepState::Ready)
        } else {
            before_ready.nstate@
        });
        assert(automation_structures::modalities::step_graph::states_monotone(
            before_ready.nstate@, graph.nstate@));
    }
    let ghost before_start = *graph;
    let _started = graph.start_running(node);
    proof {
        assert(_started == (
            node < before_start.num_nodes
            && before_start.nstate@[node as int]
                == automation_structures::StepState::Ready));
        assert(graph.nstate@ == if _started {
            before_start.nstate@.update(node as int, automation_structures::StepState::Running)
        } else {
            before_start.nstate@
        });
        assert(automation_structures::modalities::step_graph::states_monotone(
            before_start.nstate@, graph.nstate@));
    }
    let ghost before_completion = *graph;
    let _completed = graph.complete_node(node);
    proof {
        assert(_completed == (
            node < before_completion.num_nodes
            && before_completion.nstate@[node as int]
                == automation_structures::StepState::Running));
        assert(graph.nstate@ == if _completed {
            before_completion.nstate@.update(
                node as int, automation_structures::StepState::Complete)
        } else {
            before_completion.nstate@
        });
        assert(automation_structures::modalities::step_graph::states_monotone(
            before_completion.nstate@, graph.nstate@));
        assert(graph.num_nodes == before_ready.num_nodes);
        assert(graph.edges@ == before_ready.edges@);
        assert(graph.eligibility_closed());
        assert(graph.no_run_before_predecessors());
    }
}

/// Zero withdraws only unselected support; selection and Budget remain fixed.
pub fn sampler_zero_exports_support_and_selection_frames(
    sampler: &mut automation_structures::compositions::sampler::Sampler,
    item: usize,
)
    requires old(sampler).inv(),
{
    let ghost before = *sampler;
    let _accepted = sampler.zero(item);
    proof {
        assert(_accepted
            == (item < before.actuation.num_seats && !before.contains(item)));
        assert(sampler.budget == before.budget);
        assert(sampler.actuation.effects@ == before.actuation.effects@);
        if _accepted {
            assert(sampler.actuation.allocation@ ==
                if before.actuation.allocation@[item as int] is Some {
                    before.actuation.allocation@.update(item as int, None)
                } else {
                    before.actuation.allocation@
                });
        } else {
            assert(sampler.actuation.allocation@ == before.actuation.allocation@);
        }
        assert(sampler.bounded_sample());
        assert(sampler.support_consistency());
    }
}

/// Existing federation actions conserve capacity and change only the selected pool.
pub fn raw_federated_budget_exports_coupled_transitions(
    owner: &mut automation_structures::compositions::federated_budget::FederatedBudget,
    pool: usize,
    amount: u64,
)
    requires
        old(owner).inv(),
        old(owner).master.capacity >= 1,
        old(owner).sub_pools@.len() >= 2,
{
    let ghost before = *owner;
    let _delegated = owner.allocate_sub_pool(pool, amount);
    proof {
        assert(owner.inv() && owner.capacity_conservation());
        assert(owner.master.capacity == before.master.capacity);
        assert(owner.sub_pools@.len() == before.sub_pools@.len());
        assert(_delegated == (pool < before.sub_pools@.len() && amount > 0
            && before.master.used() + amount as int <= before.master.capacity as int));
        if _delegated {
            assert(owner.master.allocated == before.master.allocated + amount);
            assert(owner.sub_pools@[pool as int].allocated
                == before.sub_pools@[pool as int].allocated);
            assert(owner.sub_pools@[pool as int].reserved
                == before.sub_pools@[pool as int].reserved + amount);
        } else {
            assert(owner.master.allocated == before.master.allocated);
            assert(owner.sub_pools@ == before.sub_pools@);
        }
        assert forall|i: int| 0 <= i < before.sub_pools@.len() && i != pool as int implies
            #[trigger] owner.sub_pools@[i] == before.sub_pools@[i] by {}
    }
    let ghost delegated = *owner;
    let _consumed = owner.allocate_from_sub_pool(pool, amount);
    proof {
        assert(owner.inv() && owner.capacity_conservation());
        assert(owner.master == delegated.master);
        assert(owner.sub_pools@.len() == delegated.sub_pools@.len());
        assert(_consumed == (pool < delegated.sub_pools@.len() && amount > 0
            && amount <= delegated.sub_pools@[pool as int].reserved));
        if _consumed {
            assert(owner.sub_pools@[pool as int].allocated
                == delegated.sub_pools@[pool as int].allocated + amount);
            assert(owner.sub_pools@[pool as int].reserved
                == delegated.sub_pools@[pool as int].reserved - amount);
        } else {
            assert(owner.sub_pools@ == delegated.sub_pools@);
        }
        assert forall|i: int| 0 <= i < delegated.sub_pools@.len() && i != pool as int implies
            #[trigger] owner.sub_pools@[i] == delegated.sub_pools@[i] by {}
    }
    let ghost consumed = *owner;
    let _released = owner.release_from_sub_pool(pool, amount);
    proof {
        assert(owner.inv() && owner.capacity_conservation());
        assert(owner.master == consumed.master);
        assert(owner.sub_pools@.len() == consumed.sub_pools@.len());
        assert(_released == (pool < consumed.sub_pools@.len() && amount > 0
            && amount <= consumed.sub_pools@[pool as int].allocated));
        if _released {
            assert(owner.sub_pools@[pool as int].allocated
                == consumed.sub_pools@[pool as int].allocated - amount);
            assert(owner.sub_pools@[pool as int].reserved
                == consumed.sub_pools@[pool as int].reserved + amount);
        } else {
            assert(owner.sub_pools@ == consumed.sub_pools@);
        }
        assert forall|i: int| 0 <= i < consumed.sub_pools@.len() && i != pool as int implies
            #[trigger] owner.sub_pools@[i] == consumed.sub_pools@[i] by {}
    }
}

/// Acquire observes the three logical window branches; enabled Tick changes the clock.
pub fn raw_rate_limit_exports_acquire_and_tick(
    owner: &mut automation_structures::compositions::rate_limit::RateLimit,
)
    requires old(owner).type_invariant(), old(owner).window_start_not_future(),
{
    let ghost before = *owner;
    let _acquired = owner.try_acquire();
    proof {
        assert(_acquired == (before.window_expired()
            || before.budget.allocated < before.budget.capacity));
        assert(owner.budget.capacity == before.budget.capacity);
        assert(owner.window_duration == before.window_duration);
        assert(owner.max_clock == before.max_clock && owner.clock == before.clock);
        if before.window_expired() {
            assert(owner.window_start == before.clock && owner.budget.allocated == 1);
        } else if before.budget.allocated < before.budget.capacity {
            assert(owner.window_start == before.window_start);
            assert(owner.budget.allocated == before.budget.allocated + 1);
        } else {
            assert(owner.window_start == before.window_start);
            assert(owner.budget.allocated == before.budget.allocated);
        }
        assert(owner.type_invariant());
        assert(owner.window_count_bound() && owner.window_start_not_future());
    }
    if owner.clock < owner.max_clock {
        let ghost before_tick = *owner;
        owner.tick();
        assert(automation_structures::compositions::rate_limit::RateLimit::tick_step(
            before_tick, *owner));
        assert(owner.budget == before_tick.budget);
        assert(owner.window_start == before_tick.window_start);
        assert(owner.clock as int == before_tick.clock as int + 1);
        assert(owner.type_invariant());
        assert(owner.window_count_bound() && owner.window_start_not_future());
    }
}

/// Raw graph updates export adjacency and weighted-survivor relations.
pub fn raw_relationship_graph_exports_add_and_remove(
    owner: &mut automation_structures::compositions::relationship_graph::RelationshipGraph,
    source: usize,
    target: usize,
    weight: u64,
)
    requires
        old(owner).inv(),
        source < old(owner).num_nodes,
        target < old(owner).num_nodes,
        weight <= old(owner).max_weight,
        source != target,
{
    let ghost before = *owner;
    let _added = owner.add_edge(source, target, weight);
    proof {
        assert(owner.inv() && owner.adjacency_consistency() && owner.no_self_loops());
        assert(_added == !before.exact_edge(source, target, weight));
        if _added {
            assert(owner.registry.entries@
                == before.registry.entries@.push(((source, target, weight), ())));
        } else {
            assert(owner.registry.entries@ == before.registry.entries@);
        }
        assert forall|s: usize, d: usize| #[trigger] owner.edge_proj(s, d)
            == (before.edge_proj(s, d) || (s == source && d == target)) by {}
    }
    let ghost inserted = *owner;
    owner.remove_edge(source, target);
    assert(owner.inv() && owner.adjacency_consistency() && owner.no_self_loops());
    assert(owner.num_nodes == before.num_nodes && owner.max_weight == before.max_weight);
    assert(!owner.edge_proj(source, target));
    assert forall|s: usize, d: usize, w: u64| #[trigger] owner.exact_edge(s, d, w)
        == (!(s == source && d == target) && inserted.exact_edge(s, d, w)) by {}
}

/// The selected modulo-three profile restores an existing prefix after one descent.
pub fn raw_backtracking_exports_prefix_restoration(
    owner: &mut automation_structures::primitives::backtracking_traversal::BacktrackingTraversal,
    branch: u64,
    delta: u64,
)
    requires
        old(owner).inv(),
        old(owner).branch_factor >= 2,
        !old(owner).is_leaf(),
        1 <= branch <= old(owner).branch_factor,
        1 <= delta <= 2,
{
    let ghost before = *owner;
    owner.descend(branch, delta);
    assert(owner.inv() && owner.pairing() && owner.state_restoration());
    assert(owner.path@ == before.path@.push(branch));
    assert(owner.ledger@.len() == before.ledger@.len() + 1);
    assert(owner.ledger@[before.ledger@.len() as int].saved == before.aux);
    assert(owner.ledger@[before.ledger@.len() as int].delta == delta);
    let ghost descended = *owner;
    let visit_enabled = owner.can_visit();
    if visit_enabled {
        let ghost before_visit = *owner;
        let visit = owner.try_visit();
        if visit.is_ok() {
            assert(owner.visited@.len() == before_visit.visited@.len() + 1);
            assert(owner.visited@[before_visit.visited@.len() as int]@
                == before_visit.path@);
        } else {
            assert(owner.same_state(&before_visit));
        }
        assert(owner.path@ == before_visit.path@);
        assert(owner.ledger@ == before_visit.ledger@ && owner.aux == before_visit.aux);
        assert(owner.inv() && owner.recorded_leaf_validity());
    }
    let ghost recorded = owner.visited@;
    owner.ascend();
    assert(owner.inv() && owner.pairing() && owner.state_restoration());
    assert(owner.path@ == before.path@ && owner.aux == before.aux);
    assert(owner.ledger@ == descended.ledger@.drop_last());
    assert(owner.ledger@.len() == before.ledger@.len());
    assert forall|i: int| 0 <= i < before.ledger@.len() implies
        #[trigger] owner.ledger@[i].saved == before.ledger@[i].saved
            && owner.ledger@[i].delta == before.ledger@[i].delta by {}
    assert(owner.visited@ == recorded && owner.recorded_leaf_validity());
}

/// The existing Registry query exports its exact existential meaning and read frame.
pub fn registry_any_matching_exports_selected_count<
    K: resource_registry::KeyIdentity, V, S: resource_registry::RegistryLayout<K, V>,
    P: resource_registry::RegistryPredicate<K, V>,
>(registry: &resource_registry::ResourceRegistry<K, V, S>, predicate: &P)
    where S::Entries: resource_registry::RegistrySearch<K, V, K>,
{
    let ghost before = *registry;
    let _present = registry.any_matching(predicate);
    assert(_present == (resource_registry::selected_count(
        registry.entries@, registry.entries@.len() as int, *predicate) > 0));
    assert(*registry == before);
}

/// Physical reservation leaves every exported logical allocation owner unchanged.
pub fn indexed_allocation_exports_physical_reservation_frames(
    owner: &mut automation_structures::TypedAllocation<u64, u64,
        automation_structures::UnrestrictedAllocation, automation_structures::IndexedStorage>,
    additional: usize,
)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    let _reserved = owner.try_reserve_members(additional);
    assert(owner.inv());
    assert(owner.entries_spec() == before.entries_spec());
    assert(owner.budgets_spec() == before.budgets_spec());
    assert(owner.domain_spec() == before.domain_spec());
}

/// Indexed payload mutation preserves exact membership and resource owners at the public boundary.
pub fn indexed_allocation_exports_mutable_payload_frames(
    owner: &mut automation_structures::TypedAllocation<u64, u64,
        automation_structures::UnrestrictedAllocation, automation_structures::IndexedStorage>,
    key: u64, replacement: u64,
)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    match owner.get_query_mut(&key) {
        Some(value) => {
            *value = replacement;
            assert(has_resolved(value));
        },
        None => {},
    }
    assert(owner.inv());
    assert(owner.budgets_spec() == before.budgets_spec());
    assert(owner.entries_spec().len() == before.entries_spec().len());
    assert forall|i: int| 0 <= i < before.entries_spec().len() implies
        #[trigger] owner.entries_spec()[i].0 == before.entries_spec()[i].0
            && owner.entries_spec()[i].1.1 == before.entries_spec()[i].1.1 by {}
    assert forall|i: int| 0 <= i < before.entries_spec().len()
        && before.entries_spec()[i].0 != key implies
            #[trigger] owner.entries_spec()[i].1.0 == before.entries_spec()[i].1.0 by {}
}

/// Owner charge previews have exact read-only meanings, including an absent dimension.
pub fn indexed_allocation_exports_charge_preview(
    owner: &automation_structures::TypedAllocation<u64, u64,
        automation_structures::UnrestrictedAllocation, automation_structures::IndexedStorage>,
    dimension: usize, amount: u64,
)
    requires owner.inv(),
{
    let ghost before = *owner;
    let preview = owner.check_charge(dimension, amount);
    assert(preview == if dimension < owner.budgets_spec().len() {
        Some(owner.budgets_spec()[dimension as int].1.allocated as int + amount as int
            <= owner.budgets_spec()[dimension as int].1.capacity as int)
    } else { None });
    let members = owner.check_member_count(amount);
    assert(members == (owner.budgets_spec().len() == 0
        || owner.budgets_spec()[0].1.allocated as int + amount as int
            <= owner.budgets_spec()[0].1.capacity as int));
    assert(*owner == before);
}

/// Incremental refusal/cancellation preserves the accepted allocation through public contracts.
pub fn indexed_allocation_exports_incremental_preparation_frames(
    owner: &mut automation_structures::TypedAllocation<u64, u64,
        automation_structures::UnrestrictedAllocation, automation_structures::IndexedStorage>,
    key: u64, value: u64, charges: Vec<u64>,
)
    requires old(owner).inv(),
{
    let ghost before = *owner;
    match owner.prepare_batch_builder(1) {
        Ok(mut builder) => {
            match builder.try_push(key, value, charges) {
                Ok(()) => {
                    assert(builder.items_spec() == seq![(key,(value,charges))]);
                    assert(builder.before_spec().entries_spec() == before.entries_spec());
                    assert(builder.before_spec().budgets_spec() == before.budgets_spec());
                },
                Err(refused) => {
                    assert(refused.key == key && refused.value == value && refused.charges == charges);
                    assert(builder.items_spec().len() == 0);
                },
            }
            let returned = builder.cancel();
            assert(returned.reason == None);
        },
        Err(_) => {},
    }
    assert(owner.inv());
    assert(owner.entries_spec() == before.entries_spec());
    assert(owner.budgets_spec() == before.budgets_spec());
    assert(owner.domain_spec() == before.domain_spec());
}

/// Consuming projection transfers every original payload in order or returns the same owner.
pub fn indexed_allocation_exports_consuming_order(
    owner: automation_structures::TypedAllocation<u64, u64,
        automation_structures::UnrestrictedAllocation, automation_structures::IndexedStorage>,
)
    requires owner.inv(),
{
    let ghost before = owner;
    match owner.try_into_values() {
        Ok(values) => {
            assert(values@.len() == before.entries_spec().len());
            assert forall|i: int| 0 <= i < values@.len() implies
                #[trigger] values@[i] == before.entries_spec()[i].1.0 by {}
        },
        Err(returned) => { assert(returned == before); },
    }
}

}
