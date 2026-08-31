extern crate automation_structures;

use automation_structures::integration::governed_commit::{CommitPhase, GovernedCommit};

fn main() {
    let mut direct = GovernedCommit::new(41, 1, 2);
    let direct_ok = direct.admit();
    direct.propagate();
    direct.commit_success();

    let mut retry = GovernedCommit::new(42, 1, 2);
    let retry_admitted = retry.admit();
    retry.propagate();
    let first_failed = !retry.fail_before_effect();
    retry.commit_success();

    let mut partial = GovernedCommit::new(43, 1, 2);
    let partial_admitted = partial.admit();
    partial.propagate();
    partial.fail_after_effect();
    let partial_visible = partial.phase == CommitPhase::RecoveryPending
        && partial.effect_applied
        && partial.recovery_intent
        && !partial.evidence_persisted;
    partial.crash();
    let survived = partial.crashed
        && partial.effect_applied
        && partial.recovery_intent
        && !partial.evidence_persisted;
    partial.restart();
    partial.recover();

    let mut capacity_rejection = GovernedCommit::new(44, 0, 1);
    let rejected_for_capacity =
        !capacity_rejection.admit() && capacity_rejection.phase == CommitPhase::Rejected;

    let mut retry_exhaustion = GovernedCommit::new(45, 1, 1);
    let exhausted_admitted = retry_exhaustion.admit();
    retry_exhaustion.propagate();
    let terminal_failure = retry_exhaustion.fail_before_effect();

    let ok = direct_ok
        && direct.phase == CommitPhase::Committed
        && direct.budget.allocated == 1
        && direct.budget.reserved == 0
        && direct.audit.log.len() == 1
        && direct.evidence_persisted
        && direct.sequential.pc == 3
        && retry_admitted
        && first_failed
        && retry.attempt_budget.allocated == 2
        && retry.phase == CommitPhase::Committed
        && retry.audit.log.len() == 1
        && partial_admitted
        && partial_visible
        && survived
        && partial.phase == CommitPhase::Committed
        && partial.effect_applied
        && partial.evidence_persisted
        && !partial.recovery_intent
        && partial.audit.log.len() == 1
        && partial.sequential.pc == 3
        && rejected_for_capacity
        && exhausted_admitted
        && terminal_failure
        && retry_exhaustion.attempt_budget.allocated
            == retry_exhaustion.attempt_budget.capacity
        && retry_exhaustion.phase == CommitPhase::Rejected
        && !retry_exhaustion.effect_applied;

    if ok {
        println!("KAT_RESULT: SUCCESS (six-role governed-commit bridge)");
    } else {
        println!("KAT_RESULT: FAIL (six-role governed-commit bridge)");
        std::process::exit(1);
    }
}
