// Bounded executable slice used by the governed-commit semantic bridge.
//
// The slice owns the mapped ResourceRegistry, Budget, PropagationPass,
// ActuationPass, AuditSink, and Sequential carriers. It fixes one
// registry key, one seat, one work item, and a unit resource charge.  Those bounds
// make the cross-tool transition relation finite without changing the transferred
// claim: capacity safety and `Committed => durable audit evidence`.
//
// Runtime boundaries that Rust does not supply are explicit in the API:
//
// - `CommitOutcome` is the external-effect adapter result.  `FailureAfterEffect`
//   records a durable recovery intent before exposing the applied effect, so a
//   retry cannot duplicate the effect.
// - `crash` clears only the volatile process flag.  The six carrier states,
//   effect receipt, audit record, and recovery intent are the modeled durable
//   store and require the registered linearizable persistence provider.
// - scheduler fairness and eventual external-service success remain deployment
//   relies.  Safety and recovery-step correspondence do not assume either.
// - attempt arithmetic is guarded before increment; Budget performs its unit
//   admission in mathematical-integer specifications and overflow-safe u64 code.

use vstd::prelude::*;

use crate::modalities::sequential::Sequential;
use crate::primitives::actuation_pass::ActuationPass;
use crate::primitives::audit_sink::AuditSink;
use crate::primitives::budget::Budget;
use crate::primitives::propagation_pass::PropagationPass;
#[expect(
    unused_imports,
    reason = "Round appears in ghost specifications erased by rustc"
)]
use crate::primitives::propagation_pass::Round;
use crate::primitives::resource_registry::ResourceRegistry;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CommitPhase {
    Pending,
    Admitted,
    Ready,
    Retryable,
    RecoveryPending,
    Committed,
    Rejected,
}

/// Frozen abstract phases for the direct source-level refinement proof.  These
/// are the same five observations used by `GovernedCommitAbstract.tla`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AbstractPhase {
    Pending,
    Active,
    Recovering,
    Committed,
    Failed,
}

/// One bounded integrated request.  The component fields are the actual
/// executable carriers; the remaining fields expose the external effect,
/// persistence, failure, and recovery boundary absent from the individual rows.
pub struct GovernedCommit {
    pub registry: ResourceRegistry,
    pub budget: Budget,
    pub propagation: PropagationPass,
    pub actuation: ActuationPass,
    pub audit: AuditSink,
    pub sequential: Sequential,
    pub phase: CommitPhase,
    pub attempts: u64,
    pub max_attempts: u64,
    pub effect_applied: bool,
    pub evidence_persisted: bool,
    pub recovery_intent: bool,
    pub crashed: bool,
}

impl GovernedCommit {
    pub open spec fn abstract_phase(&self) -> AbstractPhase {
        if self.phase == CommitPhase::Pending {
            AbstractPhase::Pending
        } else if self.phase == CommitPhase::Admitted
            || self.phase == CommitPhase::Ready
            || self.phase == CommitPhase::Retryable
        {
            AbstractPhase::Active
        } else if self.phase == CommitPhase::RecoveryPending {
            AbstractPhase::Recovering
        } else if self.phase == CommitPhase::Committed {
            AbstractPhase::Committed
        } else {
            AbstractPhase::Failed
        }
    }

    pub open spec fn abstract_used(&self) -> int {
        self.budget.allocated as int + self.budget.reserved as int
    }

    /// The frozen abstract initial predicate, evaluated through the executable
    /// abstraction map above.
    pub open spec fn abstract_init(&self) -> bool {
        &&& self.abstract_phase() == AbstractPhase::Pending
        &&& self.abstract_used() == 0
        &&& !self.effect_applied
        &&& !self.evidence_persisted
        &&& !self.recovery_intent
    }

    /// Direct Verus counterpart of `AbstractSystemStep`.
    pub open spec fn abstract_system_step(
        pre: &GovernedCommit,
        post: &GovernedCommit,
    ) -> bool {
        &&& post.budget.capacity == pre.budget.capacity
        &&& post.effect_applied == pre.effect_applied
        &&& post.evidence_persisted == pre.evidence_persisted
        &&& post.recovery_intent == pre.recovery_intent
        &&& ((pre.abstract_phase() == AbstractPhase::Pending
                && post.abstract_phase() == AbstractPhase::Active
                && post.abstract_used() == 1)
            || (pre.abstract_phase() == AbstractPhase::Active
                && post.abstract_phase() == AbstractPhase::Active
                && post.abstract_used() == pre.abstract_used()))
    }

    /// Direct Verus counterpart of `AbstractFailureStep`.  Rejection, retry,
    /// partial failure, and crash are exhaustive named arms.
    pub open spec fn abstract_failure_step(
        pre: &GovernedCommit,
        post: &GovernedCommit,
    ) -> bool {
        &&& post.budget.capacity == pre.budget.capacity
        &&& ((post.abstract_phase() == AbstractPhase::Failed
                && post.abstract_used() == pre.abstract_used()
                && post.effect_applied == pre.effect_applied
                && post.evidence_persisted == pre.evidence_persisted
                && post.recovery_intent == pre.recovery_intent)
            || (pre.abstract_phase() == AbstractPhase::Active
                && post.abstract_phase() == AbstractPhase::Active
                && post.abstract_used() == pre.abstract_used()
                && post.effect_applied == pre.effect_applied
                && post.evidence_persisted == pre.evidence_persisted
                && post.recovery_intent == pre.recovery_intent)
            || (pre.abstract_phase() == AbstractPhase::Active
                && post.abstract_phase() == AbstractPhase::Recovering
                && post.abstract_used() == pre.abstract_used()
                && post.effect_applied
                && !post.evidence_persisted
                && post.recovery_intent)
            || (post.abstract_phase() == pre.abstract_phase()
                && post.abstract_used() == pre.abstract_used()
                && post.effect_applied == pre.effect_applied
                && post.evidence_persisted == pre.evidence_persisted
                && post.recovery_intent == pre.recovery_intent))
    }

    /// Direct Verus counterpart of `AbstractCommitStep`.
    pub open spec fn abstract_commit_step(
        pre: &GovernedCommit,
        post: &GovernedCommit,
    ) -> bool {
        &&& (pre.abstract_phase() == AbstractPhase::Active
            || pre.abstract_phase() == AbstractPhase::Recovering)
        &&& post.abstract_phase() == AbstractPhase::Committed
        &&& post.budget.capacity == pre.budget.capacity
        &&& post.abstract_used() == 1
        &&& post.effect_applied
        &&& post.evidence_persisted
        &&& !post.recovery_intent
    }

    /// Direct Verus counterpart of the registered restart stutter.
    pub open spec fn abstract_stutter_step(
        pre: &GovernedCommit,
        post: &GovernedCommit,
    ) -> bool {
        &&& post.abstract_phase() == pre.abstract_phase()
        &&& post.budget.capacity == pre.budget.capacity
        &&& post.abstract_used() == pre.abstract_used()
        &&& post.effect_applied == pre.effect_applied
        &&& post.evidence_persisted == pre.evidence_persisted
        &&& post.recovery_intent == pre.recovery_intent
    }

    /// Concrete and abstract external observations agree by the frozen phase
    /// projection; effect and audit fields are identity-mapped.
    pub open spec fn abstract_observation_agrees(&self) -> bool {
        &&& ((self.phase == CommitPhase::Committed)
            == (self.abstract_phase() == AbstractPhase::Committed))
        &&& ((self.phase == CommitPhase::Rejected
                || self.phase == CommitPhase::RecoveryPending)
            == (self.abstract_phase() == AbstractPhase::Failed
                || self.abstract_phase() == AbstractPhase::Recovering))
    }

    pub proof fn prove_observation_agreement(&self)
        ensures self.abstract_observation_agrees(),
    {
    }

    pub open spec fn component_invariants(&self) -> bool {
        &&& self.registry.unique_mapping()
        &&& self.budget.safety_invariant()
        &&& self.propagation.inv()
        &&& self.actuation.invariant()
        &&& self.audit.inv()
        &&& self.sequential.inv()
    }

    pub open spec fn integrated_coupling(&self) -> bool {
        &&& self.max_attempts > 0
        &&& self.attempts <= self.max_attempts
        &&& self.propagation.num_nodes == 1
        &&& self.propagation.max_iterations == 1
        &&& self.propagation.max_value == 0
        &&& self.propagation.edges@.len() == 0
        &&& self.registry.contains_key(0)
        &&& self.actuation.num_seats == 1
        &&& self.actuation.allocation@.len() == 1
        &&& self.actuation.allocation@[0] is Some
        &&& self.actuation.effects@.len() == 1
        &&& self.audit.max_log_len == 1
        &&& self.sequential.steps == 3
        &&& self.sequential.value_domain_size == 4
        &&& !self.sequential.active
        &&& (self.effect_applied == (self.actuation.effects@[0] is Some))
        &&& (self.evidence_persisted == (self.audit.log@.len() == 1))
        &&& (self.phase == CommitPhase::Pending ==> self.sequential.pc == 0)
        &&& (self.phase == CommitPhase::Pending
                ==> self.budget.allocated == 0
                    && self.budget.reserved == 0
                    && !self.effect_applied
                    && !self.evidence_persisted
                    && !self.recovery_intent)
        &&& (self.phase == CommitPhase::Admitted ==> self.sequential.pc == 1)
        &&& (self.phase == CommitPhase::Ready
             || self.phase == CommitPhase::Retryable
             || self.phase == CommitPhase::RecoveryPending
                ==> self.sequential.pc == 2)
        &&& (self.phase == CommitPhase::Committed ==> self.sequential.pc == 3)
        &&& (self.phase == CommitPhase::Admitted
             || self.phase == CommitPhase::Ready
             || self.phase == CommitPhase::Retryable
             || self.phase == CommitPhase::RecoveryPending
                ==> self.budget.reserved == 1)
        &&& (self.phase == CommitPhase::Admitted
             || self.phase == CommitPhase::Ready
             || self.phase == CommitPhase::Retryable
                ==> self.budget.allocated == 0
                    && !self.effect_applied
                    && !self.evidence_persisted
                    && !self.recovery_intent)
        &&& (self.phase == CommitPhase::Rejected
                ==> !self.effect_applied && !self.evidence_persisted && !self.recovery_intent)
        &&& (self.phase == CommitPhase::RecoveryPending
                ==> self.budget.allocated == 0
                    && self.effect_applied
                    && self.recovery_intent
                    && !self.evidence_persisted)
        &&& (self.phase == CommitPhase::Committed
                ==> self.effect_applied
                    && self.evidence_persisted
                    && !self.recovery_intent
                    && self.budget.allocated == 1
                    && self.budget.reserved == 0)
    }

    pub open spec fn inv(&self) -> bool {
        self.component_invariants() && self.integrated_coupling()
    }

    /// The exact bounded guarantee transferred by the semantic bridge.
    pub open spec fn transferred_guarantee(&self) -> bool {
        &&& self.budget.used() <= self.budget.capacity as int
        &&& (self.phase == CommitPhase::Committed ==> self.evidence_persisted)
    }

    pub fn new(resource: u64, capacity: u64, max_attempts: u64) -> (s: GovernedCommit)
        requires capacity <= 1, 0 < max_attempts <= 2,
        ensures
            s.inv(),
            s.transferred_guarantee(),
            s.abstract_init(),
            s.abstract_observation_agrees(),
            s.phase == CommitPhase::Pending,
            s.attempts == 0,
            !s.effect_applied,
            !s.evidence_persisted,
            !s.recovery_intent,
            !s.crashed,
            s.budget.capacity == capacity,
            s.max_attempts == max_attempts,
    {
        let mut registry = ResourceRegistry::new();
        registry.register(0, resource);

        let budget = Budget::new(capacity);

        let edges: Vec<(usize, usize)> = Vec::new();
        let mut values: Vec<u64> = Vec::new();
        values.push(0);
        let propagation = PropagationPass::new(1, 1, 0, edges, values);

        let mut allocation: Vec<Option<u64>> = Vec::new();
        allocation.push(Some(resource));
        let actuation = ActuationPass::new(allocation, 1);

        let audit = AuditSink::new(1);
        let sequential = Sequential::new(3, 4, 0);

        GovernedCommit {
            registry,
            budget,
            propagation,
            actuation,
            audit,
            sequential,
            phase: CommitPhase::Pending,
            attempts: 0,
            max_attempts,
            effect_applied: false,
            evidence_persisted: false,
            recovery_intent: false,
            crashed: false,
        }
    }

    fn advance(sequential: &mut Sequential, next_value: u64)
        requires
            old(sequential).inv(),
            old(sequential).pc < old(sequential).steps,
            !old(sequential).active,
            next_value < old(sequential).value_domain_size,
        ensures
            final(sequential).inv(),
            final(sequential).steps == old(sequential).steps,
            final(sequential).value_domain_size == old(sequential).value_domain_size,
            final(sequential).pc == old(sequential).pc + 1,
            !final(sequential).active,
            final(sequential).value == next_value,
    {
        let began = sequential.begin_step();
        let _ = began;
        assert(began);
        let completed = sequential.complete_step(next_value);
        let _ = completed;
        assert(completed);
    }

    /// Budget admission.  Capacity rejection is an explicit terminal API result
    /// and leaves every claim-bearing carrier other than the phase unchanged.
    pub fn admit(&mut self) -> (accepted: bool)
        requires
            old(self).inv(),
            !old(self).crashed,
            old(self).phase == CommitPhase::Pending,
            old(self).sequential.pc == 0,
        ensures
            final(self).component_invariants(),
            final(self).integrated_coupling(),
            final(self).transferred_guarantee(),
            accepted ==> Self::abstract_system_step(old(self), final(self)),
            !accepted ==> Self::abstract_failure_step(old(self), final(self)),
            accepted == (old(self).budget.used() + 1 <= old(self).budget.capacity as int),
            accepted ==> final(self).phase == CommitPhase::Admitted,
            !accepted ==> final(self).phase == CommitPhase::Rejected,
            final(self).attempts == old(self).attempts,
            final(self).effect_applied == old(self).effect_applied,
            final(self).evidence_persisted == old(self).evidence_persisted,
    {
        let accepted = self.budget.reserve(1);
        if accepted {
            Self::advance(&mut self.sequential, 1);
            self.phase = CommitPhase::Admitted;
        } else {
            self.phase = CommitPhase::Rejected;
        }
        accepted
    }

    /// Run the one-node propagation witness and advance the Sequential carrier.
    /// This is the bounded readiness stage between admission and effect commit.
    pub fn propagate(&mut self)
        requires
            old(self).inv(),
            !old(self).crashed,
            old(self).phase == CommitPhase::Admitted,
            old(self).sequential.pc == 1,
            old(self).propagation.round == Round::Idle,
            old(self).propagation.changed,
            old(self).propagation.iteration == 0,
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_system_step(old(self), final(self)),
            final(self).phase == CommitPhase::Ready,
            final(self).sequential.pc == 2,
            final(self).propagation.iteration == 1,
            final(self).propagation.round == Round::Idle,
            !final(self).propagation.changed,
    {
        self.propagation.start_round();
        self.propagation.update_node(0);
        assert(self.propagation.all_updated());
        assert(self.propagation.values@ == self.propagation.snapshot@);
        self.propagation.end_round();
        Self::advance(&mut self.sequential, 2);
        self.phase = CommitPhase::Ready;
    }

    /// Record a failed external-service attempt before any effect occurred.
    /// Calling this action again from `Retryable` is the explicit bounded retry
    /// path; the last permitted failure is a terminal rejection.
    pub fn fail_before_effect(&mut self) -> (terminal: bool)
        requires
            old(self).inv(),
            !old(self).crashed,
            old(self).phase == CommitPhase::Ready
                || old(self).phase == CommitPhase::Retryable,
            old(self).attempts < old(self).max_attempts,
            old(self).sequential.pc == 2,
            !old(self).effect_applied,
            !old(self).evidence_persisted,
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_failure_step(old(self), final(self)),
            final(self).attempts == old(self).attempts + 1,
            final(self).effect_applied == old(self).effect_applied,
            final(self).evidence_persisted == old(self).evidence_persisted,
            final(self).recovery_intent == old(self).recovery_intent,
            final(self).attempts < final(self).max_attempts ==>
                !terminal && final(self).phase == CommitPhase::Retryable,
            final(self).attempts == final(self).max_attempts ==>
                terminal && final(self).phase == CommitPhase::Rejected,
    {
        self.attempts = self.attempts + 1;
        if self.attempts == self.max_attempts {
            self.phase = CommitPhase::Rejected;
            true
        } else {
            self.phase = CommitPhase::Retryable;
            false
        }
    }

    /// Record the external effect together with a durable recovery intent, then
    /// expose the modeled failure before the audit evidence commit. The effect must not
    /// be retried; only `recover` may complete this state.
    pub fn fail_after_effect(&mut self)
        requires
            old(self).inv(),
            !old(self).crashed,
            old(self).phase == CommitPhase::Ready
                || old(self).phase == CommitPhase::Retryable,
            old(self).attempts < old(self).max_attempts,
            old(self).sequential.pc == 2,
            !old(self).effect_applied,
            !old(self).evidence_persisted,
            old(self).audit.log@.len() == 0,
            old(self).actuation.effects@[0] is None,
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_failure_step(old(self), final(self)),
            final(self).attempts == old(self).attempts + 1,
            final(self).phase == CommitPhase::RecoveryPending,
            final(self).effect_applied,
            !final(self).evidence_persisted,
            final(self).recovery_intent,
    {
        self.attempts = self.attempts + 1;
        // The durable intent precedes the effect receipt at this API boundary.
        self.recovery_intent = true;
        self.actuation.actuate(0);
        self.effect_applied = true;
        self.phase = CommitPhase::RecoveryPending;
    }

    /// Atomic success boundary for the bounded persistence adapter: effect
    /// receipt, unit-budget commit, audit append, and sequential closure become
    /// visible together at method return.
    pub fn commit_success(&mut self)
        requires
            old(self).inv(),
            !old(self).crashed,
            old(self).phase == CommitPhase::Ready
                || old(self).phase == CommitPhase::Retryable,
            old(self).attempts < old(self).max_attempts,
            old(self).sequential.pc == 2,
            !old(self).effect_applied,
            !old(self).evidence_persisted,
            old(self).audit.log@.len() == 0,
            old(self).actuation.effects@[0] is None,
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_commit_step(old(self), final(self)),
            final(self).attempts == old(self).attempts + 1,
            final(self).phase == CommitPhase::Committed,
            final(self).effect_applied,
            final(self).evidence_persisted,
            !final(self).recovery_intent,
            final(self).sequential.pc == 3,
    {
        self.attempts = self.attempts + 1;
        self.actuation.actuate(0);
        self.effect_applied = true;
        self.budget.commit_reservation(1);
        let recorded = self.audit.record(0);
        let _ = recorded;
        assert(recorded);
        self.evidence_persisted = true;
        self.recovery_intent = false;
        Self::advance(&mut self.sequential, 3);
        self.phase = CommitPhase::Committed;
    }

    /// Finish a partial failure without reissuing the already applied effect.
    pub fn recover(&mut self)
        requires
            old(self).inv(),
            !old(self).crashed,
            old(self).phase == CommitPhase::RecoveryPending,
            old(self).sequential.pc == 2,
            old(self).audit.log@.len() == 0,
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_commit_step(old(self), final(self)),
            final(self).phase == CommitPhase::Committed,
            final(self).effect_applied,
            final(self).evidence_persisted,
            !final(self).recovery_intent,
            final(self).sequential.pc == 3,
    {
        self.budget.commit_reservation(1);
        let recorded = self.audit.record(0);
        let _ = recorded;
        assert(recorded);
        self.evidence_persisted = true;
        self.recovery_intent = false;
        Self::advance(&mut self.sequential, 3);
        self.phase = CommitPhase::Committed;
    }

    /// Crash only the volatile process boundary.  All fields named by the
    /// persistence abstraction remain unchanged and therefore survive restart.
    pub fn crash(&mut self)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_failure_step(old(self), final(self)),
            final(self).crashed,
            final(self).phase == old(self).phase,
            final(self).effect_applied == old(self).effect_applied,
            final(self).evidence_persisted == old(self).evidence_persisted,
            final(self).recovery_intent == old(self).recovery_intent,
    {
        self.crashed = true;
    }

    pub fn restart(&mut self)
        requires old(self).inv(), old(self).crashed,
        ensures
            final(self).inv(),
            final(self).transferred_guarantee(),
            Self::abstract_stutter_step(old(self), final(self)),
            !final(self).crashed,
            final(self).phase == old(self).phase,
            final(self).effect_applied == old(self).effect_applied,
            final(self).evidence_persisted == old(self).evidence_persisted,
            final(self).recovery_intent == old(self).recovery_intent,
    {
        self.crashed = false;
    }
}

}
