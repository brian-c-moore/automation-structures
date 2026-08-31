// Phase-aware convergence-governor executable correspondence boundary.
//
// A sub-threshold delta is classified differently before and after a threshold
// event. The gradient_phase field records that classification, and the
// peak_observed latch prevents COOLING from carrying a COLD phase. The TLA+
// `ConvergenceGovernorPhaseAware` spec has four state variables —
// state, gradient_phase, delta_history, peak_observed — and its .cfg checks
// four invariants:
//
//   TypeInvariant             == well-typed (state/phase enums, len<=Window, peak bool)
//   NoCoolingFromCold         == state = COOLING => gradient_phase /= COLD
//   ConvergenceRequiresHistory== state ∈ {COOLING,CONVERGED} => peak_observed
//   ConvergedRequiresPeak     == state = CONVERGED => peak_observed
//
// All four are discharged under the full Update dynamics. The inductive proof
// carries the `WarmStateRequiresPeak` strengthening:
//   peak_implies: state ∈ {COOLING,CONVERGED,AWAKENED} => peak_observed
// (the AWAKENED case is required to close the AWAKENED -> CONVERGED step).
// ConvergenceRequiresHistory and ConvergedRequiresPeak then follow as weakenings.
// NoCoolingFromCold holds because the only routes into COOLING either force
// new_peak (ACTIVE -> COOLING) or stay in COOLING where peak_observed was
// already TRUE, and ClassifyPhase returns COLD only when peak is FALSE.
//
// `update` computes the post-slide window average internally. Callers supply
// only the new delta, so ordinary Rust and verified callers share one
// transition boundary.

use vstd::prelude::*;

verus! {

/// Governor state. Enum => `state ∈ GovernorStates` holds by construction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GovState {
    /// Learning remains active.
    Active,
    /// A peak was observed and the recent average is declining.
    Cooling,
    /// The recent average is below the convergence threshold.
    Converged,
    /// Activity after convergence exceeded the awakening threshold.
    Awakened,
}

/// Gradient-trajectory phase. Enum => `gradient_phase ∈ GradientPhases` by
/// construction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    /// No peak has been observed and the delta remains below threshold.
    Cold,
    /// The first threshold event has been observed.
    Warming,
    /// A post-peak delta is at or above threshold.
    ActiveLearning,
    /// A post-peak delta is below threshold.
    Declining,
}

/// A phase-aware convergence governor.
pub struct ConvergenceGovernorPhaseAware {
    /// Delta threshold used for convergence classification.
    pub threshold: u64,
    /// Window-sum threshold that reawakens a converged governor.
    pub awaken_threshold: u64,
    /// Maximum retained delta-history length.
    pub window: usize,
    /// Inclusive ceiling of observed delta values.
    pub max_delta: u64,
    /// Current convergence state.
    pub state: GovState,
    /// Current gradient-trajectory phase.
    pub gradient_phase: Phase,
    /// Retained recent deltas from oldest to newest.
    pub delta_history: Vec<u64>,
    /// Whether any threshold-reaching delta has been observed.
    pub peak_observed: bool,
}

impl ConvergenceGovernorPhaseAware {
    // ── Phase classification (TLA+ ClassifyPhase) ───────────────────────

    /// Classify the current delta and pre-step peak latch. `Declining` records
    /// a sub-threshold delta after the latch; it does not assert monotonicity.
    pub open spec fn classify_phase_spec(delta: u64, peak: bool, threshold: u64) -> Phase {
        if !peak && delta < threshold {
            Phase::Cold
        } else if !peak && delta >= threshold {
            Phase::Warming
        } else if peak && delta >= threshold {
            Phase::ActiveLearning
        } else {
            Phase::Declining
        }
    }

    /// Executable ClassifyPhase.
    pub fn classify_phase(delta: u64, peak: bool, threshold: u64) -> (p: Phase)
        ensures p == Self::classify_phase_spec(delta, peak, threshold),
    {
        if !peak && delta < threshold {
            Phase::Cold
        } else if !peak && delta >= threshold {
            Phase::Warming
        } else if peak && delta >= threshold {
            Phase::ActiveLearning
        } else {
            Phase::Declining
        }
    }

    // ── Transition (TLA+ Update state CASE) ─────────────────────────────

    /// State transition corresponding to the TLA+ `Update` CASE expression.
    /// ACTIVE -> COOLING requires the post-step peak latch.
    pub open spec fn next_state_spec(s: GovState, avg: u64, new_peak: bool, threshold: u64, awaken: u64)
        -> GovState {
        match s {
            GovState::Active =>
                if avg < threshold * 2 && new_peak { GovState::Cooling } else { GovState::Active },
            GovState::Cooling =>
                if avg < threshold { GovState::Converged }
                else if avg >= threshold * 2 { GovState::Active }
                else { GovState::Cooling },
            GovState::Converged =>
                if avg > awaken { GovState::Awakened } else { GovState::Converged },
            GovState::Awakened =>
                if avg < threshold { GovState::Converged } else { GovState::Awakened },
        }
    }

    /// Executable transition.
    pub fn next_state(s: GovState, avg: u64, new_peak: bool, threshold: u64, awaken: u64)
        -> (out: GovState)
        requires threshold <= u64::MAX / 2,
        ensures out == Self::next_state_spec(s, avg, new_peak, threshold, awaken),
    {
        match s {
            GovState::Active =>
                if avg < threshold * 2 && new_peak { GovState::Cooling } else { GovState::Active },
            GovState::Cooling =>
                if avg < threshold { GovState::Converged }
                else if avg >= threshold * 2 { GovState::Active }
                else { GovState::Cooling },
            GovState::Converged =>
                if avg > awaken { GovState::Awakened } else { GovState::Converged },
            GovState::Awakened =>
                if avg < threshold { GovState::Converged } else { GovState::Awakened },
        }
    }

    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ `TypeInvariant`'s window clause (+ the overflow / nonempty-window
    /// bounds; the enum and bool clauses are carried by the types).
    pub open spec fn type_invariant(&self) -> bool {
        self.delta_history.len() <= self.window
            && self.threshold <= u64::MAX / 2
            && self.window >= 1
            && self.window as int * self.max_delta as int <= u64::MAX as int
            && forall|i: int| 0 <= i < self.delta_history.len() ==>
                #[trigger] self.delta_history@[i] <= self.max_delta
    }

    /// `WarmStateRequiresPeak` strengthening: any non-ACTIVE state implies a
    /// peak was observed. Includes AWAKENED so AWAKENED -> CONVERGED preserves it.
    pub open spec fn peak_implies(&self) -> bool {
        (self.state == GovState::Cooling || self.state == GovState::Converged
            || self.state == GovState::Awakened) ==> self.peak_observed
    }

    /// TLA+ `NoCoolingFromCold`.
    pub open spec fn no_cooling_from_cold(&self) -> bool {
        self.state == GovState::Cooling ==> self.gradient_phase != Phase::Cold
    }

    /// TLA+ `ConvergenceRequiresHistory` (a weakening of peak_implies).
    pub open spec fn convergence_requires_history(&self) -> bool {
        (self.state == GovState::Cooling || self.state == GovState::Converged) ==> self.peak_observed
    }

    /// TLA+ `ConvergedRequiresPeak` (a weakening of peak_implies).
    pub open spec fn converged_requires_peak(&self) -> bool {
        self.state == GovState::Converged ==> self.peak_observed
    }

    /// Full maintained invariant.
    pub open spec fn inv(&self) -> bool {
        self.type_invariant() && self.peak_implies() && self.no_cooling_from_cold()
    }

    /// TLA+ `SumSeq`: the sum of a delta window.
    pub open spec fn sum_seq(s: Seq<u64>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::sum_seq(s.take(s.len() - 1)) + s[s.len() - 1] as int
        }
    }

    /// Extending a delta sequence extends its mathematical sum by that delta.
    pub proof fn lemma_sum_push(s: Seq<u64>, delta: u64)
        ensures Self::sum_seq(s.push(delta)) == Self::sum_seq(s) + delta as int,
    {
        assert(s.push(delta).take(s.len() as int) =~= s);
    }

    /// TLA+ `Update`'s `new_history`: drop the oldest when the window is full,
    /// then append the new delta. A function of the PRE-state and `delta` only.
    pub open spec fn slide_window(&self, delta: u64) -> Seq<u64> {
        if self.delta_history@.len() >= self.window {
            self.delta_history@.drop_first().push(delta)
        } else {
            self.delta_history@.push(delta)
        }
    }

    /// TLA+ `Update`'s `avg`. The slid window is never empty (`type_invariant`
    /// carries `window >= 1`), so the division is well defined.
    pub open spec fn window_avg(&self, delta: u64) -> int {
        Self::sum_seq(self.slide_window(delta)) / self.slide_window(delta).len() as int
    }

    // ── Init (TLA+ Init) ────────────────────────────────────────────────

    /// Start ACTIVE / COLD / no peak. Realises the TLA+ `Init`.
    pub fn new(threshold: u64, awaken_threshold: u64, window: usize, max_delta: u64)
        -> (g: ConvergenceGovernorPhaseAware)
        requires
            threshold <= u64::MAX / 2,
            window >= 1,
            window as int * max_delta as int <= u64::MAX as int,
        ensures
            g.threshold == threshold,
            g.awaken_threshold == awaken_threshold,
            g.window == window,
            g.max_delta == max_delta,
            g.state == GovState::Active,
            g.gradient_phase == Phase::Cold,
            g.delta_history@.len() == 0,
            g.peak_observed == false,
            g.inv(),
    {
        ConvergenceGovernorPhaseAware {
            threshold, awaken_threshold, window, max_delta,
            state: GovState::Active, gradient_phase: Phase::Cold, delta_history: Vec::new(),
            peak_observed: false,
        }
    }

    // ── Update (TLA+ Update) ────────────────────────────────────────────

    /// One governor step: classify the phase, update the peak latch, slide the
    /// window, compute its average, and transition. Realises the TLA+
    /// `Update(delta)` and re-establishes all four checked invariants.
    pub fn update(&mut self, delta: u64) -> (avg: u64)
        requires
            old(self).inv(),
            delta <= old(self).max_delta,
        ensures
            avg as int == old(self).window_avg(delta),
            final(self).threshold == old(self).threshold,
            final(self).awaken_threshold == old(self).awaken_threshold,
            final(self).window == old(self).window,
            final(self).max_delta == old(self).max_delta,
            final(self).gradient_phase
                == Self::classify_phase_spec(delta, old(self).peak_observed, old(self).threshold),
            final(self).peak_observed == (old(self).peak_observed || delta >= old(self).threshold),
            final(self).state == Self::next_state_spec(
                old(self).state, avg,
                old(self).peak_observed || delta >= old(self).threshold,
                old(self).threshold, old(self).awaken_threshold),
            // Transition fidelity: `type_invariant()` bounds only
            // the post-state window's LENGTH; without this the contract admits
            // a governor that classifies the phase and transitions correctly and
            // never records the delta.
            final(self).delta_history@ == old(self).slide_window(delta),
            final(self).type_invariant(),
            final(self).no_cooling_from_cold(),
            final(self).convergence_requires_history(),
            final(self).converged_requires_peak(),
            final(self).inv(),
    {
        let old_peak = self.peak_observed;
        let old_state = self.state;
        let new_phase = Self::classify_phase(delta, old_peak, self.threshold);
        let new_peak = old_peak || (delta >= self.threshold);
        let ghost pre_hist = self.delta_history@;
        if self.delta_history.len() >= self.window {
            self.delta_history.remove(0);
            assert(self.delta_history@ =~= pre_hist.drop_first());
        }
        self.delta_history.push(delta);
        assert(self.delta_history@ =~= old(self).slide_window(delta));
        proof {
            assert(self.delta_history.len() <= self.window);
            assert(self.delta_history.len() as int * self.max_delta as int
                <= self.window as int * self.max_delta as int) by (nonlinear_arith)
                requires
                    self.delta_history.len() <= self.window,
                    self.max_delta >= 0;
        }
        let avg = Self::history_average(&self.delta_history, self.max_delta);
        let new_state = Self::next_state(
            old_state,
            avg,
            new_peak,
            self.threshold,
            self.awaken_threshold,
        );
        self.gradient_phase = new_phase;
        self.peak_observed = new_peak;
        self.state = new_state;
        avg
    }

    fn history_average(history: &Vec<u64>, _max_delta: u64) -> (average: u64)
        requires
            history.len() >= 1,
            history.len() as int * _max_delta as int <= u64::MAX as int,
            forall|i: int| 0 <= i < history.len() ==>
                #[trigger] history@[i] <= _max_delta,
        ensures average as int == Self::sum_seq(history@) / history.len() as int,
    {
        let mut total: u64 = 0;
        let mut index: usize = 0;
        while index < history.len()
            invariant
                index <= history.len(),
                total as int == Self::sum_seq(history@.take(index as int)),
                total as int <= index as int * _max_delta as int,
                index as int * _max_delta as int <= u64::MAX as int,
                history.len() as int * _max_delta as int <= u64::MAX as int,
                forall|i: int| 0 <= i < history.len() ==>
                    #[trigger] history@[i] <= _max_delta,
            decreases history.len() - index,
        {
            proof {
                Self::lemma_sum_push(history@.take(index as int), history@[index as int]);
                assert(history@.take(index as int + 1)
                    =~= history@.take(index as int).push(history@[index as int]));
                assert(total as int + history@[index as int] as int
                    <= (index as int + 1) * _max_delta as int) by (nonlinear_arith)
                    requires
                        total as int <= index as int * _max_delta as int,
                        history@[index as int] <= _max_delta;
                assert((index as int + 1) * _max_delta as int
                    <= history.len() as int * _max_delta as int) by (nonlinear_arith)
                    requires
                        index + 1 <= history.len(),
                        _max_delta >= 0;
            }
            total = total + history[index];
            index = index + 1;
        }
        assert(history@.take(history.len() as int) =~= history@);
        assert(total as int == Self::sum_seq(history@));
        let denominator = history.len() as u64;
        assert(denominator > 0);
        let average = total / denominator;
        assert(average as int == total as int / denominator as int);
        assert(denominator as int == history.len() as int);
        assert(average as int == Self::sum_seq(history@) / history.len() as int);
        average
    }
}

}
