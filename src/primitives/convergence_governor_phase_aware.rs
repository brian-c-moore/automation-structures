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

use crate::connectives::buffer::{Buffer, BufferStorage, MirroredU64Storage};
use crate::primitives::budget::Budget;
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

mod governor_history_seal { pub trait Sealed {} }

/// Sealed history binding beneath the one phase-aware Governor transition.
pub trait GovernorHistory: governor_history_seal::Sealed + View<V = Seq<u64>> {
    /// Representation coupling to the unchanged Governor configuration.
    spec fn coupled(&self, window: usize, max_delta: u64) -> bool;
    /// Number of retained deltas.
    fn len(&self) -> (length: usize) ensures length == self@.len();
    /// Whether the same retained history has no deltas.
    fn is_empty(&self) -> (empty: bool)
        ensures empty == (self@.len() == 0),
    { self.len() == 0 }
    /// Borrow the exact chronological retained history.
    fn as_slice(&self) -> (values: &[u64]) ensures values@ == self@;
    /// Read one chronological position, preserving the ordinary optional accessor.
    fn value_at(&self, index: usize) -> (value: Option<u64>)
        ensures value == if index < self@.len() { Some(self@[index as int]) } else { None };
    /// Commit the exact slide and return its floor average.
    fn step(&mut self, delta: u64, window: usize, max_delta: u64) -> (average: u64)
        requires old(self).coupled(window, max_delta), old(self)@.len() <= window,
            window >= 1, window as int * max_delta as int <= u64::MAX,
            delta <= max_delta,
            forall|i: int| 0 <= i < old(self)@.len() ==> #[trigger] old(self)@[i] <= max_delta,
        ensures final(self).coupled(window, max_delta),
            final(self)@ == if old(self)@.len() >= window {
                old(self)@.drop_first().push(delta)
            } else { old(self)@.push(delta) },
            average as int == ConvergenceGovernorPhaseAware::sum_seq(final(self)@)
                / final(self)@.len() as int;
}
impl governor_history_seal::Sealed for Vec<u64> {}
impl GovernorHistory for Vec<u64> {
    open spec fn coupled(&self, _window: usize, _max_delta: u64) -> bool { true }
    fn len(&self) -> (length: usize) { self.len() }
    fn as_slice(&self) -> (values: &[u64]) { self.as_slice() }
    #[expect(clippy::indexing_slicing, reason = "the chronological index guard bounds the original Vec read")]
    fn value_at(&self, index: usize) -> (value: Option<u64>) {
        if index < self.len() { Some(self[index]) } else { None }
    }
    fn step(&mut self, delta: u64, window: usize, max_delta: u64) -> (average: u64) {
        let ghost before = self@;
        if self.len() >= window { self.remove(0); }
        self.push(delta);
        assert(self@ == if before.len() >= window { before.drop_first().push(delta) }
            else { before.push(delta) });
        assert(self@.len() as int * max_delta as int <= u64::MAX) by (nonlinear_arith)
            requires self@.len() <= window, window as int * max_delta as int <= u64::MAX,
                max_delta >= 0;
        ConvergenceGovernorPhaseAware::history_average(self, max_delta)
    }
}

/// Checked history: Buffer owns order and storage; Budget owns the exact retained sum.
pub struct BufferedGovernorHistory {
    history: Buffer<u64, MirroredU64Storage>,
    sum: Budget,
}
impl View for BufferedGovernorHistory {
    type V = Seq<u64>;
    closed spec fn view(&self) -> Seq<u64> { self.history.values@ }
}
impl BufferedGovernorHistory {
    #[expect(clippy::arithmetic_side_effects, reason = "the unchanged Governor product bound makes the Budget ceiling representable")]
    fn new(window: usize, max_delta: u64) -> (history: Self)
        requires window >= 1, window as int * max_delta as int <= u64::MAX,
        ensures history@ == Seq::<u64>::empty(), history.coupled(window, max_delta),
    {
        let capacity = window as u64 * max_delta;
        Self { history: Buffer::with_storage(window), sum: Budget::new(capacity) }
    }
}
impl governor_history_seal::Sealed for BufferedGovernorHistory {}
impl GovernorHistory for BufferedGovernorHistory {
    closed spec fn coupled(&self, window: usize, max_delta: u64) -> bool {
        &&& self.history.well_formed() && self.history.capacity == window
        &&& self.sum.safety_invariant()
        &&& self.sum.capacity as int == window as int * max_delta as int
        &&& self.sum.reserved == 0 && self.sum.pending_eviction == 0
        &&& self.sum.allocated as int == ConvergenceGovernorPhaseAware::sum_seq(self.history.values@)
    }
    fn len(&self) -> (length: usize) { self.history.len() }
    fn as_slice(&self) -> (values: &[u64]) { self.history.as_slice() }
    fn value_at(&self, index: usize) -> (value: Option<u64>) {
        assert(self@ == self.history.values@);
        match self.history.values.value_at(index) {
            Some(value) => {
                assert(index < self@.len());
                assert(*value == self@[index as int]);
                Some(*value)
            }
            None => {
                assert(index >= self@.len());
                None
            }
        }
    }
    #[expect(clippy::integer_division, reason = "the committed nonempty history defines its exact floor average")]
    #[expect(clippy::arithmetic_side_effects, reason = "the committed nonempty history proves the division denominator is positive")]
    fn step(&mut self, delta: u64, window: usize, _max_delta: u64) -> (average: u64) {
        let ghost before = self@;
        proof { self.history.expose_capacity_bound(); }
        if self.history.len() >= window {
            proof { ConvergenceGovernorPhaseAware::lemma_sum_drop(before); }
            let removed = match self.history.pop() {
                Some(value) => value,
                None => { assert(false); 0 },
            };
            assert(removed == before[0]);
            proof {
                ConvergenceGovernorPhaseAware::lemma_sum_bound(self@, _max_delta);
                assert(0 <= ConvergenceGovernorPhaseAware::sum_seq(self@));
                assert(removed <= self.sum.allocated);
            }
            self.sum.release(removed);
            assert(self.sum.allocated as int == ConvergenceGovernorPhaseAware::sum_seq(self@));
        }
        proof {
            ConvergenceGovernorPhaseAware::lemma_sum_bound(self@, _max_delta);
            assert(self@.len() < window);
            assert(self.sum.used() + delta as int <= self.sum.capacity as int) by (nonlinear_arith)
                requires self.sum.used() == ConvergenceGovernorPhaseAware::sum_seq(self@),
                    ConvergenceGovernorPhaseAware::sum_seq(self@) <= self@.len() * _max_delta as int,
                    self@.len() < window, delta <= _max_delta,
                    self.sum.capacity as int == window as int * _max_delta as int;
            ConvergenceGovernorPhaseAware::lemma_sum_push(self@, delta);
        }
        let _published = self.history.push(delta);
        assert(_published is Ok);
        let _charged = self.sum.try_allocate(delta);
        assert(_charged);
        assert(self@ == if before.len() >= window { before.drop_first().push(delta) }
            else { before.push(delta) });
        assert(self.coupled(window, _max_delta));
        let total = self.sum.used_exec();
        let denominator = self.history.len() as u64;
        assert(denominator > 0);
        total / denominator
    }
}

/// A phase-aware convergence governor.
pub struct ConvergenceGovernorPhaseAware<H: GovernorHistory = Vec<u64>> {
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
    pub delta_history: H,
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
    #[expect(clippy::arithmetic_side_effects, reason = "the required threshold <= u64::MAX / 2 bound makes each threshold doubling representable")]
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

}

impl<H: GovernorHistory> ConvergenceGovernorPhaseAware<H> {
    // ── Specifications ──────────────────────────────────────────────────

    /// TLA+ `TypeInvariant`'s window clause (+ the overflow / nonempty-window
    /// bounds; the enum and bool clauses are carried by the types).
    pub open spec fn type_invariant(&self) -> bool {
        self.delta_history@.len() <= self.window
            && self.threshold <= u64::MAX / 2
            && self.window >= 1
            && self.window as int * self.max_delta as int <= u64::MAX as int
            && self.delta_history.coupled(self.window, self.max_delta)
            && forall|i: int| 0 <= i < self.delta_history@.len() ==>
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

}

impl ConvergenceGovernorPhaseAware {
    /// The oldest retained delta contributes exactly once to the mathematical sum.
    proof fn lemma_sum_drop(s: Seq<u64>)
        requires s.len() > 0,
        ensures Self::sum_seq(s) == s[0] as int + Self::sum_seq(s.drop_first()),
        decreases s.len(),
    {
        let prefix = s.take(s.len() - 1);
        let tail = s.drop_first();
        reveal_with_fuel(ConvergenceGovernorPhaseAware::sum_seq, 2);
        if s.len() == 1 {
            assert(prefix =~= Seq::<u64>::empty());
            assert(tail =~= Seq::<u64>::empty());
            assert(s[s.len() - 1] == s[0]);
        } else {
            assert(prefix.len() == s.len() - 1);
            assert(prefix[0] == s[0]);
            Self::lemma_sum_drop(prefix);
            assert(tail.len() == s.len() - 1);
            assert(prefix.drop_first() =~= tail.take(tail.len() - 1));
            assert(tail[tail.len() - 1] == s[s.len() - 1]);
            assert(Self::sum_seq(s) == Self::sum_seq(prefix) + s[s.len() - 1] as int);
            assert(Self::sum_seq(tail) == Self::sum_seq(tail.take(tail.len() - 1))
                + tail[tail.len() - 1] as int);
        }
    }
    proof fn lemma_sum_bound(s: Seq<u64>, maximum: u64)
        requires forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= maximum,
        ensures 0 <= Self::sum_seq(s) <= s.len() * maximum as int,
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::lemma_sum_bound(s.take(s.len() - 1), maximum);
            assert(Self::sum_seq(s.take(s.len() - 1)) + s[s.len() - 1] as int
                <= s.len() * maximum as int) by (nonlinear_arith)
                requires Self::sum_seq(s.take(s.len() - 1)) <= (s.len() - 1) * maximum as int,
                    s[s.len() - 1] <= maximum;
        }
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

}

impl<H: GovernorHistory> ConvergenceGovernorPhaseAware<H> {
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
        ConvergenceGovernorPhaseAware::sum_seq(self.slide_window(delta)) / self.slide_window(delta).len() as int
    }

}

impl ConvergenceGovernorPhaseAware {
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
        Self::initialize(threshold, awaken_threshold, window, max_delta, Vec::new())
    }

    /// Admit the complete sliding-window storage before the first update.
    ///
    /// # Errors
    /// Returns the allocation error without exposing a governor.
    pub fn try_new(threshold: u64, awaken_threshold: u64, window: usize, max_delta: u64)
        -> (result: Result<Self, std::collections::TryReserveError>)
        requires threshold <= u64::MAX / 2, window >= 1,
            window as int * max_delta as int <= u64::MAX as int,
        ensures result is Ok ==> {
            let g = result.unwrap();
            &&& g.inv() && g.threshold == threshold && g.awaken_threshold == awaken_threshold
            &&& g.window == window && g.max_delta == max_delta
            &&& g.state == GovState::Active && g.gradient_phase == Phase::Cold
            &&& !g.peak_observed && g.delta_history@.len() == 0
        },
    {
        let mut history = Vec::new(); history.try_reserve(window)?;
        Ok(Self::initialize(threshold, awaken_threshold, window, max_delta, history))
    }

    fn initialize(threshold: u64, awaken_threshold: u64, window: usize, max_delta: u64, delta_history: Vec<u64>)
        -> (g: ConvergenceGovernorPhaseAware)
        requires
            delta_history@.len() == 0,
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
            state: GovState::Active, gradient_phase: Phase::Cold, delta_history,
            peak_observed: false,
        }
    }

    /// Construct the same empty Init with canonical FIFO and sum owners.
    pub(crate) fn new_buffered(threshold: u64, awaken_threshold: u64, window: usize, max_delta: u64)
        -> (g: ConvergenceGovernorPhaseAware<BufferedGovernorHistory>)
        requires threshold <= u64::MAX / 2, window >= 1,
            window as int * max_delta as int <= u64::MAX,
        ensures g.threshold == threshold, g.awaken_threshold == awaken_threshold,
            g.window == window, g.max_delta == max_delta,
            g.state == GovState::Active, g.gradient_phase == Phase::Cold,
            g.delta_history@ == Seq::<u64>::empty(), !g.peak_observed, g.inv(),
    {
        let delta_history = BufferedGovernorHistory::new(window, max_delta);
        ConvergenceGovernorPhaseAware { threshold, awaken_threshold, window, max_delta,
            state: GovState::Active, gradient_phase: Phase::Cold, delta_history, peak_observed: false }
    }
}

impl<H: GovernorHistory> ConvergenceGovernorPhaseAware<H> {
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
                == ConvergenceGovernorPhaseAware::classify_phase_spec(delta, old(self).peak_observed, old(self).threshold),
            final(self).peak_observed == (old(self).peak_observed || delta >= old(self).threshold),
            final(self).state == ConvergenceGovernorPhaseAware::next_state_spec(
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
        let new_phase = ConvergenceGovernorPhaseAware::classify_phase(delta, old_peak, self.threshold);
        let new_peak = old_peak || (delta >= self.threshold);
        let avg = self.delta_history.step(delta, self.window, self.max_delta);
        assert(self.delta_history@ =~= old(self).slide_window(delta));
        let new_state = ConvergenceGovernorPhaseAware::next_state(
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

}

impl ConvergenceGovernorPhaseAware {
    #[expect(clippy::indexing_slicing, reason = "the history loop guards each index against the immutable retained window length")]
    #[expect(clippy::arithmetic_side_effects, reason = "the history-length times max-delta precondition bounds every partial sum, and the loop bounds each cursor successor")]
    #[expect(clippy::integer_division, reason = "the nonempty-window precondition supplies a positive denominator and the contract specifies the floor integer average")]
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
