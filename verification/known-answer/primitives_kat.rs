// Catalog primitive and composition known-answer cross-check. The 19 catalog
// entries plus the specified composition witnesses are exercised on selected
// inputs whose outputs are computable by inspection. The
// Verus-verified functions are called from this binary linked against the
// Verus-compiled library; any mismatch between the computed answer and the
// expected answer surfaces as a FAIL. This is executable correspondence
// evidence, not proof or exhaustive input coverage.
extern crate automation_structures;
mod actuation_pass_vectors;
use automation_structures::compositions::rate_limit::RateLimit;
use automation_structures::compositions::select_then_actuate::SelectThenActuate;
use automation_structures::compositions::signal::Signal;
use automation_structures::compositions::traversal_budget_composition::TraversalBudgetComposition;
use automation_structures::compositions::allocation_snapshot::{capture, AllocationSnapshot};
use automation_structures::primitives::audit_sink::AuditSink;
use automation_structures::primitives::backtracking_traversal::BacktrackingTraversal;
use automation_structures::compositions::bisection::{bisection_find, Bisection};
use automation_structures::primitives::budget::Budget;
use automation_structures::primitives::competitive_selection::{
    CompetitiveSelectionHard, CompetitiveSelectionHardExclusive, CompetitiveSelectionRanked,
    CompetitiveSelectionSoft,
};
use automation_structures::primitives::convergence_governor_phase_aware::{
    ConvergenceGovernorPhaseAware, GovState, Phase,
};
use automation_structures::compositions::equivalence_class::EquivalenceClass;
use automation_structures::compositions::federated_budget::FederatedBudget;
use automation_structures::primitives::propagation_pass::{PropagationPass, Round};
use automation_structures::primitives::quality_hierarchy::QualityHierarchy;
use automation_structures::compositions::reduction::{reduce_max, reduce_sum, Reducer};
use automation_structures::compositions::relationship_graph::RelationshipGraph;
use automation_structures::primitives::resource_registry::ResourceRegistry;
use automation_structures::compositions::sampler::Sampler;
use automation_structures::compositions::traversal_engine::TraversalEngine;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

// ── distributional: the empirical statistical layer ────────────────────────────────
//
// Every other check in this binary is a known-answer cross-check of a verified
// function. This section is an empirical statistical test, because the Sampler
// entry's distributional property is not expressible in the TLA+ model;
// Sampler.tla's header names chi-squared as the route.
//
// Two generators are run: `draw_weighted` and `draw_uniform`. Both are
// Verus-verified against the same specification -- each re-establishes exactly
// BoundedSample and SupportConsistency and nothing else -- and they produce
// different frequency profiles, so the specification does not pin the
// distribution and the draw rule is domain-supplied content.
//
// The generator is a linear congruential generator with the Numerical Recipes
// constants, which Sampler.tla's header names as the reference generator. An
// LCG is not a cryptographic PRNG and its low-order bits have short periods, so
// the high bits are used for both proposals.

struct Lcg(u32);

impl Lcg {
    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(1664525).wrapping_add(1013904223);
        self.0
    }
    /// A value in `0..m`, taken from the high bits.
    fn below(&mut self, m: u32) -> u32 {
        (self.next_u32() >> 16) % m
    }
}

/// Pearson chi-squared of `obs` against expected counts proportional to
/// `weights`, conditioned on the total number of observations.
fn chi_squared(obs: &[u64], weights: &[u64]) -> f64 {
    let total_obs: u64 = obs.iter().sum();
    let total_w: u64 = weights.iter().sum();
    let mut x2 = 0.0f64;
    for k in 0..obs.len() {
        let expected = total_obs as f64 * weights[k] as f64 / total_w as f64;
        let d = obs[k] as f64 - expected;
        x2 += d * d / expected;
    }
    x2
}

/// Run `trials` single draws, each from a fresh Sampler, and return the
/// per-item accepted counts. `weighted` selects the draw rule.
fn draw_frequencies(
    weights: &[u64],
    max_prob: u64,
    trials: u32,
    weighted: bool,
    seed: u32,
) -> Vec<u64> {
    let n = weights.len();
    let mut counts = vec![0u64; n];
    let mut rng = Lcg(seed);
    for _ in 0..trials {
        let mut s = Sampler::new(weights.to_vec(), 1);
        let i = rng.below(n as u32) as usize;
        let r = rng.below(max_prob as u32) as u64;
        let accepted = if weighted {
            s.draw_weighted(i, r)
        } else {
            s.draw_uniform(i)
        };
        if accepted {
            counts[i] += 1;
        }
    }
    counts
}

fn main() {
    println!("Catalog primitive and composition KAT cross-check");
    let mut all_ok = true;

    // Reduction Reduction: additive fold over bounded u64.
    all_ok &= check("Reduction reduce_sum(empty)", reduce_sum(&[]), 0);
    all_ok &= check(
        "Reduction reduce_sum([1,2,3,4,5])",
        reduce_sum(&[1, 2, 3, 4, 5]),
        15,
    );
    all_ok &= check(
        "Reduction reduce_sum(10x 1e9)",
        reduce_sum(&[1_000_000_000u64; 10]),
        10_000_000_000u64,
    );
    all_ok &= check("Reduction reduce_sum([42])", reduce_sum(&[42]), 42);

    // Reduction (second operator): max fold, discriminating vectors. Each vector
    // rules out a specific plausible-wrong construction rather than only
    // confirming that the correct construction gives the correct answer.
    all_ok &= check("Reduction reduce_max(empty)", reduce_max(&[]), 0);
    all_ok &= check("Reduction reduce_max([5])", reduce_max(&[5]), 5);
    // Max at the FIRST position: rules out a construction that initializes
    // result to the identity and starts scanning from index 1 (skipping
    // items[0] entirely) -- that bug would see only {2,3,1} and return 3.
    all_ok &= check(
        "Reduction reduce_max([100,2,3,1]) (max at front)",
        reduce_max(&[100, 2, 3, 1]),
        100,
    );
    // Max at the LAST position: rules out an off-by-one loop that stops one
    // short (e.g. iterates 0..n-1) -- that bug would see only {1,2,3} and
    // return 3.
    all_ok &= check(
        "Reduction reduce_max([1,2,3,100]) (max at back)",
        reduce_max(&[1, 2, 3, 100]),
        100,
    );
    // Same input to both operators: rules out an operator-confusion /
    // copy-paste construction that internally still sums when max was
    // requested (or vice versa) -- sum and max disagree here (15 vs 5), so a
    // swapped implementation fails one side visibly.
    all_ok &= check(
        "Reduction reduce_max([1,2,3,4,5]) (vs. reduce_sum, same input)",
        reduce_max(&[1, 2, 3, 4, 5]),
        5,
    );
    all_ok &= check(
        "Reduction reduce_sum([1,2,3,4,5]) (vs. reduce_max, same input)",
        reduce_sum(&[1, 2, 3, 4, 5]),
        15,
    );

    // Reduction (machine): the TLA+ Reduction machine (Reducer) -- Partition +
    // Aggregate maintained step by step by process() (TLA+ Process). Each step
    // moves one value from remaining to processed and folds it into result.
    let mut red = Reducer::new(vec![10u64, 20, 30]);
    all_ok &= check("Reduction Reducer new: result 0", red.result, 0);
    all_ok &= check(
        "Reduction Reducer new: remaining len 3",
        red.remaining.len(),
        3,
    );
    all_ok &= check(
        "Reduction Reducer new: processed empty",
        red.processed.len(),
        0,
    );
    red.process(); // fold 10
    all_ok &= check("Reduction Reducer step 1: result 10", red.result, 10);
    all_ok &= check(
        "Reduction Reducer step 1: processed len 1",
        red.processed.len(),
        1,
    );
    all_ok &= check(
        "Reduction Reducer step 1: remaining len 2 (partition: 1+2==3)",
        red.remaining.len(),
        2,
    );
    red.process(); // fold 20
    all_ok &= check("Reduction Reducer step 2: result 30", red.result, 30);
    red.process(); // fold 30
    all_ok &= check(
        "Reduction Reducer drained: result 60 (aggregate == fold)",
        red.result,
        60,
    );
    all_ok &= check("Reduction Reducer drained: done", red.done(), true);
    all_ok &= check(
        "Reduction Reducer drained: processed len 3 (partition: 3+0==3)",
        red.processed.len(),
        3,
    );

    // ResourceRegistry ResourceRegistry: unique key->value mapping (TLA+ Register/Deregister).
    let mut reg: ResourceRegistry = ResourceRegistry::new();
    all_ok &= check(
        "ResourceRegistry new registry: lookup(3) absent",
        reg.lookup(3),
        None,
    );
    reg.register(3, 0xdeadbeefu64);
    all_ok &= check(
        "ResourceRegistry after register(3,..): lookup(3)",
        reg.lookup(3),
        Some(0xdeadbeefu64),
    );
    reg.register(5, 100u64);
    all_ok &= check(
        "ResourceRegistry after register(5,100): lookup(5)",
        reg.lookup(5),
        Some(100u64),
    );
    all_ok &= check(
        "ResourceRegistry register frame: lookup(3) unaffected",
        reg.lookup(3),
        Some(0xdeadbeefu64),
    );
    reg.register(3, 7u64); // upsert: key 3 keeps a single value (UniqueMapping)
    all_ok &= check(
        "ResourceRegistry upsert register(3,7): lookup(3) now 7",
        reg.lookup(3),
        Some(7u64),
    );
    reg.deregister(3);
    all_ok &= check(
        "ResourceRegistry after deregister(3): lookup(3) absent",
        reg.lookup(3),
        None,
    );
    all_ok &= check(
        "ResourceRegistry deregister frame: lookup(5) still present",
        reg.lookup(5),
        Some(100u64),
    );

    // TraversalEngine TraversalEngine: budgeted star walk (TLA+ VisitNode). num_nodes=4,
    // root=0, budget=6. Visit root (NodeCost 2 <= 6): accept, budget 4, enqueue
    // the star children {1,2,3}. Visit child 1 (cost 2 <= 4): accept, budget 2.
    let mut te = TraversalEngine::new(4, 0, 6);
    all_ok &= check(
        "TraversalEngine TraversalEngine new: budget 6",
        te.budget_remaining,
        6,
    );
    all_ok &= check(
        "TraversalEngine TraversalEngine new: queue = {root}",
        te.queue[0],
        0,
    );
    te.visit_node(0); // visit root: accept, spend NodeCost 2, enqueue {1,2,3}
    all_ok &= check(
        "TraversalEngine after visit root: budget 4",
        te.budget_remaining,
        4,
    );
    all_ok &= check(
        "TraversalEngine after visit root: root accepted",
        te.accepted[0],
        0,
    );
    all_ok &= check(
        "TraversalEngine after visit root: visited len 1",
        te.visited.len(),
        1,
    );
    te.visit_node(1); // visit enqueued child: accept (cost 2 <= 4)
    all_ok &= check(
        "TraversalEngine after visit child: accepted len 2 (accepted subset visited)",
        te.accepted.len(),
        2,
    );
    // Exhaust the budget (discriminating vector): the three checks
    // above never leave accepted a PROPER subset of visited -- every node
    // visited so far was also affordable, so a wrong-but-plausible
    // construction that always accepts whatever it visits (collapsing
    // accepted == visited, ignoring the budget guard on acceptance entirely)
    // would pass unchanged. Visiting two more nodes exercises the skip
    // branch: node 2 is still affordable (cost 2 <= budget 2), draining the
    // budget to exactly 0; node 3 is then visited but NOT accepted (cost
    // 2 > budget 0) -- the one place this invariant's content is exercised.
    te.visit_node(2); // visit enqueued child: accept (cost 2 <= 2), budget -> 0
    all_ok &= check(
        "TraversalEngine after visit node 2: budget 0",
        te.budget_remaining,
        0,
    );
    all_ok &= check(
        "TraversalEngine after visit node 2: accepted len 3",
        te.accepted.len(),
        3,
    );
    te.visit_node(3); // visit last enqueued child: budget exhausted (2 > 0) -- SKIP
    all_ok &= check(
        "TraversalEngine after visit node 3 (budget exhausted): visited len 4",
        te.visited.len(),
        4,
    );
    all_ok &= check(
        "TraversalEngine after visit node 3 (budget exhausted): accepted len STILL 3 (visited but not accepted)",
        te.accepted.len(),
        3,
    );

    all_ok &= actuation_pass_vectors::run();

    // Bisection Bisection: halving search on sorted slice.
    let sorted: [u64; 7] = [1, 3, 5, 7, 9, 11, 13];
    all_ok &= check(
        "Bisection bisection_find(sorted, 1)",
        bisection_find(&sorted, 1),
        0,
    );
    all_ok &= check(
        "Bisection bisection_find(sorted, 7)",
        bisection_find(&sorted, 7),
        3,
    );
    all_ok &= check(
        "Bisection bisection_find(sorted, 13)",
        bisection_find(&sorted, 13),
        6,
    );
    // Not present: returns sorted.len() (i.e., 7).
    all_ok &= check(
        "Bisection bisection_find(sorted, 4) absent",
        bisection_find(&sorted, 4),
        7,
    );
    all_ok &= check(
        "Bisection bisection_find(sorted, 100) absent",
        bisection_find(&sorted, 100),
        7,
    );
    // Empty slice: returns 0 (= len).
    all_ok &= check(
        "Bisection bisection_find([], 5) empty",
        bisection_find(&[], 5),
        0,
    );

    // Bisection (machine): the TLA+ Bisection constants and lo/hi/probes machine.
    // Domain [0,16], threshold 5, and MaxProbes 4 satisfy
    // DomainSize <= Pow2[MaxProbes].
    let mut bx = Bisection::new(0, 16, 5, 16, 4);
    all_ok &= check("Bisection Bisection new: lo 0", bx.lo, 0);
    all_ok &= check("Bisection Bisection new: hi 16", bx.hi, 16);
    all_ok &= check("Bisection Bisection new: max probes 4", bx.max_probes, 4);
    all_ok &= check("Bisection Bisection new: probes 0", bx.probes_taken, 0);
    all_ok &= check(
        "Bisection Bisection new: threshold bracketed",
        bx.lo <= bx.threshold && bx.threshold <= bx.hi,
        true,
    );
    bx.probe(); // mid = 8 >= 5 -> hi' = 8 (width 16 halved to 8)
    all_ok &= check("Bisection Bisection probe 1: hi 8 (halved)", bx.hi, 8);
    all_ok &= check("Bisection Bisection probe 1: probes 1", bx.probes_taken, 1);
    all_ok &= check(
        "Bisection Bisection probe 1: threshold still bracketed",
        bx.lo <= bx.threshold && bx.threshold <= bx.hi,
        true,
    );
    bx.probe(); // mid = 4 < 5 -> lo' = 5 (interval 0..8 -> 5..8)
    all_ok &= check("Bisection Bisection probe 2: lo 5", bx.lo, 5);
    all_ok &= check("Bisection Bisection probe 2: hi 8 (width 3)", bx.hi, 8);
    all_ok &= check("Bisection Bisection probe 2: probes 2", bx.probes_taken, 2);
    let mut by = Bisection::new(0, 16, 5, 16, 4);
    by.bisect(); // (0,16) -> (0,8) -> (5,8) -> (5,6): converged
    all_ok &= check(
        "Bisection Bisection bisect: converged (hi-lo<2)",
        by.hi - by.lo < 2,
        true,
    );
    all_ok &= check(
        "Bisection Bisection bisect: threshold pinned in [lo,hi]",
        by.lo <= by.threshold && by.threshold <= by.hi,
        true,
    );
    all_ok &= check(
        "Bisection Bisection bisect: within MaxProbes",
        by.probes_taken <= by.max_probes,
        true,
    );
    // Exact edge: threshold 1 over a 32-wide domain consumes all five allowed
    // probes, so the ProbeBound boundary is observable.
    let mut bz = Bisection::new(0, 32, 1, 32, 5);
    bz.bisect();
    all_ok &= check(
        "Bisection Bisection exact budget: converged",
        bz.hi - bz.lo < 2,
        true,
    );
    all_ok &= check(
        "Bisection Bisection exact budget: probes == MaxProbes",
        bz.probes_taken,
        bz.max_probes,
    );

    // Sampler Sampler: bounded support-preserving selection (TLA+ BoundedSample +
    // SupportConsistency). distribution over 4 items (item 1 has zero
    // probability), sample_size 2.
    let mut smp = Sampler::new(vec![3u64, 0, 5, 2], 2);
    all_ok &= check("Sampler Sampler new: num_items", smp.num_items, 4);
    all_ok &= check("Sampler Sampler new: selected empty", smp.selected.len(), 0);
    smp.sample(0); // distribution[0] = 3 > 0 (in support)
    all_ok &= check("Sampler sample(0): selected len 1", smp.selected.len(), 1);
    all_ok &= check("Sampler sample(0): selected[0] == 0", smp.selected[0], 0);
    smp.sample(2); // distribution[2] = 5 > 0
    all_ok &= check(
        "Sampler sample(2): selected len 2 (BoundedSample == SampleSize)",
        smp.selected.len(),
        2,
    );
    all_ok &= check(
        "Sampler sample(2): selected[1] == 2 (support > 0)",
        smp.selected[1],
        2,
    );
    all_ok &= check(
        "Sampler Sampler: item 1 (zero prob) never selected",
        smp.contains_exec(1),
        false,
    );

    // ── distributional EMPIRICAL: the distributional property lives in the DRAW RULE ──
    //
    // Weights (1,2,3,4) over four items; a single draw per trial from a fresh
    // Sampler, so each trial is an independent draw from the same
    // distribution. df = 3; the 0.1% critical value of chi-squared(3) is
    // 16.266, which is the threshold used below.
    //
    // Three measurements, and it is the CONTRAST that is the result:
    //   1. the weighted rule against the weighted expectation  -> must FIT
    //   2. the uniform rule against the UNIFORM expectation    -> must FIT
    //      (so a rejection in 3 cannot be blamed on a broken generator)
    //   3. the uniform rule against the weighted expectation   -> must NOT fit
    // Both rules satisfy the SAME Verus-verified specification.
    println!("  --- distributional EMPIRICAL (statistical, not a verified property) ---");
    let w_dist: Vec<u64> = vec![1, 2, 3, 4];
    let w_unif: Vec<u64> = vec![1, 1, 1, 1];
    let trials: u32 = 200_000;
    let crit_3df_001 = 16.266f64;

    let f_weighted = draw_frequencies(&w_dist, 4, trials, true, 12345);
    let f_uniform = draw_frequencies(&w_dist, 4, trials, false, 12345);

    let x2_w_vs_w = chi_squared(&f_weighted, &w_dist);
    let x2_u_vs_u = chi_squared(&f_uniform, &w_unif);
    let x2_u_vs_w = chi_squared(&f_uniform, &w_dist);

    println!(
        "  distributional weighted-draw counts {:?}  chi2 vs weighted = {:.2}",
        f_weighted, x2_w_vs_w
    );
    println!(
        "  distributional uniform-draw  counts {:?}  chi2 vs uniform  = {:.2}",
        f_uniform, x2_u_vs_u
    );
    println!(
        "  distributional uniform-draw  counts {:?}  chi2 vs weighted = {:.2}",
        f_uniform, x2_u_vs_w
    );

    all_ok &= check(
        "distributional weighted draw FITS the weighted expectation (chi2 < 16.266, df=3)",
        x2_w_vs_w < crit_3df_001,
        true,
    );
    all_ok &= check(
        "distributional uniform draw FITS the uniform expectation (generator is sound)",
        x2_u_vs_u < crit_3df_001,
        true,
    );
    all_ok &= check(
        "distributional uniform draw REJECTED against the weighted expectation (the discriminator)",
        x2_u_vs_w > crit_3df_001,
        true,
    );

    // AllocationSnapshot: immutable allocation record built by the guarded
    // AcceptNode action. capture(cap=10, num_nodes=5, nodes=[0..5],
    // costs=[3,4,5,1,2]): accept 0(3),1(4); skip 2 (cost 5 > rem 3); accept
    // 3(1),4(2) -> total=10, rem=0, |accepted|=4.
    let a1 = capture(10, 5, &[0u64, 1, 2, 3, 4], &[3u64, 4, 5, 1, 2]);
    all_ok &= check("AllocSnap capture(10,..).total_cost", a1.total_cost, 10);
    all_ok &= check(
        "AllocSnap capture(10,..).budget_remaining",
        a1.budget_remaining,
        0,
    );
    all_ok &= check(
        "AllocSnap capture(10,..).accepted.len()",
        a1.accepted.len(),
        4,
    );
    all_ok &= check(
        "AllocSnap capture(10,..) BudgetConsistency",
        a1.total_cost + a1.budget_remaining,
        10,
    );

    // Duplicate and out-of-range node ids are skipped (the set + Nodes guards).
    // capture(cap=20, num_nodes=3, nodes=[0,0,1,5,2], costs=[5,5,5,5,5]):
    //   accept 0; skip 0 (dup); accept 1; skip 5 (>= num_nodes); accept 2
    //   -> total=15, rem=5, |accepted|=3.
    let a2 = capture(20, 3, &[0u64, 0, 1, 5, 2], &[5u64, 5, 5, 5, 5]);
    all_ok &= check("AllocSnap capture(dup/oob).total_cost", a2.total_cost, 15);
    all_ok &= check(
        "AllocSnap capture(dup/oob).budget_remaining",
        a2.budget_remaining,
        5,
    );
    all_ok &= check(
        "AllocSnap capture(dup/oob).accepted.len()",
        a2.accepted.len(),
        3,
    );

    // Budget exhaustion mid-stream. capture(cap=5, num_nodes=10,
    // nodes=[0,1,2], costs=[10,2,2]): skip 0 (10 > 5); accept 1(2),2(2)
    //   -> total=4, rem=1, |accepted|=2.
    let a3 = capture(5, 10, &[0u64, 1, 2], &[10u64, 2, 2]);
    all_ok &= check("AllocSnap capture(exhaust).total_cost", a3.total_cost, 4);
    all_ok &= check(
        "AllocSnap capture(exhaust).budget_remaining",
        a3.budget_remaining,
        1,
    );
    all_ok &= check(
        "AllocSnap capture(exhaust).accepted.len()",
        a3.accepted.len(),
        2,
    );

    // Init (new) then direct AcceptNode steps: new(100,3); accept 0(30), 2(50)
    //   -> total=80, rem=20, |accepted|=2.
    let mut a4 = AllocationSnapshot::new(100, 3);
    all_ok &= check("AllocSnap new(100,3).total_cost", a4.total_cost, 0);
    all_ok &= check(
        "AllocSnap new(100,3).budget_remaining",
        a4.budget_remaining,
        100,
    );
    a4.accept_node(0, 30);
    a4.accept_node(2, 50);
    all_ok &= check(
        "AllocSnap after accept 30,50: total_cost",
        a4.total_cost,
        80,
    );
    all_ok &= check(
        "AllocSnap after accept 30,50: budget_remaining",
        a4.budget_remaining,
        20,
    );
    all_ok &= check(
        "AllocSnap after accept 30,50: accepted.len()",
        a4.accepted.len(),
        2,
    );

    // Budget: full 4-field capacity ceiling traced through all six actions.
    // used == allocated + reserved + pending_eviction must stay <= capacity.
    let mut b = Budget::new(100);
    all_ok &= check("Budget new(100): allocated", b.allocated, 0);
    all_ok &= check("Budget new(100): available", b.available(), 100);
    let ok1 = b.try_allocate(30); // used 0 -> 30
    all_ok &= check("Budget try_allocate(30) accepted", ok1, true);
    all_ok &= check("Budget after alloc 30: allocated", b.allocated, 30);
    let okr = b.reserve(40); // used 30 -> 70
    all_ok &= check("Budget reserve(40) accepted", okr, true);
    all_ok &= check("Budget after reserve 40: reserved", b.reserved, 40);
    let ok2 = b.try_allocate(40); // used 70 + 40 = 110 > 100 -> reject
    all_ok &= check(
        "Budget try_allocate(40) rejected (over ceiling)",
        ok2,
        false,
    );
    all_ok &= check(
        "Budget after rejected alloc: allocated unchanged",
        b.allocated,
        30,
    );
    let ok3 = b.try_allocate(30); // used 70 + 30 = 100 -> accept, at ceiling
    all_ok &= check("Budget try_allocate(30) accepted (hits ceiling)", ok3, true);
    all_ok &= check("Budget at ceiling: available", b.available(), 0);
    let ok4 = b.try_allocate(1); // at ceiling -> reject
    all_ok &= check("Budget try_allocate(1) at ceiling rejected", ok4, false);
    b.commit_reservation(40); // allocated 60 -> 100, reserved 40 -> 0
    all_ok &= check(
        "Budget after commit_reservation(40): allocated",
        b.allocated,
        100,
    );
    all_ok &= check(
        "Budget after commit_reservation(40): reserved",
        b.reserved,
        0,
    );
    b.release(50); // allocated 100 -> 50
    all_ok &= check("Budget after release(50): allocated", b.allocated, 50);
    b.mark_eviction(30); // allocated 50 -> 20, pending 0 -> 30
    all_ok &= check("Budget after mark_eviction(30): allocated", b.allocated, 20);
    all_ok &= check(
        "Budget after mark_eviction(30): pending_eviction",
        b.pending_eviction,
        30,
    );
    b.complete_eviction(10); // pending 30 -> 20
    all_ok &= check(
        "Budget after complete_eviction(10): pending_eviction",
        b.pending_eviction,
        20,
    );
    // used == 20 + 0 + 20 == 40, so available == 60.
    all_ok &= check("Budget final available (used 40 of 100)", b.available(), 60);

    // QualityHierarchy: refinement forest. Build a small tree over 4 nodes:
    //   levels 0->3, 1->2, 2->2, 3->1 ; costs 0->1, 1->2, 2->3, 3->4 ;
    //   edges 0->1, 0->2 (node 0 has two children), 1->3. NULL sentinel == 4.
    let mut h = QualityHierarchy::new(4, 5);
    all_ok &= check("QHier new(4,5): edges empty", h.edges.len(), 0);
    all_ok &= check(
        "QHier new(4,5): parent[0] == NULL (num_nodes)",
        h.parent[0],
        4,
    );
    all_ok &= check("QHier new(4,5): level[0] == 0", h.level[0], 0);
    h.set_node_properties(0, 3, 1);
    h.set_node_properties(1, 2, 2);
    h.set_node_properties(2, 2, 3);
    h.set_node_properties(3, 1, 4);
    all_ok &= check("QHier set_node_properties: level[0]", h.level[0], 3);
    all_ok &= check("QHier set_node_properties: cost[3]", h.cost[3], 4);
    h.add_child(0, 1);
    h.add_child(0, 2);
    h.add_child(1, 3);
    all_ok &= check("QHier edges.len() after 3 add_child", h.edges.len(), 3);
    all_ok &= check("QHier parent[1] == 0", h.parent[1], 0);
    all_ok &= check("QHier parent[2] == 0", h.parent[2], 0);
    all_ok &= check("QHier parent[3] == 1", h.parent[3], 1);
    all_ok &= check("QHier parent[0] still NULL", h.parent[0], 4);
    all_ok &= check("QHier has_children(0) (two kids)", h.has_children(0), true);
    all_ok &= check("QHier has_children(1) (one kid)", h.has_children(1), true);
    all_ok &= check("QHier has_children(2) (leaf)", h.has_children(2), false);
    all_ok &= check("QHier has_children(3) (leaf)", h.has_children(3), false);
    // StrictLevelDescent spot-check: each edge has parent level > child level.
    all_ok &= check(
        "QHier edge 0->1 level 3>2",
        h.level[h.edges[0].0] > h.level[h.edges[0].1],
        true,
    );
    all_ok &= check(
        "QHier edge 1->3 levels (2,1)",
        (h.level[1], h.level[3]),
        (2, 1),
    );

    // AuditSink: append-only hash-chained log. Hash(prev,op) = (prev*3 + op + 1)
    // % 100. Chain from last_hash 0 under ops 1,2,3,1 is 0 -> 2 -> 9 -> 31 -> 95.
    // Each record's prev_hash must equal the previous record's hash (ChainIntegrity).
    let mut s = AuditSink::new(4);
    all_ok &= check("AuditSink new(4): last_hash", s.last_hash, 0);
    all_ok &= check("AuditSink new(4): log empty", s.log.len(), 0);
    let r1 = s.record(1); // Hash(0,1) = 2
    all_ok &= check("AuditSink record(1) ok", r1, true);
    all_ok &= check("AuditSink after rec1: last_hash", s.last_hash, 2);
    all_ok &= check(
        "AuditSink after rec1: log[0].prev_hash",
        s.log[0].prev_hash,
        0,
    );
    all_ok &= check("AuditSink after rec1: log[0].hash", s.log[0].hash, 2);
    all_ok &= check(
        "AuditSink after rec1: log[0].operation",
        s.log[0].operation,
        1,
    );
    s.record(2); // Hash(2,2) = 9
    all_ok &= check("AuditSink after rec2: last_hash", s.last_hash, 9);
    all_ok &= check(
        "AuditSink after rec2: log[1].prev_hash chains to log[0].hash",
        s.log[1].prev_hash,
        2,
    );
    all_ok &= check("AuditSink after rec2: log[1].hash", s.log[1].hash, 9);
    s.record(3); // Hash(9,3) = 31
    all_ok &= check("AuditSink after rec3: last_hash", s.last_hash, 31);
    all_ok &= check(
        "AuditSink after rec3: log[2].prev_hash",
        s.log[2].prev_hash,
        9,
    );
    s.record(1); // Hash(31,1) = 95, log now full (len 4)
    all_ok &= check("AuditSink after rec4: last_hash", s.last_hash, 95);
    all_ok &= check(
        "AuditSink after rec4: log[3].prev_hash",
        s.log[3].prev_hash,
        31,
    );
    all_ok &= check("AuditSink after rec4: log.len()", s.log.len(), 4);
    let r5 = s.record(2); // log full -> rejected
    all_ok &= check("AuditSink record at MaxLogLen rejected", r5, false);
    all_ok &= check(
        "AuditSink after rejected: log.len() unchanged",
        s.log.len(),
        4,
    );
    all_ok &= check(
        "AuditSink after rejected: last_hash unchanged",
        s.last_hash,
        95,
    );
    // ChainIntegrity spot-check: each prev_hash equals the previous hash.
    all_ok &= check(
        "AuditSink chain log[1].prev==log[0].hash",
        s.log[1].prev_hash == s.log[0].hash,
        true,
    );
    all_ok &= check(
        "AuditSink chain log[3].prev==log[2].hash",
        s.log[3].prev_hash == s.log[2].hash,
        true,
    );
    // HashBindsContent: the hash depends on op — from last_hash 0, op=1 -> 2 but
    // op=2 -> 3, so the same chain position with different content gets a different hash.
    let mut s_a = AuditSink::new(1);
    s_a.record(1);
    let mut s_b = AuditSink::new(1);
    s_b.record(2);
    all_ok &= check(
        "AuditSink HashBindsContent: op=1 from 0 -> hash 2",
        s_a.last_hash,
        2,
    );
    all_ok &= check(
        "AuditSink HashBindsContent: op=2 from 0 -> hash 3 (binds op)",
        s_b.last_hash,
        3,
    );

    // FederatedBudget: master pool (cap 6) federated into 2 sub-pools.
    // CapacityConservation: master_allocated == sub_capacities[0] + sub_capacities[1].
    let mut fb = FederatedBudget::new(6, 2);
    all_ok &= check(
        "FedBudget new(6,2): master_allocated",
        fb.master_allocated,
        0,
    );
    all_ok &= check(
        "FedBudget new(6,2): sub_capacities[0]",
        fb.sub_capacities[0],
        0,
    );
    let f1 = fb.allocate_sub_pool(0, 4); // master 0+4 <= 6
    all_ok &= check("FedBudget allocate_sub_pool(0,4) accepted", f1, true);
    all_ok &= check(
        "FedBudget after alloc(0,4): master_allocated",
        fb.master_allocated,
        4,
    );
    all_ok &= check(
        "FedBudget after alloc(0,4): sub_capacities[0]",
        fb.sub_capacities[0],
        4,
    );
    let f2 = fb.allocate_sub_pool(1, 3); // master 4+3 = 7 > 6 -> reject
    all_ok &= check(
        "FedBudget allocate_sub_pool(1,3) rejected (over master)",
        f2,
        false,
    );
    all_ok &= check(
        "FedBudget after reject: master_allocated unchanged",
        fb.master_allocated,
        4,
    );
    let f3 = fb.allocate_sub_pool(1, 2); // master 4+2 = 6 <= 6
    all_ok &= check("FedBudget allocate_sub_pool(1,2) accepted", f3, true);
    all_ok &= check(
        "FedBudget after alloc(1,2): master_allocated",
        fb.master_allocated,
        6,
    );
    all_ok &= check(
        "FedBudget after alloc(1,2): sub_capacities[1]",
        fb.sub_capacities[1],
        2,
    );
    // CapacityConservation spot-check.
    all_ok &= check(
        "FedBudget consistency master==sum(caps)",
        fb.master_allocated == fb.sub_capacities[0] + fb.sub_capacities[1],
        true,
    );
    let g1 = fb.allocate_from_sub_pool(0, 3); // sub_alloc[0] 0+3 <= cap 4
    all_ok &= check("FedBudget allocate_from_sub_pool(0,3) accepted", g1, true);
    all_ok &= check(
        "FedBudget after from(0,3): sub_allocated[0]",
        fb.sub_allocated[0],
        3,
    );
    let g2 = fb.allocate_from_sub_pool(0, 2); // 3+2 = 5 > cap 4 -> reject
    all_ok &= check(
        "FedBudget allocate_from_sub_pool(0,2) rejected (over sub cap)",
        g2,
        false,
    );
    all_ok &= check(
        "FedBudget after from reject: sub_allocated[0] unchanged",
        fb.sub_allocated[0],
        3,
    );
    fb.release_from_sub_pool(0, 1); // sub_alloc[0] 3 -> 2
    all_ok &= check(
        "FedBudget after release(0,1): sub_allocated[0]",
        fb.sub_allocated[0],
        2,
    );

    // RelationshipGraph: weighted graph with a consistent adjacency view.
    // Build edges 0->1(w2), 1->2(w1), 0->2(w0), then remove 0->1; both the edge
    // list and the adjacency view must drop exactly the (0,1) pair.
    let mut g = RelationshipGraph::new(3, 2);
    all_ok &= check("RelGraph new(3,2): edges empty", g.edges.len(), 0);
    all_ok &= check("RelGraph new(3,2): adjacency empty", g.adjacency.len(), 0);
    g.add_edge(0, 1, 2);
    all_ok &= check("RelGraph after add(0,1,2): edges.len()", g.edges.len(), 1);
    all_ok &= check(
        "RelGraph after add(0,1,2): adjacency[0]",
        g.adjacency[0],
        (0, 1),
    );
    all_ok &= check("RelGraph after add(0,1,2): edges[0]", g.edges[0], (0, 1, 2));
    g.add_edge(1, 2, 1);
    g.add_edge(0, 2, 0);
    all_ok &= check("RelGraph after 3 adds: edges.len()", g.edges.len(), 3);
    all_ok &= check(
        "RelGraph after 3 adds: adjacency.len()",
        g.adjacency.len(),
        3,
    );
    g.remove_edge(0, 1); // drops (0,1) from both lists
    all_ok &= check("RelGraph after remove(0,1): edges.len()", g.edges.len(), 2);
    all_ok &= check(
        "RelGraph after remove(0,1): adjacency.len()",
        g.adjacency.len(),
        2,
    );
    all_ok &= check(
        "RelGraph after remove(0,1): adjacency[0] now (1,2)",
        g.adjacency[0],
        (1, 2),
    );
    all_ok &= check(
        "RelGraph after remove(0,1): adjacency[1] now (0,2)",
        g.adjacency[1],
        (0, 2),
    );
    all_ok &= check(
        "RelGraph after remove(0,1): edges[0] now (1,2,1)",
        g.edges[0],
        (1, 2, 1),
    );

    // PropagationPassGraph: one path-graph round with snapshot isolation.
    // Node 2 must read node 1's round-start value 2 even though node 1 has
    // already committed 1 in this round, so node 2 becomes 2 rather than 1.
    let mut pp = PropagationPass::new(
        3,
        4,
        3,
        vec![(0usize, 1usize), (1usize, 2usize)],
        vec![0u64, 2, 3],
    );
    all_ok &= check("PropPass new: round idle", pp.round, Round::Idle);
    all_ok &= check("PropPass new: iteration", pp.iteration, 0);
    pp.start_round();
    all_ok &= check("PropPass start: snapshot[1]", pp.snapshot[1], 2);
    all_ok &= check("PropPass start: updated[1] false", pp.updated[1], false);
    pp.update_node(1);
    all_ok &= check("PropPass update node 1: value", pp.values[1], 1);
    pp.update_node(2);
    all_ok &= check("PropPass snapshot isolation at node 2", pp.values[2], 2);
    pp.update_node(0);
    all_ok &= check("PropPass full round coverage", pp.all_nodes_updated(), true);
    pp.end_round();
    all_ok &= check("PropPass end: iteration", pp.iteration, 1);
    all_ok &= check("PropPass end: changed", pp.changed, true);

    // Boundary: a changing round may close exactly at the iteration ceiling.
    let mut pc = PropagationPass::new(2, 1, 2, vec![(0usize, 1usize)], vec![0u64, 2]);
    pc.start_round();
    pc.update_node(0);
    pc.update_node(1);
    pc.end_round();
    all_ok &= check("PropPass ceiling: iteration == max", pc.iteration, 1);
    all_ok &= check("PropPass ceiling: change retained", pc.changed, true);
    pc.terminate();

    // ConvergenceGovernorPhaseAware: a COLD start (peak never reached) must
    // never cool, even with a low average.
    let mut pg = ConvergenceGovernorPhaseAware::new(10, 30, 3, 50);
    all_ok &= check("PhaseGov new: ACTIVE", pg.state, GovState::Active);
    all_ok &= check("PhaseGov new: COLD", pg.gradient_phase, Phase::Cold);
    all_ok &= check("PhaseGov new: no peak", pg.peak_observed, false);
    pg.update(5); // cold delta (< threshold), low avg: must stay ACTIVE/COLD
    all_ok &= check(
        "PhaseGov cold delta: stays ACTIVE (no cool-from-cold)",
        pg.state,
        GovState::Active,
    );
    all_ok &= check(
        "PhaseGov cold delta: phase COLD",
        pg.gradient_phase,
        Phase::Cold,
    );
    all_ok &= check(
        "PhaseGov cold delta: still no peak",
        pg.peak_observed,
        false,
    );
    pg.update(3); // still cold
    all_ok &= check("PhaseGov still cold: ACTIVE", pg.state, GovState::Active);
    all_ok &= check("PhaseGov still cold: no peak", pg.peak_observed, false);

    // Convergence path: warm up (peak), cool, converge, awaken, re-converge.
    // `update` computes the average of the post-slide window. Reaching
    // AWAKENED needs the window average to exceed the awaken threshold, which a
    // single large delta in a 3-slot window cannot do, so the sequence runs
    // several steps.
    let mut pg2 = ConvergenceGovernorPhaseAware::new(10, 30, 3, 50);
    pg2.update(12); // window <<12>>, avg 12; delta>=threshold -> peak; WARMING;
                        // avg 12 < 2*threshold(20) and peak -> COOLING
    all_ok &= check("PhaseGov2 warm: COOLING", pg2.state, GovState::Cooling);
    all_ok &= check(
        "PhaseGov2 warm: WARMING",
        pg2.gradient_phase,
        Phase::Warming,
    );
    all_ok &= check("PhaseGov2 warm: peak set", pg2.peak_observed, true);
    pg2.update(2); // window <<12,2>>, avg 14/2 = 7 < threshold(10) -> CONVERGED
    all_ok &= check("PhaseGov2: CONVERGED", pg2.state, GovState::Converged);
    all_ok &= check(
        "PhaseGov2: DECLINING (peak set, sub-threshold delta)",
        pg2.gradient_phase,
        Phase::Declining,
    );
    pg2.update(10); // window <<12,2,10>>, avg 24/3 = 8; peak && delta>=threshold
                       // -> ACTIVE_LEARNING; 8 not > awaken(30) -> stays CONVERGED
    all_ok &= check(
        "PhaseGov2: ACTIVE_LEARNING phase",
        pg2.gradient_phase,
        Phase::ActiveLearning,
    );
    all_ok &= check("PhaseGov2: still CONVERGED", pg2.state, GovState::Converged);
    pg2.update(50); // window <<2,10,50>>, avg 62/3 = 20; not > awaken -> CONVERGED
    all_ok &= check(
        "PhaseGov2: avg 20 <= awaken, stays CONVERGED",
        pg2.state,
        GovState::Converged,
    );
    pg2.update(50); // window <<10,50,50>>, avg 110/3 = 36 > awaken(30) -> AWAKENED
    all_ok &= check("PhaseGov2: AWAKENED", pg2.state, GovState::Awakened);
    pg2.update(2); // window <<50,50,2>>, avg 102/3 = 34; not < threshold -> AWAKENED
    all_ok &= check(
        "PhaseGov2: avg 34 >= threshold, stays AWAKENED",
        pg2.state,
        GovState::Awakened,
    );
    pg2.update(2); // window <<50,2,2>>, avg 54/3 = 18; still >= threshold -> AWAKENED
    all_ok &= check(
        "PhaseGov2: avg 18 >= threshold, stays AWAKENED",
        pg2.state,
        GovState::Awakened,
    );
    pg2.update(2); // window <<2,2,2>>, avg 6/3 = 2 < threshold(10) -> CONVERGED
    all_ok &= check("PhaseGov2: re-CONVERGED", pg2.state, GovState::Converged);
    all_ok &= check(
        "PhaseGov2: DECLINING phase",
        pg2.gradient_phase,
        Phase::Declining,
    );

    // EquivalenceClass: union-find. Transitivity via union; cycle signal.
    let mut uf = EquivalenceClass::new(4, 6);
    all_ok &= check("EqClass new(4): find(0)==0", uf.find(0), 0);
    all_ok &= check("EqClass new(4): find(3)==3", uf.find(3), 3);
    all_ok &= check("EqClass union(0,1) merges", uf.union(0, 1), true);
    all_ok &= check("EqClass union(1,2) merges", uf.union(1, 2), true);
    all_ok &= check("EqClass same(0,2) transitive", uf.same(0, 2), true);
    all_ok &= check("EqClass same(0,1)", uf.same(0, 1), true);
    all_ok &= check(
        "EqClass find(0)==find(2) (one class)",
        uf.find(0),
        uf.find(2),
    );
    all_ok &= check(
        "EqClass union(0,2) already same -> false (cycle signal)",
        uf.union(0, 2),
        false,
    );
    all_ok &= check("EqClass same(0,3) distinct classes", uf.same(0, 3), false);

    // CompetitiveSelection Hard: argmax winner.
    let mut ch = CompetitiveSelectionHard::new(3);
    ch.update_score(0, 5);
    ch.update_score(1, 3);
    ch.update_score(2, 8);
    all_ok &= check(
        "CompSel Hard: allocation None before evaluate",
        ch.allocation,
        None,
    );
    ch.evaluate();
    all_ok &= check(
        "CompSel Hard: winner is candidate 2 (score 8)",
        ch.allocation,
        Some(2usize),
    );

    // Tie-break contract: candidates 0 and 2
    // both score 8 (tied argmax); the LOWEST-index candidate wins. Witnesses the
    // TLA+ WinnerTieBreak invariant and rules out a highest-index / arbitrary
    // tie-break (which would pick candidate 2). Matches the Verus argmax scan,
    // which keeps the lower-indexed candidate on a tie (strict > replacement).
    let mut cht = CompetitiveSelectionHard::new(3);
    cht.update_score(0, 8);
    cht.update_score(1, 5);
    cht.update_score(2, 8);
    cht.evaluate();
    all_ok &= check(
        "CompSel Hard tie-break: 0,2 tie at 8; winner is lowest index 0",
        cht.allocation,
        Some(0usize),
    );

    // Active hard-exclusive carrier: seat 0 claims candidate 0. Seat 1's
    // global argmax is also candidate 0, but Available(1) excludes it, so seat
    // 1 receives its best remaining candidate 1.
    let mut che = CompetitiveSelectionHardExclusive::new(2, 3, 10);
    che.update_score(0, 0, 9);
    che.update_score(0, 1, 8);
    che.update_score(1, 0, 10);
    che.update_score(1, 1, 7);
    che.update_score(1, 2, 6);
    che.evaluate(0);
    che.evaluate(1);
    all_ok &= check(
        "CompSel HardExclusive seat 0 winner",
        che.allocation[0],
        Some(0u64),
    );
    all_ok &= check(
        "CompSel HardExclusive seat 1 best available",
        che.allocation[1],
        Some(1u64),
    );
    all_ok &= check(
        "CompSel HardExclusive mutual exclusion",
        che.allocation[0] != che.allocation[1],
        true,
    );
    che.update_score(0, 2, 10);
    all_ok &= check(
        "CompSel HardExclusive score update clears seat 0",
        che.allocation[0],
        None,
    );
    all_ok &= check(
        "CompSel HardExclusive score update clears coupled seat 1",
        che.allocation[1],
        None,
    );

    // CompetitiveSelection Soft: reserved-floor sequential Sainte-Lague (Webster).
    // WeightTotal = 12, order c1,c2,c3, lowest-index tie-break. The vectors cover
    // the Soft-mode proportionality boundary and match the TLA+ construction's
    // own reference implementation bit-for-bit.
    let soft_kat: [([u64; 3], [u64; 3]); 8] = [
        ([1, 1, 1], [4, 4, 4]),
        ([1, 1, 3], [3, 3, 6]),
        ([1, 2, 2], [3, 5, 4]),
        ([1, 3, 1], [3, 6, 3]),
        ([2, 2, 3], [4, 3, 5]),
        ([1, 2, 3], [3, 4, 5]),
        ([3, 1, 1], [6, 3, 3]),
        ([3, 3, 3], [4, 4, 4]),
    ];
    for (scores, want) in soft_kat.iter() {
        let cs = CompetitiveSelectionSoft::new(scores.to_vec(), 12, 4);
        let got = [cs.weight_at(0), cs.weight_at(1), cs.weight_at(2)];
        all_ok &= check(
            &format!("CompSel Soft Webster: scores {:?} -> weights", scores),
            got,
            *want,
        );
    }
    all_ok &= check(
        "CompSel Soft: weight_total==12",
        CompetitiveSelectionSoft::new(vec![1u64, 2, 3], 12, 4).weight_total,
        12,
    );

    // Mutable-score allocation correspondence: Init exposes the reserved-floor state;
    // AssignNext commits exactly one lowest-index priority winner; UpdateScore
    // writes one score and atomically invalidates every prior extra award.
    let mut csl = CompetitiveSelectionSoft::init(vec![1u64, 3, 1], 12, 4);
    all_ok &= check(
        "CompSel mutable scores Init: reserved weights",
        csl.extra.clone(),
        vec![0u64, 0, 0],
    );
    let first_soft_winner = csl.assign_next();
    all_ok &= check(
        "CompSel mutable scores AssignNext: priority winner",
        first_soft_winner,
        1usize,
    );
    all_ok &= check(
        "CompSel mutable scores AssignNext: one exact award",
        csl.extra.clone(),
        vec![0u64, 1, 0],
    );
    csl.update_score(0, 4);
    all_ok &= check(
        "CompSel mutable scores UpdateScore: score committed",
        csl.scores[0],
        4u64,
    );
    all_ok &= check(
        "CompSel mutable scores UpdateScore: awards invalidated",
        csl.extra.clone(),
        vec![0u64, 0, 0],
    );
    for _ in 0..9 {
        csl.assign_next();
    }
    let csl_rebuilt = CompetitiveSelectionSoft::new(vec![4u64, 3, 1], 12, 4);
    all_ok &= check(
        "CompSel mutable scores replay matches batch Webster carrier",
        csl.extra.clone(),
        csl_rebuilt.extra.clone(),
    );
    all_ok &= check(
        "CompSel mutable scores terminal normalization",
        csl.weight_at(0) + csl.weight_at(1) + csl.weight_at(2),
        12u64,
    );

    // CompetitiveSelection Ranked: top-K. scores [3,1,4,2], K=2 -> select {2,0}.
    let mut cr = CompetitiveSelectionRanked::new(vec![3, 1, 4, 2], 2, 4);
    cr.select();
    all_ok &= check(
        "CompSel Ranked: candidate 2 selected (score 4)",
        cr.selected[2],
        true,
    );
    all_ok &= check(
        "CompSel Ranked: candidate 0 selected (score 3)",
        cr.selected[0],
        true,
    );
    all_ok &= check(
        "CompSel Ranked: candidate 1 not selected (score 1)",
        cr.selected[1],
        false,
    );
    all_ok &= check(
        "CompSel Ranked: candidate 3 not selected (score 2)",
        cr.selected[3],
        false,
    );

    // Tie-break contract: candidates 1 and 2
    // both score 3, and only one fits under the K=2 cutoff (candidate 0 at 5
    // takes the first slot). The LOWER-index candidate (1) is selected and the
    // higher (2) excluded. Witnesses the TLA+ RankedTieBreak invariant (every
    // selected candidate is Better -- score, then lowest position -- than every
    // non-selected one) and rules out a highest-index / arbitrary tie-break
    // (which would select 2 over 1). Matches the Verus find_max_unselected scan,
    // which keeps the lower index on a tie (strict > replacement).
    let mut crt = CompetitiveSelectionRanked::new(vec![5, 3, 3, 1], 2, 5);
    crt.select();
    all_ok &= check(
        "CompSel Ranked tie-break: 1,2 tie at 3; lower index 1 selected",
        crt.selected[1],
        true,
    );
    all_ok &= check(
        "CompSel Ranked tie-break: 1,2 tie at 3; higher index 2 excluded",
        crt.selected[2],
        false,
    );

    // BacktrackingTraversalUndo: paired do/undo over the canonical modulo-3
    // mutation instance. Different deltas make aux independent of depth.
    let mut bt = BacktrackingTraversal::new(2, 3, 0);
    all_ok &= check("Backtrack new: aux == 0", bt.aux, 0);
    all_ok &= check("Backtrack new: depth 0", bt.path.len(), 0);
    bt.descend(1, 2); // depth 1, aux 2, save 0
    all_ok &= check("Backtrack after descend(1,2): aux == 2", bt.aux, 2);
    all_ok &= check("Backtrack token[0] saved 0", bt.ledger[0].saved, 0);
    all_ok &= check("Backtrack token[0] delta 2", bt.ledger[0].delta, 2);
    bt.descend(2, 2); // depth 2, aux 1, save 2
    all_ok &= check("Backtrack after second delta 2: aux == 1", bt.aux, 1);
    bt.descend(1, 1); // depth 3 (leaf), aux 2, save 1
    all_ok &= check("Backtrack at leaf: aux == 2", bt.aux, 2);
    all_ok &= check("Backtrack at leaf: depth == 3", bt.path.len(), 3);
    bt.visit(); // record [1,2,1]
    all_ok &= check("Backtrack after visit: visited.len()", bt.visited.len(), 1);
    all_ok &= check(
        "Backtrack visited path is full depth",
        bt.visited[0].len(),
        3,
    );
    all_ok &= check("Backtrack visited path[0]", bt.visited[0][0], 1);
    all_ok &= check("Backtrack visited path[1]", bt.visited[0][1], 2);
    bt.ascend(); // undo delta 1: restore saved 1
    all_ok &= check(
        "Backtrack after ascend: aux restored to token saved 1",
        bt.aux,
        1,
    );
    all_ok &= check("Backtrack after ascend: depth 2", bt.path.len(), 2);
    bt.ascend(); // undo delta 2: restore saved 2
    all_ok &= check(
        "Backtrack after 2nd ascend: aux restored to token saved 2",
        bt.aux,
        2,
    );

    // ── Signal named composition. SetValue's change-detection filter plus the
    // guarded change epoch and atomic pending->notified move. Each vector rules
    // out a named wrong-but-plausible construction.
    // Values {0,1,2}, Listeners {l0,l1}.
    let mut sig = Signal::new(0, 3, 2);
    all_ok &= check("Signal new: current_value 0", sig.current_value, 0);
    all_ok &= check("Signal new: no change observed", sig.change_observed, false);
    all_ok &= check("Signal new: l0 not pending", sig.is_pending(0), false);
    all_ok &= check("Signal new: l1 not pending", sig.is_pending(1), false);
    all_ok &= check("Signal new: l0 not notified", sig.is_notified(0), false);
    all_ok &= check("Signal new: l1 not notified", sig.is_notified(1), false);

    // SetValue(1): a change fires -- pending' = Listeners (BOTH l0 and
    // l1), notified' = {}. Checking BOTH listeners rules out a
    // partial-pending construction that skips listener 0 (index off-by-one
    // starting at 1) or stops one short of the last listener.
    all_ok &= check(
        "Signal set_value(1): fires (guard 1 /= 0)",
        sig.set_value(1),
        true,
    );
    all_ok &= check(
        "Signal after set_value(1): current_value 1",
        sig.current_value,
        1,
    );
    all_ok &= check(
        "Signal after set_value(1): change observed",
        sig.change_observed,
        true,
    );
    all_ok &= check(
        "Signal after set_value(1): l0 pending (rules out skip-first)",
        sig.is_pending(0),
        true,
    );
    all_ok &= check(
        "Signal after set_value(1): l1 pending (rules out stop-short)",
        sig.is_pending(1),
        true,
    );

    // NotifyListener(l0): ONE step moves l0 from pending to notified. The
    // explicit both-views check is PendingNotifiedDisjointness at l0 -- it rules
    // out a non-atomic construction that adds to notified without removing
    // from pending; the SignalDecomposed witness exposes that overlap. The l1
    // frame check rules out a
    // clear-all-pending construction.
    sig.notify_listener(0);
    all_ok &= check(
        "Signal after notify(l0): l0 not pending",
        sig.is_pending(0),
        false,
    );
    all_ok &= check(
        "Signal after notify(l0): l0 notified",
        sig.is_notified(0),
        true,
    );
    all_ok &= check(
        "Signal after notify(l0): l0 not in both views (disjoint)",
        sig.is_pending(0) && sig.is_notified(0),
        false,
    );
    all_ok &= check(
        "Signal after notify(l0): l1 still pending (frame)",
        sig.is_pending(1),
        true,
    );

    // SetValue(1) again -- SAME value: the change-detection filter must
    // reject (returns false) and the state must be UNCHANGED. Rules out the
    // filter-drop construction (the exact SignalFromAuditSink_NEG break: a
    // Signal that fires on a non-change) -- that construction would refill
    // pending (l0 back to pending) and reset notified (l0 dropped).
    all_ok &= check(
        "Signal set_value(1) same value: filter rejects",
        sig.set_value(1),
        false,
    );
    all_ok &= check(
        "Signal after rejected set: l0 still not pending (unchanged)",
        sig.is_pending(0),
        false,
    );
    all_ok &= check(
        "Signal after rejected set: l0 still notified (unchanged)",
        sig.is_notified(0),
        true,
    );
    all_ok &= check(
        "Signal after rejected set: l1 still pending (unchanged)",
        sig.is_pending(1),
        true,
    );
    all_ok &= check(
        "Signal after rejected set: change provenance retained",
        sig.change_observed,
        true,
    );

    sig.notify_listener(1);
    all_ok &= check(
        "Signal after notify(l1): l1 notified",
        sig.is_notified(1),
        true,
    );
    all_ok &= check(
        "Signal after notify(l1): pending drained",
        sig.is_pending(0) || sig.is_pending(1),
        false,
    );

    // SetValue(2): a change after a full notify cycle -- notified must
    // RESET to {} in the same step pending refills. Rules out the
    // stale-notified construction (SetValue updates value + pending but
    // keeps notified) -- that construction would leave l0/l1 in notified
    // while pending refills: the pending ∩ notified /= {} state that
    // PendingNotifiedDisjointness forbids.
    all_ok &= check(
        "Signal set_value(2): fires (guard 2 /= 1)",
        sig.set_value(2),
        true,
    );
    all_ok &= check(
        "Signal after set_value(2): l0 notified reset",
        sig.is_notified(0),
        false,
    );
    all_ok &= check(
        "Signal after set_value(2): l1 notified reset",
        sig.is_notified(1),
        false,
    );
    all_ok &= check(
        "Signal after set_value(2): l0 pending again",
        sig.is_pending(0),
        true,
    );
    all_ok &= check(
        "Signal after set_value(2): l1 pending again",
        sig.is_pending(1),
        true,
    );

    // ── RateLimit named composition, at the TLA+ configuration's constants
    // (MaxPerWindow=3, WindowDuration=5, MaxClock=12). Each vector rules out a
    // named wrong-but-plausible construction.
    let mut rl = RateLimit::new(3, 5, 12);
    all_ok &= check("RateLimit new: count 0", rl.count, 0);
    all_ok &= check("RateLimit new: window_start 0", rl.window_start, 0);
    all_ok &= check("RateLimit new: clock 0", rl.clock, 0);

    // Grant path up to the ceiling, then rejection AT the ceiling. The 4th
    // acquire must return false with count unchanged -- rules out an
    // unguarded-increment construction that grants without the
    // count < MaxPerWindow check (WindowCountBound broken directly).
    all_ok &= check("RateLimit acquire 1: granted", rl.try_acquire(), true);
    all_ok &= check("RateLimit acquire 2: granted", rl.try_acquire(), true);
    all_ok &= check(
        "RateLimit acquire 3: granted (at ceiling)",
        rl.try_acquire(),
        true,
    );
    all_ok &= check("RateLimit after 3 acquires: count 3", rl.count, 3);
    all_ok &= check(
        "RateLimit acquire 4: REJECTED at ceiling",
        rl.try_acquire(),
        false,
    );
    all_ok &= check(
        "RateLimit after rejected acquire: count still 3",
        rl.count,
        3,
    );
    all_ok &= check(
        "RateLimit after rejected acquire: window_start still 0",
        rl.window_start,
        0,
    );

    // Advance the clock to exactly WindowDuration (5): the window expires.
    rl.tick();
    rl.tick();
    rl.tick();
    rl.tick();
    rl.tick();
    all_ok &= check("RateLimit after 5 ticks: clock 5", rl.clock, 5);

    // Rollover: the expired-window acquire must re-anchor AND grant in one
    // step -- count' = 1 (NOT count+1: rules out a rollover-keeps-counting
    // construction that would report 4) and window_start' = clock (rules out
    // the exact RateLimitFromBudget_NEG break: a rollover that omits
    // window_start' = clock, letting acquires leak across window boundaries).
    all_ok &= check(
        "RateLimit acquire after expiry: granted (rollover)",
        rl.try_acquire(),
        true,
    );
    all_ok &= check(
        "RateLimit after rollover: count 1 (fresh window, not 4)",
        rl.count,
        1,
    );
    all_ok &= check(
        "RateLimit after rollover: window_start re-anchored to 5",
        rl.window_start,
        5,
    );

    // Fill the fresh window to its ceiling and confirm rejection again.
    all_ok &= check(
        "RateLimit acquire (fresh window) 2: granted",
        rl.try_acquire(),
        true,
    );
    all_ok &= check(
        "RateLimit acquire (fresh window) 3: granted",
        rl.try_acquire(),
        true,
    );
    all_ok &= check(
        "RateLimit acquire (fresh window) 4: REJECTED",
        rl.try_acquire(),
        false,
    );
    all_ok &= check("RateLimit fresh window at ceiling: count 3", rl.count, 3);

    // Advance to clock 9: elapsed 9-5 = 4 < WindowDuration 5 -- the window is
    // NOT yet expired, so an acquire at the ceiling must still be rejected.
    // Rules out an off-by-one early-rollover construction (elapsed >=
    // duration-1) that would roll over and grant here.
    rl.tick();
    rl.tick();
    rl.tick();
    rl.tick();
    all_ok &= check("RateLimit after 4 more ticks: clock 9", rl.clock, 9);
    all_ok &= check(
        "RateLimit acquire at elapsed 4 < 5: REJECTED (no early rollover)",
        rl.try_acquire(),
        false,
    );
    all_ok &= check("RateLimit no early rollover: count still 3", rl.count, 3);
    all_ok &= check(
        "RateLimit no early rollover: window_start still 5",
        rl.window_start,
        5,
    );

    // One more tick to clock 10: elapsed 10-5 = 5 >= 5 -- now it rolls over.
    rl.tick();
    all_ok &= check(
        "RateLimit acquire at elapsed 5: granted (rollover)",
        rl.try_acquire(),
        true,
    );
    all_ok &= check("RateLimit second rollover: count 1", rl.count, 1);
    all_ok &= check(
        "RateLimit second rollover: window_start 10",
        rl.window_start,
        10,
    );

    // ── SelectThenActuate composition-theorem witness:
    // argmax selection (Evaluate) coupled with actuation (Actuate) over a
    // shared allocation, plus the interaction step UpdateScore that nulls the
    // allocation AND retracts actuated in ONE step. Each vector rules out a
    // named wrong-but-plausible construction; the interaction-step vector covers
    // the stale-winner race. Seats {s0,s1}, Candidates {c0,c1,c2}.
    let mut sta = SelectThenActuate::new(2, 3);
    all_ok &= check(
        "SelectThenActuate new: seat 0 allocation NULL",
        sta.is_allocated(0),
        false,
    );
    all_ok &= check(
        "SelectThenActuate new: seat 0 not actuated",
        sta.is_actuated(0),
        false,
    );
    all_ok &= check(
        "SelectThenActuate new: seat 1 allocation NULL",
        sta.is_allocated(1),
        false,
    );

    // Seat 0 scores: candidate 2 is the unique argmax (8 > 5 > 3). Seat 1
    // scores: candidate 0 is the unique argmax (7 > 2 > 0). update_score also
    // exercises the interaction fields on a not-yet-actuated seat (allocation
    // stays NULL, actuated stays false), the trivial case of the interaction.
    sta.update_score(0, 0, 5);
    sta.update_score(0, 1, 3);
    sta.update_score(0, 2, 8);
    sta.update_score(1, 0, 7);
    sta.update_score(1, 1, 2);
    all_ok &= check(
        "SelectThenActuate scores set: score_at(0,2)==8",
        sta.score_at(0, 2),
        8,
    );

    // Evaluate seat 0: WinnerOptimality selects the ARGMAX (candidate 2). Rules
    // out an evaluate that selects a non-argmax candidate -- a first-candidate
    // construction would pick 0, a min construction would pick 1; the argmax is
    // neither the first nor the lowest-scoring, so this vector separates all
    // three.
    sta.evaluate(0);
    all_ok &= check(
        "SelectThenActuate evaluate(0): winner candidate 2 (argmax, not first/min)",
        sta.allocation[0],
        Some(2u64),
    );
    sta.evaluate(1);
    all_ok &= check(
        "SelectThenActuate evaluate(1): winner candidate 0 (argmax)",
        sta.allocation[1],
        Some(0u64),
    );

    // Actuate both seats (allocation Some, not yet actuated -- both guards hold).
    sta.actuate(0);
    all_ok &= check(
        "SelectThenActuate actuate(0): seat 0 actuated",
        sta.is_actuated(0),
        true,
    );
    all_ok &= check(
        "SelectThenActuate actuate(0): ActuationScope -- seat 0 allocation still Some",
        sta.is_allocated(0),
        true,
    );
    sta.actuate(1);
    all_ok &= check(
        "SelectThenActuate actuate(1): seat 1 actuated",
        sta.is_actuated(1),
        true,
    );

    // Interaction step: update a score on the ALREADY-ACTUATED
    // seat 0. One step must (a) retract seat 0 from actuated and (b) null its
    // allocation. Rules out the stale-winner construction that updates scores
    // and nulls the allocation but KEEPS actuated -- that construction would
    // leave seat 0 with actuated == true while allocation == NULL, the exact
    // ActuationScope violation.
    sta.update_score(0, 1, 9);
    all_ok &= check(
        "SelectThenActuate interaction: seat 0 actuated RETRACTED (rules out keeps-actuated)",
        sta.is_actuated(0),
        false,
    );
    all_ok &= check(
        "SelectThenActuate interaction: seat 0 allocation NULL",
        sta.allocation[0],
        None,
    );
    all_ok &= check(
        "SelectThenActuate interaction: seat 0 score updated to 9",
        sta.score_at(0, 1),
        9,
    );
    // FRAME: the seat-0 update must not disturb seat 1 (a wrong update that
    // clobbers other seats would fail here).
    all_ok &= check(
        "SelectThenActuate frame: seat 1 still actuated",
        sta.is_actuated(1),
        true,
    );
    all_ok &= check(
        "SelectThenActuate frame: seat 1 allocation unchanged (candidate 0)",
        sta.allocation[1],
        Some(0u64),
    );

    // Re-evaluate seat 0 after the score change: scores[0] is now [5,9,8], so
    // candidate 1 is the new argmax (9 > 8 > 5). Confirms the re-selection
    // tracks the updated scores rather than a stale winner.
    sta.evaluate(0);
    all_ok &= check(
        "SelectThenActuate re-evaluate(0): new winner candidate 1 (score 9)",
        sta.allocation[0],
        Some(1u64),
    );
    // Actuating the freshly re-evaluated seat 0 is legal again (allocation Some,
    // not actuated after the retraction).
    all_ok &= check(
        "SelectThenActuate re-actuate(0): guards hold after re-evaluate",
        {
            sta.actuate(0);
            sta.is_actuated(0)
        },
        true,
    );

    // ── TraversalBudgetComposition composition-theorem witness: budgeted
    // traversal with a shared budget, total_cost +
    // budget_remaining = MaxBudget. Run at MaxBudget=3, NodeCost=2, 3 nodes
    // (root + 2 children), so SkipUnaffordable is reachable; at MaxBudget=6,
    // all three nodes fit exactly.
    let mut tbc = TraversalBudgetComposition::new(3, 0, 3);
    all_ok &= check(
        "TraversalBudgetComposition new: total_cost 0",
        tbc.total_cost,
        0,
    );
    all_ok &= check(
        "TraversalBudgetComposition new: budget_remaining 3",
        tbc.budget_remaining,
        3,
    );
    all_ok &= check(
        "TraversalBudgetComposition new: accepted empty",
        tbc.accepted.len(),
        0,
    );
    all_ok &= check(
        "TraversalBudgetComposition new: visited empty",
        tbc.visited.len(),
        0,
    );
    all_ok &= check(
        "TraversalBudgetComposition new: root queued",
        tbc.queue_contains(0),
        true,
    );

    // Visit-and-accept the root (NodeCost 2 <= budget 3): accept, deduct from
    // BOTH views (total_cost 0->2, budget 3->1), mark visited, enqueue the star
    // children {1,2}. The composition equation total_cost + budget = MaxBudget
    // (2 + 1 = 3) is the coupling.
    tbc.visit_and_accept(0);
    all_ok &= check(
        "TraversalBudgetComposition after visit root: total_cost 2",
        tbc.total_cost,
        2,
    );
    all_ok &= check(
        "TraversalBudgetComposition after visit root: budget_remaining 1 (2+1==MaxBudget 3)",
        tbc.budget_remaining,
        1,
    );
    all_ok &= check(
        "TraversalBudgetComposition after visit root: accepted len 1",
        tbc.accepted.len(),
        1,
    );
    all_ok &= check(
        "TraversalBudgetComposition after visit root: visited len 1",
        tbc.visited.len(),
        1,
    );
    all_ok &= check(
        "TraversalBudgetComposition after visit root: root removed",
        tbc.queue_contains(0),
        false,
    );
    all_ok &= check(
        "TraversalBudgetComposition after visit root: child 1 enqueued",
        tbc.queue_contains(1),
        true,
    );
    all_ok &= check(
        "TraversalBudgetComposition after visit root: child 2 enqueued",
        tbc.queue_contains(2),
        true,
    );

    // Attempt child 1 (NodeCost 2 > budget 1): SkipUnaffordable fires -- mark
    // visited but do NOT accept and do NOT deduct. This is the one place the
    // invariant's content is exercised: accepted becomes a PROPER subset of visited.
    // Rules out (a) accept-everything-visited (drops the budget guard on
    // acceptance, collapsing accepted == visited: it would report accepted
    // len 2 here); (b) a skip_unaffordable that deducts anyway (breaks
    // total_cost + budget = MaxBudget: total_cost or budget would move).
    tbc.skip_unaffordable(1);
    all_ok &= check(
        "TraversalBudgetComposition after skip_unaffordable(1): visited len 2",
        tbc.visited.len(),
        2,
    );
    all_ok &= check("TraversalBudgetComposition after skip_unaffordable(1): accepted len STILL 1 (accepted proper subset)", tbc.accepted.len(), 1);
    all_ok &= check(
        "TraversalBudgetComposition after skip_unaffordable(1): total_cost STILL 2 (no deduction)",
        tbc.total_cost,
        2,
    );
    all_ok &= check("TraversalBudgetComposition after skip_unaffordable(1): budget_remaining STILL 1 (no deduction)", tbc.budget_remaining, 1);
    all_ok &= check(
        "TraversalBudgetComposition after skip_unaffordable(1): child 1 removed",
        tbc.queue_contains(1),
        false,
    );

    // Skip child 2 (heuristic drop, no visit): remove it from the queue while
    // leaving accepted, visited, and both budget views unchanged.
    tbc.skip(2);
    all_ok &= check(
        "TraversalBudgetComposition after skip(2): accepted len 1 (frame)",
        tbc.accepted.len(),
        1,
    );
    all_ok &= check(
        "TraversalBudgetComposition after skip(2): visited len 2 (frame)",
        tbc.visited.len(),
        2,
    );
    all_ok &= check(
        "TraversalBudgetComposition after skip(2): total_cost 2 (frame)",
        tbc.total_cost,
        2,
    );
    all_ok &= check(
        "TraversalBudgetComposition after skip(2): budget_remaining 1 (frame)",
        tbc.budget_remaining,
        1,
    );
    all_ok &= check(
        "TraversalBudgetComposition after skip(2): child 2 removed",
        tbc.queue_contains(2),
        false,
    );
    all_ok &= check(
        "TraversalBudgetComposition after skip(2): queue empty",
        tbc.queue.len(),
        0,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (catalog primitives + compositions)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
