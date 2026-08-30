extern crate automation_structures;

use automation_structures::primitives::competitive_selection::CompetitiveSelectionHardExclusive;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn main() {
    let mut ok = true;

    let mut hard = CompetitiveSelectionHardExclusive::new(2, 3, 10);
    ok &= check("init seats", hard.num_seats, 2);
    ok &= check("init candidates", hard.num_candidates, 3);
    ok &= check("init seat 0 NULL", hard.allocation[0], None);
    ok &= check("init seat 1 NULL", hard.allocation[1], None);

    // Both seats prefer candidate 0 globally. Seat 1 must instead take its
    // highest-scoring member of Available(1) after seat 0 commits.
    hard.update_score(0, 0, 9);
    hard.update_score(0, 1, 8);
    hard.update_score(0, 2, 1);
    hard.update_score(1, 0, 10);
    hard.update_score(1, 1, 7);
    hard.update_score(1, 2, 6);
    ok &= check("seat 0 has available", hard.has_available(0), true);
    hard.evaluate(0);
    ok &= check("seat 0 global argmax", hard.allocation[0], Some(0u64));
    ok &= check(
        "candidate 0 unavailable to seat 1",
        hard.candidate_available(1, 0),
        false,
    );
    ok &= check(
        "candidate 1 available to seat 1",
        hard.candidate_available(1, 1),
        true,
    );
    hard.evaluate(1);
    ok &= check("seat 1 best available", hard.allocation[1], Some(1u64));
    ok &= check(
        "cross-seat mutual exclusion",
        hard.allocation[0] != hard.allocation[1],
        true,
    );

    // A live score change clears the entire coupled assignment in one commit.
    hard.update_score(0, 2, 10);
    ok &= check("global invalidation seat 0", hard.allocation[0], None);
    ok &= check("global invalidation seat 1", hard.allocation[1], None);
    ok &= check("updated score committed", hard.score_at(0, 2), 10);

    // Reversing evaluation order changes availability, while preserving both
    // optimality and exclusion.
    hard.evaluate(1);
    ok &= check(
        "reordered seat 1 takes candidate 0",
        hard.allocation[1],
        Some(0u64),
    );
    hard.evaluate(0);
    ok &= check(
        "reordered seat 0 takes best remaining",
        hard.allocation[0],
        Some(2u64),
    );
    ok &= check(
        "reordered exclusion",
        hard.allocation[0] != hard.allocation[1],
        true,
    );

    // Lowest candidate index is the WEnum/Pos tie-break, including after the
    // lower candidate has been removed from another seat's pool.
    let mut ties = CompetitiveSelectionHardExclusive::new(2, 3, 0);
    ties.evaluate(0);
    ties.evaluate(1);
    ok &= check("tie seat 0 lowest index", ties.allocation[0], Some(0u64));
    ok &= check(
        "tie seat 1 lowest available index",
        ties.allocation[1],
        Some(1u64),
    );

    // With more seats than candidates, the final seat's action is disabled.
    let mut exhausted = CompetitiveSelectionHardExclusive::new(3, 2, 0);
    exhausted.evaluate(0);
    exhausted.evaluate(1);
    ok &= check(
        "exhausted seat has no available candidate",
        exhausted.has_available(2),
        false,
    );
    ok &= check("exhausted seat remains NULL", exhausted.allocation[2], None);

    if ok {
        println!("KAT_RESULT: SUCCESS (CompetitiveSelectionHardExclusive)");
    } else {
        println!("KAT_RESULT: FAIL (CompetitiveSelectionHardExclusive)");
        std::process::exit(1);
    }
}
