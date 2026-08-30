extern crate automation_structures;

use automation_structures::primitives::competitive_selection::{
    CompetitiveSelectionRanked, CompetitiveSelectionSoft,
};

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

    // Ranked Select: deterministic top-K by score then lowest candidate index.
    let mut ranked = CompetitiveSelectionRanked::new(vec![3, 1, 4, 2], 2, 9);
    ranked.select();
    ok &= check(
        "ranked top-K",
        ranked.selected.clone(),
        vec![true, false, true, false],
    );

    let mut tied = CompetitiveSelectionRanked::new(vec![5, 3, 3, 1], 2, 5);
    tied.select();
    ok &= check(
        "ranked cutoff tie uses lower index",
        tied.selected.clone(),
        vec![true, true, false, false],
    );

    let mut zero = CompetitiveSelectionRanked::new(vec![9, 8], 0, 9);
    zero.select();
    ok &= check(
        "ranked K=0 selects none",
        zero.selected.clone(),
        vec![false, false],
    );

    let mut wide = CompetitiveSelectionRanked::new(vec![2, 1], 5, 2);
    wide.select();
    ok &= check(
        "ranked K>candidate count selects all",
        wide.selected.clone(),
        vec![true, true],
    );

    ranked.update_scores(vec![0, 8, 7, 6]);
    ok &= check(
        "ranked score update invalidates selection",
        ranked.selected.clone(),
        vec![false; 4],
    );
    ranked.select();
    ok &= check(
        "ranked reselection uses new scores",
        ranked.selected.clone(),
        vec![false, true, true, false],
    );

    // Mutable-score soft selection: Init, AssignNext, UpdateScore, and terminal replay.
    let mut mutable_scores = CompetitiveSelectionSoft::init(vec![1u64, 3, 1], 12, 4);
    ok &= check(
        "mutable-score soft reserved floor",
        mutable_scores.extra.clone(),
        vec![0u64, 0, 0],
    );
    ok &= check(
        "mutable-score soft first priority winner",
        mutable_scores.assign_next(),
        1usize,
    );
    ok &= check(
        "mutable-score soft one exact award",
        mutable_scores.extra.clone(),
        vec![0u64, 1, 0],
    );

    mutable_scores.update_score(0, 4);
    ok &= check(
        "mutable-score soft score committed",
        mutable_scores.scores.clone(),
        vec![4u64, 3, 1],
    );
    ok &= check(
        "mutable-score soft update invalidates awards",
        mutable_scores.extra.clone(),
        vec![0u64, 0, 0],
    );

    for _ in 0..9 {
        mutable_scores.assign_next();
    }
    let batch = CompetitiveSelectionSoft::new(vec![4u64, 3, 1], 12, 4);
    ok &= check(
        "mutable-score soft replay equals terminal batch",
        mutable_scores.extra.clone(),
        batch.extra.clone(),
    );
    ok &= check(
        "soft terminal normalization",
        mutable_scores.weight_at(0) + mutable_scores.weight_at(1) + mutable_scores.weight_at(2),
        12u64,
    );

    let equal = CompetitiveSelectionSoft::new(vec![1u64, 1, 1], 12, 1);
    ok &= check(
        "soft equal-score tie bounded",
        equal.extra.clone(),
        vec![3u64, 3, 3],
    );

    if ok {
        println!("KAT_RESULT: SUCCESS (CompetitiveSelection ranked/mutable-score soft)");
    } else {
        println!("KAT_RESULT: FAIL (CompetitiveSelection ranked/mutable-score soft)");
        std::process::exit(1);
    }
}
