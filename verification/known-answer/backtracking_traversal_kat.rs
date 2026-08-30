extern crate automation_structures;

use automation_structures::primitives::backtracking_traversal::BacktrackingTraversal;

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
    let mut all_ok = true;
    let mut t = BacktrackingTraversal::new(2, 3, 0);

    all_ok &= check("root cannot ascend", t.can_ascend(), false);
    all_ok &= check("non-leaf cannot visit", t.can_visit(), false);
    all_ok &= check("branch zero rejected", t.can_descend(0, 1), false);
    all_ok &= check("branch above factor rejected", t.can_descend(3, 1), false);
    all_ok &= check("delta zero rejected", t.can_descend(1, 0), false);
    all_ok &= check("delta above domain rejected", t.can_descend(1, 3), false);

    t.descend(1, 2);
    all_ok &= check("first do applies delta 2", t.aux, 2);
    all_ok &= check("first token saves pre-do value", t.ledger[0].saved, 0);
    t.descend(2, 2);
    all_ok &= check("second do wraps modulo 3", t.aux, 1);
    all_ok &= check("second token saves held value", t.ledger[1].saved, 2);
    t.descend(1, 1);
    all_ok &= check("leaf depth reached", t.is_leaf_exec(), true);
    all_ok &= check("leaf rejects further descent", t.can_descend(1, 1), false);
    all_ok &= check("fresh leaf can be visited", t.can_visit(), true);

    t.visit();
    all_ok &= check(
        "visit records exact path",
        t.visited[0].clone(),
        vec![1, 2, 1],
    );
    all_ok &= check("repeated visit rejected by set guard", t.can_visit(), false);

    t.ascend();
    all_ok &= check("nested undo restores saved 1", t.aux, 1);
    t.ascend();
    all_ok &= check("second undo restores saved 2", t.aux, 2);
    t.ascend();
    all_ok &= check("root undo restores InitAux", t.aux, 0);
    all_ok &= check("ledger empty after full restoration", t.ledger.len(), 0);
    all_ok &= check("visited leaf survives ascent frames", t.visited.len(), 1);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (BacktrackingTraversalUndo)");
    } else {
        println!("KAT_RESULT: FAIL (BacktrackingTraversalUndo)");
        std::process::exit(1);
    }
}
