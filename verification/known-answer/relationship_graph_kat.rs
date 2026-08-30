extern crate automation_structures;

use automation_structures::compositions::relationship_graph::RelationshipGraph;

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
    let mut g = RelationshipGraph::new(3, 5);

    all_ok &= check(
        "self-loop admission rejected",
        g.can_add_edge(1, 1, 2),
        false,
    );
    all_ok &= check("source boundary rejected", g.can_add_edge(3, 1, 2), false);
    all_ok &= check(
        "destination boundary rejected",
        g.can_add_edge(1, 3, 2),
        false,
    );
    all_ok &= check("weight boundary rejected", g.can_add_edge(0, 1, 6), false);

    all_ok &= check("first weighted edge added", g.add_edge(0, 1, 2), true);
    all_ok &= check(
        "exact weighted member present",
        g.contains_exact_edge(0, 1, 2),
        true,
    );
    all_ok &= check("adjacency projection present", g.contains_pair(0, 1), true);
    all_ok &= check(
        "duplicate weighted edge stutters",
        g.add_edge(0, 1, 2),
        false,
    );
    all_ok &= check("duplicate does not grow edge set carrier", g.edges.len(), 1);
    all_ok &= check(
        "duplicate does not grow adjacency carrier",
        g.adjacency.len(),
        1,
    );

    all_ok &= check(
        "second weight on same pair added",
        g.add_edge(0, 1, 4),
        true,
    );
    all_ok &= check("second weight grows weighted set", g.edges.len(), 2);
    all_ok &= check(
        "same pair does not duplicate adjacency",
        g.adjacency.len(),
        1,
    );
    all_ok &= check(
        "second weighted member present",
        g.contains_exact_edge(0, 1, 4),
        true,
    );
    all_ok &= check("unrelated edge added", g.add_edge(1, 2, 3), true);

    g.remove_edge(0, 1);
    all_ok &= check(
        "remove drops first weight",
        g.contains_exact_edge(0, 1, 2),
        false,
    );
    all_ok &= check(
        "remove drops all pair weights",
        g.contains_exact_edge(0, 1, 4),
        false,
    );
    all_ok &= check("remove drops adjacency pair", g.contains_pair(0, 1), false);
    all_ok &= check(
        "remove frames unrelated weighted edge",
        g.contains_exact_edge(1, 2, 3),
        true,
    );
    all_ok &= check(
        "remove frames unrelated adjacency",
        g.contains_pair(1, 2),
        true,
    );

    let before_edges = g.edges.clone();
    let before_adj = g.adjacency.clone();
    g.remove_edge(2, 0);
    all_ok &= check(
        "absent removal frames weighted carrier",
        g.edges,
        before_edges,
    );
    all_ok &= check(
        "absent removal frames adjacency carrier",
        g.adjacency,
        before_adj,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (RelationshipGraph)");
    } else {
        println!("KAT_RESULT: FAIL (RelationshipGraph)");
        std::process::exit(1);
    }
}
