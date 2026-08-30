extern crate automation_structures;

use automation_structures::primitives::quality_hierarchy::QualityHierarchy;

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
    let mut h = QualityHierarchy::new(4, 5);

    all_ok &= check(
        "Init: isolated node accepts bounded properties",
        h.can_set_node_properties(0, 3, 1),
        true,
    );
    all_ok &= check(
        "SetNodeProperties: level above MaxLevel rejected",
        h.can_set_node_properties(0, 6, 1),
        false,
    );
    all_ok &= check(
        "SetNodeProperties: cost above MaxLevel rejected",
        h.can_set_node_properties(0, 3, 6),
        false,
    );

    h.set_node_properties(0, 3, 1);
    h.set_node_properties(1, 2, 2);
    h.set_node_properties(2, 2, 3);
    h.set_node_properties(3, 1, 4);

    all_ok &= check(
        "AddChild: valid ordered edge enabled",
        h.can_add_child(0, 1),
        true,
    );
    all_ok &= check("AddChild: self edge rejected", h.can_add_child(0, 0), false);
    all_ok &= check(
        "AddChild: level-order violation rejected",
        h.can_add_child(2, 0),
        false,
    );
    all_ok &= check(
        "AddChild: cost-order violation rejected",
        h.can_add_child(3, 2),
        false,
    );

    h.add_child(0, 1);
    all_ok &= check("AddChild: exact edge committed", h.has_edge(0, 1), true);
    all_ok &= check("AddChild: parent pointer committed", h.parent_of(1), 0);
    all_ok &= check(
        "AddChild: duplicate edge rejected",
        h.can_add_child(0, 1),
        false,
    );
    all_ok &= check(
        "AddChild: second parent rejected",
        h.can_add_child(2, 1),
        false,
    );
    all_ok &= check(
        "SetNodeProperties: parent node with children rejected",
        h.can_set_node_properties(0, 4, 1),
        false,
    );
    all_ok &= check(
        "SetNodeProperties: attached child rejected",
        h.can_set_node_properties(1, 1, 3),
        false,
    );
    all_ok &= check("Frame: unrelated node level unchanged", h.level_of(2), 2);
    all_ok &= check("Frame: unrelated node cost unchanged", h.cost_of(3), 4);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (QualityHierarchy)");
    } else {
        println!("KAT_RESULT: FAIL (QualityHierarchy)");
        std::process::exit(1);
    }
}
