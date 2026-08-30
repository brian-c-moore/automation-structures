extern crate automation_structures;

use automation_structures::compositions::federated_budget::FederatedBudget;

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
    let mut f = FederatedBudget::new(6, 2);

    all_ok &= check(
        "missing pool capacity request rejected",
        f.allocate_sub_pool(2, 1),
        false,
    );
    all_ok &= check(
        "zero capacity request rejected",
        f.allocate_sub_pool(0, 0),
        false,
    );
    all_ok &= check(
        "amount above master domain rejected",
        f.allocate_sub_pool(0, 7),
        false,
    );
    all_ok &= check(
        "rejected capacity requests frame master",
        f.master_allocated,
        0,
    );

    all_ok &= check(
        "pool 0 capacity 4 accepted",
        f.allocate_sub_pool(0, 4),
        true,
    );
    all_ok &= check("capacity commit moves master", f.master_allocated, 4);
    all_ok &= check("capacity commit moves named pool", f.sub_capacities[0], 4);
    all_ok &= check("capacity commit frames other pool", f.sub_capacities[1], 0);
    all_ok &= check(
        "master overspend rejected",
        f.allocate_sub_pool(1, 3),
        false,
    );
    all_ok &= check(
        "exact remaining master accepted",
        f.allocate_sub_pool(1, 2),
        true,
    );
    all_ok &= check(
        "master equals finite capacity sum",
        f.master_allocated,
        f.sub_capacities[0] + f.sub_capacities[1],
    );

    all_ok &= check(
        "missing pool consumption rejected",
        f.allocate_from_sub_pool(2, 1),
        false,
    );
    all_ok &= check(
        "zero consumption rejected",
        f.allocate_from_sub_pool(0, 0),
        false,
    );
    all_ok &= check(
        "pool 0 consumption 3 accepted",
        f.allocate_from_sub_pool(0, 3),
        true,
    );
    all_ok &= check("consumption commit moves named pool", f.sub_allocated[0], 3);
    all_ok &= check(
        "consumption commit frames other pool",
        f.sub_allocated[1],
        0,
    );
    all_ok &= check(
        "sub-pool overspend rejected",
        f.allocate_from_sub_pool(0, 2),
        false,
    );
    all_ok &= check(
        "overspend rejection frames allocation",
        f.sub_allocated[0],
        3,
    );

    all_ok &= check(
        "missing pool release rejected",
        f.release_from_sub_pool(2, 1),
        false,
    );
    all_ok &= check(
        "zero release rejected",
        f.release_from_sub_pool(0, 0),
        false,
    );
    all_ok &= check(
        "release above allocation rejected",
        f.release_from_sub_pool(0, 4),
        false,
    );
    all_ok &= check(
        "valid release accepted",
        f.release_from_sub_pool(0, 1),
        true,
    );
    all_ok &= check("release exact named-pool effect", f.sub_allocated[0], 2);
    all_ok &= check("release frames capacity", f.sub_capacities[0], 4);
    all_ok &= check("release frames other allocation", f.sub_allocated[1], 0);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (FederatedBudget)");
    } else {
        println!("KAT_RESULT: FAIL (FederatedBudget)");
        std::process::exit(1);
    }
}
