extern crate automation_structures;

use automation_structures::compositions::equivalence_class::EquivalenceClass;

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
    let mut u = EquivalenceClass::new(6, 4);

    all_ok &= check("self representative", u.find(0), 0);
    all_ok &= check("initial classes separate", u.same(0, 1), false);
    all_ok &= check("equal-rank union merges", u.union(0, 1), true);
    all_ok &= check("equal-rank tie attaches rb under ra", u.parent[1], 0);
    all_ok &= check("equal-rank tie increments ra rank", u.rank[0], 1);
    all_ok &= check("successful union consumes one operation", u.ops_done, 1);

    all_ok &= check("repeated union rejected", u.union(0, 1), false);
    all_ok &= check("repeated union does not consume operation", u.ops_done, 1);
    all_ok &= check("repeated union frames parent", u.parent[1], 0);

    all_ok &= check("second equal-rank union merges", u.union(2, 3), true);
    all_ok &= check("second rank root", u.parent[3], 2);
    all_ok &= check("two rank-one roots merge", u.union(0, 2), true);
    all_ok &= check("rank tie remains deterministic", u.parent[2], 0);
    all_ok &= check("winning root rank increments to two", u.rank[0], 2);
    all_ok &= check("transitive class membership", u.same(1, 3), true);
    all_ok &= check("find follows multi-hop path", u.find(3), 0);
    all_ok &= check("find does not add path compression", u.parent[3], 2);

    all_ok &= check("unequal-rank union merges", u.union(4, 0), true);
    all_ok &= check("lower-rank root attaches to higher", u.parent[4], 0);
    all_ok &= check("unequal-rank union leaves winning rank", u.rank[0], 2);
    all_ok &= check("operation ceiling reached", u.ops_done, 4);

    let before_parent = u.parent.clone();
    let before_rank = u.rank.clone();
    all_ok &= check("union after MaxOps rejected", u.union(4, 5), false);
    all_ok &= check("MaxOps rejection frames parent", u.parent, before_parent);
    all_ok &= check("MaxOps rejection frames rank", u.rank, before_rank);
    all_ok &= check("MaxOps rejection frames counter", u.ops_done, 4);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (EquivalenceClass)");
    } else {
        println!("KAT_RESULT: FAIL (EquivalenceClass)");
        std::process::exit(1);
    }
}
