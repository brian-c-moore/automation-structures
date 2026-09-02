extern crate automation_structures;

use automation_structures::modalities::sequential::Sequential;

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
    let mut s = Sequential::new(2, 4, 0);
    ok &= check("Init cursor", s.pc, 0);
    ok &= check("Init inactive", s.active, false);
    ok &= check(
        "terminal stutter initially disabled",
        s.done_stuttering(),
        false,
    );
    ok &= check("first BeginStep admitted", s.begin_step(), true);
    ok &= check(
        "second BeginStep rejected while active",
        s.begin_step(),
        false,
    );
    ok &= check(
        "invalid completion choice rejected",
        s.complete_step(4),
        false,
    );
    ok &= check("invalid completion keeps active", s.active, true);
    ok &= check("first completion admitted", s.complete_step(2), true);
    ok &= check("first completion exact cursor", s.pc, 1);
    ok &= check("first completion exact value", s.value, 2);
    ok &= check("first completion exact history", s.history.clone(), vec![2]);
    ok &= check(
        "completion rejected while inactive",
        s.complete_step(3),
        false,
    );
    ok &= check("second BeginStep admitted", s.begin_step(), true);
    ok &= check("second completion admitted", s.complete_step(3), true);
    ok &= check("terminal cursor bounded", s.pc, 2);
    ok &= check("history agrees with execution position", s.history.clone(), vec![2, 3]);
    ok &= check("BeginStep rejected at step bound", s.begin_step(), false);
    let before = (s.pc, s.value, s.active, s.history.clone());
    ok &= check("terminal stutter enabled", s.done_stuttering(), true);
    ok &= check(
        "terminal stutter exact frame",
        (s.pc, s.value, s.active, s.history.clone()),
        before,
    );

    if ok {
        println!("KAT_RESULT: SUCCESS (Sequential modality)");
    } else {
        println!("KAT_RESULT: FAIL (Sequential modality)");
        std::process::exit(1);
    }
}
