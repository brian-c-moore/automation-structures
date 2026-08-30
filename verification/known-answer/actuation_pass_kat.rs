extern crate automation_structures;

mod actuation_pass_vectors;

fn main() {
    if actuation_pass_vectors::run() {
        println!("KAT_RESULT: SUCCESS (ActuationPass)");
    } else {
        println!("KAT_RESULT: FAIL (ActuationPass)");
        std::process::exit(1);
    }
}
