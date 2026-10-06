extern crate automation_structures;

mod actuation_pass_vectors;

fn main() -> std::process::ExitCode {
    if actuation_pass_vectors::run() {
        println!("KAT_RESULT: SUCCESS (ActuationPass)");
        std::process::ExitCode::SUCCESS
    } else {
        println!("KAT_RESULT: FAIL (ActuationPass)");
        std::process::ExitCode::FAILURE
    }
}
