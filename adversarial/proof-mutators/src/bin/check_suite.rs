//! `check-suite`: load and validate the hostile-submission suite, print a
//! one-line summary per case. Exit non-zero on the first structural problem.
//! This is the local well-formedness gate (no server required).

use proof_mutators::suite;
use std::path::PathBuf;

fn main() {
    let root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(suite::default_root);

    match suite::load_all(&root) {
        Ok(cases) => {
            println!(
                "# hostile-submission suite: {} cases ({})",
                cases.len(),
                root.display()
            );
            for c in &cases {
                println!(
                    "ok  {:32} decision={:?} family={} gates={:?}",
                    c.name,
                    c.expect.expected_decision,
                    c.expect.attack_family,
                    c.expect.expected_failing_gates,
                );
            }
            println!("ALL {} CASES WELL-FORMED", cases.len());
        }
        Err(e) => {
            eprintln!("SUITE CHECK FAILED: {e}");
            std::process::exit(1);
        }
    }
}
