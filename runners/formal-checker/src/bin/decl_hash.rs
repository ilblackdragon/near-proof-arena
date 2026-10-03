//! `decl-hash` — structural content hash of Lean declarations, the same
//! `decl_hash` the NDJSON audit uses to detect shadowed/changed trusted
//! declarations. Used by governance to pin `security/assumptions/*.json`
//! `lean_decl_digest`.
//!
//! ```text
//! lean4export ArenaCore -- ArenaCore.Assumptions.Sha256CollisionResistant > ex.ndjson
//! decl-hash --export ex.ndjson ArenaCore.Assumptions.Sha256CollisionResistant ...
//! ```
//! Prints one line per name: `<name> sha256:<hex>`; exits 1 if a name is missing.
use arena_formal_checker::ndjson::{hex, Export};
use std::path::PathBuf;

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().skip(1);
    let mut export = None;
    let mut names = Vec::new();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--export" => export = Some(PathBuf::from(args.next().ok_or_else(|| anyhow::anyhow!("--export FILE"))?)),
            _ => names.push(a),
        }
    }
    let ex = Export::read(&export.ok_or_else(|| anyhow::anyhow!("--export required"))?, 1 << 32)?;
    let mut missing = false;
    for n in names {
        match ex.decls.get(&n) {
            Some(d) => println!("{n} sha256:{}", hex(&ex.decl_hash(d))),
            None => {
                eprintln!("missing declaration {n}");
                missing = true;
            }
        }
    }
    std::process::exit(if missing { 1 } else { 0 })
}
