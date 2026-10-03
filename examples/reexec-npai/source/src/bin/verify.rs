//! `verify --public <dir> --claim <claim.bin> --proof <proof.bin>`
//!
//! LOCAL CONVENIENCE ONLY. On the `npai-v1` route the arena ignores this
//! binary and runs its own interpreter (`npai-verify`, runners/npai) on
//! `out/verifier.npai` with fuel `ChallengeParams.verifyFuel`. This wrapper
//! runs a verbatim copy of that interpreter (`src/npai_interp.rs`) on the same
//! image (embedded at build time, `NPAI_IMAGE`) with the challenge fuel 2^30,
//! so that `arena check-local` exercises exactly the certified bytecode.
//! Exit codes: 0 accept, 1 reject (trap / out of fuel / HALT 0), 2 usage/I/O.
use reexec::npai_interp::{decode, run_full, Inputs, Outcome, MAX_TAPE_LEN};
use std::path::PathBuf;
use std::process::ExitCode;

const IMAGE: &[u8] = include_bytes!(env!("NPAI_IMAGE"));
const FUEL: u64 = 1 << 30;

fn read(p: &std::path::Path) -> Option<Vec<u8>> {
    let b = std::fs::read(p).ok()?;
    if b.len() as u64 >= MAX_TAPE_LEN {
        return None;
    }
    Some(b)
}

fn main() -> ExitCode {
    let a = reexec::parse_args(&["public", "claim", "proof"]);
    let mut public = a["public"].clone();
    if public.is_dir() {
        public.push("public.bin");
    }
    let (Some(p), Some(c), Some(q)) = (read(&public), read(&a["claim"]), read(&PathBuf::from(&a["proof"]))) else {
        eprintln!("error: unreadable or oversized input");
        return ExitCode::from(1);
    };
    let Some(prog) = decode(IMAGE) else {
        eprintln!("error: embedded image does not decode");
        return ExitCode::from(2);
    };
    let (o, s) = run_full(&prog, &Inputs { public: &p, claim: &c, proof: &q }, FUEL, false);
    eprintln!("npai: {} (fuel used {})", o.as_str(), FUEL - s.fuel);
    ExitCode::from(if o == Outcome::Accept { 0 } else { 1 })
}
