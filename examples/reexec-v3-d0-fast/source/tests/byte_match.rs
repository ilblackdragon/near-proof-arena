//! Gate of the PROVER-ONLY child: on every public positive case of
//! `near-chunk-validation-d0` (`oracle/fixtures/v3/arena-public/cases`), the native
//! `prove` must write a `proof.bin` byte-identical to the parent's Lean prover
//! (`examples/reexec-v3-d0`, `ReexecV3D0.normSW`). `lean-prover.sha256` holds the
//! sha256 of the Lean prover's proof per case; regenerate (and re-check against a fresh
//! build of the parent) with `tools/byte-match.sh --regen`.
//!
//! Skipped (with a message) when the repo fixtures are not next to the package, e.g. in
//! the judge's isolated build.

use std::path::PathBuf;
use std::process::Command;

fn sha256_hex(path: &std::path::Path) -> String {
    let out = Command::new("sha256sum").arg(path).output().expect("sha256sum");
    String::from_utf8(out.stdout).unwrap()[..64].to_string()
}

#[test]
fn proofs_byte_match_the_lean_prover_on_every_public_positive() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases = manifest.join("../../../oracle/fixtures/v3/arena-public/cases");
    if !cases.is_dir() {
        eprintln!("SKIP: no fixtures at {}", cases.display());
        return;
    }
    let expected = std::fs::read_to_string(manifest.join("tests/lean-prover.sha256")).unwrap();
    let mut n = 0;
    let mut seen = std::collections::BTreeSet::new();
    let tmp = std::env::temp_dir().join(format!("v3-d0-fast-bytematch-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    for line in expected.lines() {
        let (hash, case) = line.split_once("  ").unwrap();
        seen.insert(case.to_string());
        let d = cases.join(case);
        let st = Command::new(env!("CARGO_BIN_EXE_prove"))
            .args(["--public", tmp.to_str().unwrap()])
            .arg("--request")
            .arg(d.join("request.bin"))
            .arg("--witness")
            .arg(d.join("witness.bin"))
            .arg("--claim-out")
            .arg(tmp.join("claim.bin"))
            .arg("--proof-out")
            .arg(tmp.join("proof.bin"))
            .status()
            .unwrap();
        assert!(st.success(), "{case}: prove refused");
        assert_eq!(sha256_hex(&tmp.join("proof.bin")), hash, "{case}: proof differs from the Lean prover");
        assert_eq!(
            std::fs::read(tmp.join("claim.bin")).unwrap(),
            std::fs::read(d.join("expected_claim.bin")).unwrap(),
            "{case}: claim"
        );
        n += 1;
    }
    // the manifest covers the full positive set
    let all: std::collections::BTreeSet<String> = std::fs::read_dir(&cases)
        .unwrap()
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    assert_eq!(seen, all, "manifest does not cover exactly the public positive set");
    assert!(n >= 78, "{n} cases");
    let _ = std::fs::remove_dir_all(&tmp);
}
