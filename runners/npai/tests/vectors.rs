//! Every case of the committed Lean vector suite
//! (`formal-core/vectors/npai-v1.json`, produced by `arena-interp-ref
//! vectors`) must give byte-identical results in the Rust interpreter, and
//! `npai-verify` must map each outcome to the CONTRACTS §4 exit code.

use arena_npai::interp::{self, Inputs};
use arena_npai::report::{expect_json, from_hex};
use std::path::PathBuf;
use std::process::Command;

fn suite() -> Vec<serde_json::Value> {
    let p =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../formal-core/vectors/npai-v1.json");
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(p).unwrap()).unwrap();
    assert_eq!(v["format"], "npai-v1-vectors");
    v["cases"].as_array().unwrap().clone()
}

fn hex(c: &serde_json::Value, k: &str) -> Vec<u8> {
    from_hex(c[k].as_str().unwrap()).unwrap()
}

#[test]
fn lean_vectors_match_byte_for_byte() {
    let cases = suite();
    assert!(
        cases.len() >= 40,
        "vector suite unexpectedly small: {}",
        cases.len()
    );
    for c in &cases {
        let (image, public, claim, proof) = (
            hex(c, "code"),
            hex(c, "public"),
            hex(c, "claim"),
            hex(c, "proof"),
        );
        let fuel = c["fuel"].as_u64().unwrap();
        let got = expect_json(&interp::expect(
            &image,
            &Inputs {
                public: &public,
                claim: &claim,
                proof: &proof,
            },
            fuel,
        ));
        let want = serde_json::to_string(&c["expect"]).unwrap();
        assert_eq!(got, want, "vector {}", c["name"]);
    }
}

#[test]
fn encode_inverts_decode_on_valid_vectors() {
    for c in suite() {
        let image = hex(&c, "code");
        if let Some(p) = interp::decode(&image) {
            assert_eq!(interp::encode(&p), image, "vector {}", c["name"]);
        }
    }
}

#[test]
fn npai_verify_exit_codes() {
    let dir = std::env::temp_dir().join(format!("npai-verify-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for c in suite() {
        let name = c["name"].as_str().unwrap();
        let files: Vec<PathBuf> = ["code", "public", "claim", "proof"]
            .iter()
            .map(|k| {
                let f = dir.join(format!("{name}.{k}"));
                std::fs::write(&f, hex(&c, k)).unwrap();
                f
            })
            .collect();
        let out = Command::new(env!("CARGO_BIN_EXE_npai-verify"))
            .arg("--image")
            .arg(&files[0])
            .arg("--public")
            .arg(&files[1])
            .arg("--claim")
            .arg(&files[2])
            .arg("--proof")
            .arg(&files[3])
            .arg("--fuel")
            .arg(c["fuel"].as_u64().unwrap().to_string())
            .output()
            .unwrap();
        let want = if c["expect"]["outcome"] == "accept" {
            0
        } else {
            1
        };
        assert_eq!(
            out.status.code(),
            Some(want),
            "vector {name}: {}",
            String::from_utf8_lossy(&out.stdout)
        );
        let diag = String::from_utf8(out.stdout).unwrap();
        assert!(
            diag.contains(&format!(
                "\"outcome\":\"{}\"",
                c["expect"]["outcome"].as_str().unwrap()
            )),
            "{name}: {diag}"
        );
    }
    // Digest binding and I/O errors.
    let img = dir.join("halt_reject.code");
    let e = dir.join("halt_reject.public");
    let run = |extra: &[&str]| {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_npai-verify"));
        cmd.arg("--image")
            .arg(&img)
            .arg("--public")
            .arg(&e)
            .arg("--claim")
            .arg(&e)
            .arg("--proof")
            .arg(&e)
            .arg("--fuel")
            .arg("10");
        cmd.args(extra);
        cmd.output().unwrap().status.code()
    };
    assert_eq!(run(&[]), Some(1));
    assert_eq!(run(&["--expect-digest", &"00".repeat(32)]), Some(3));
    let d = arena_npai::report::to_hex(&<sha2::Sha256 as sha2::Digest>::digest(
        std::fs::read(&img).unwrap(),
    ));
    assert_eq!(run(&["--expect-digest", &d]), Some(1));
    let missing = Command::new(env!("CARGO_BIN_EXE_npai-verify"))
        .args([
            "--image",
            "/nonexistent",
            "--public",
            "/x",
            "--claim",
            "/x",
            "--proof",
            "/x",
            "--fuel",
            "1",
        ])
        .output()
        .unwrap();
    assert_eq!(missing.status.code(), Some(2));
    std::fs::remove_dir_all(&dir).ok();
}
