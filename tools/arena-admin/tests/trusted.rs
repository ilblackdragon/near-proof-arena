//! `freeze-trusted` / `check-trusted`: frozen trusted trees are published
//! only for the commit whose formal-core + spec/lean hash to the pin, and the
//! registration gate refuses a missing, tampered or wrong tree.

use arena_admin::challenge_file::load_definition;
use arena_admin::trusted::{check_available, freeze};
use arena_types::trusted_tree;
use arena_types::Digest;
use std::path::{Path, PathBuf};

/// The NEAR v1 family's freeze commit and pin.
const COMMIT: &str = "6873c9980fd93c0483e93b94fe7e8a1fe0d52d52";
const PIN: &str = "sha256:8090432a8236d8a8cacada10c257f83575f6c0ec480a40659d6af023ff39c611";

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn have_commit() -> bool {
    std::process::Command::new("git")
        .arg("-C")
        .arg(repo())
        .args(["cat-file", "-e", &format!("{COMMIT}^{{commit}}")])
        .status()
        .is_ok_and(|s| s.success())
}

fn make_writable(p: &Path) {
    let _ = std::process::Command::new("chmod")
        .args(["-R", "u+w"])
        .arg(p)
        .status();
}

#[test]
fn freeze_publishes_only_the_pinned_tree() {
    if !have_commit() {
        eprintln!("skipped: {COMMIT} not in this clone");
        return;
    }
    let tmp = tempfile::tempdir().unwrap();
    let store = tmp.path().join("store");
    let pin: Digest = PIN.to_string().try_into().unwrap();
    let chals: Vec<_> = [
        "chl_5ef2bc7d2068219635426e47ca46bfbb",
        "chl_f7eb2d91bf7b363eee134b6ad9d3e011",
        "chl_3be93793610370275ae40f36a475f01f",
        "chl_fefb6bc7596a6fb1a145062c864db947",
        "chl_b7c82396ad623f6dc21efab0f008ea4b",
    ]
    .iter()
    .map(|id| load_definition(&repo().join(format!("challenges/{id}.json"))).unwrap())
    .collect();
    for c in &chals {
        assert_eq!(c.semantic_scope.formal_spec.tree_digest, pin);
        // Not published yet: registration refused.
        assert!(check_available(&store, c).is_err());
    }

    // A commit whose tree differs from the pin is refused, nothing published.
    let head_tree = {
        let d = tmp.path().join("head");
        let f = freeze(&repo(), "HEAD", &d, &[]).unwrap();
        f.digest
    };
    if head_tree != pin {
        let e = freeze(&repo(), "HEAD", &store, std::slice::from_ref(&pin)).unwrap_err();
        assert!(format!("{e:#}").contains("not the pinned"), "{e:#}");
        assert!(!trusted_tree::entry_dir(&store, &pin).exists());
    }

    // The freeze commit reproduces the pin; every v1-family challenge then registers.
    let f = freeze(&repo(), COMMIT, &store, std::slice::from_ref(&pin)).unwrap();
    assert_eq!(f.digest, pin);
    assert!(!f.existed);
    for c in &chals {
        assert!(check_available(&store, c).unwrap().is_some());
    }
    // Idempotent (re-verified).
    assert!(
        freeze(&repo(), COMMIT, &store, std::slice::from_ref(&pin))
            .unwrap()
            .existed
    );
    // The demo challenge needs no trusted tree.
    let demo =
        load_definition(&repo().join("challenges/chl_54c65fe7c73c5abcfe500681889177bc.json"))
            .unwrap();
    assert!(check_available(&store, &demo).unwrap().is_none());

    // Tampered after publication: registration and re-freeze refuse it.
    let entry = trusted_tree::entry_dir(&store, &pin);
    make_writable(&entry);
    let p = entry.join("spec/lean/NearSpec/TransferV1.lean");
    let mut s = std::fs::read_to_string(&p).unwrap();
    s.push_str("\n-- tampered\n");
    std::fs::write(&p, s).unwrap();
    let e = check_available(&store, &chals[0]).unwrap_err();
    assert!(format!("{e:#}").contains("not the pinned"), "{e:#}");
    assert!(freeze(&repo(), COMMIT, &store, std::slice::from_ref(&pin)).is_err());
    make_writable(tmp.path());
}
