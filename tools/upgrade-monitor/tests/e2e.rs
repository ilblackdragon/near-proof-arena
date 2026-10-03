//! End-to-end: synthetic git repo with a tiny cargo workspace.

use std::fs;
use std::path::Path;
use std::process::Command;

fn sh(dir: &Path, args: &[&str]) {
    let st = Command::new(args[0])
        .args(&args[1..])
        .current_dir(dir)
        .output()
        .unwrap();
    assert!(
        st.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&st.stderr)
    );
}

fn krate(root: &Path, name: &str, deps: &[&str]) {
    let d = root.join(name);
    fs::create_dir_all(d.join("src")).unwrap();
    let deps: String = deps
        .iter()
        .map(|x| format!("{x} = {{ path = \"../{x}\" }}\n"))
        .collect();
    fs::write(
        d.join("Cargo.toml"),
        format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n[dependencies]\n{deps}"),
    )
    .unwrap();
    fs::write(d.join("src/lib.rs"), "pub fn f() {}\n").unwrap();
}

const MAP: &str = r#"
schema = "arena-impact-map-v1"
[default]
spec_definitions = ["*"]
obligations = ["FORMAL_SEMANTIC_SOUNDNESS"]
fixtures = ["*"]
[[rule]]
id = "b"
paths = ["b/**"]
spec_definitions = ["concept:b"]
obligations = ["CONFORMANCE_DIFFERENTIAL"]
fixtures = []
"#;

fn setup() -> tempfile::TempDir {
    let t = tempfile::tempdir().unwrap();
    let r = t.path().join("repo");
    fs::create_dir_all(&r).unwrap();
    fs::write(
        r.join("Cargo.toml"),
        "[workspace]\nresolver = \"2\"\nmembers = [\"a\", \"b\", \"c\"]\n",
    )
    .unwrap();
    // `a` is the root, depends on `b`; `c` is unrelated.
    krate(&r, "a", &["b"]);
    krate(&r, "b", &[]);
    krate(&r, "c", &[]);
    fs::write(r.join("Cargo.lock"), "version = 4\n[[package]]\nname = \"a\"\nversion = \"0.1.0\"\ndependencies = [\"b\"]\n[[package]]\nname = \"b\"\nversion = \"0.1.0\"\n[[package]]\nname = \"c\"\nversion = \"0.1.0\"\n").unwrap();
    fs::write(t.path().join("map.toml"), MAP).unwrap();
    // Minimal protocol facts (the monitor fails closed if these are absent).
    fs::create_dir_all(r.join("core/primitives-core/src")).unwrap();
    fs::write(
        r.join("core/primitives-core/src/version.rs"),
        "pub enum ProtocolFeature { X, }\nimpl ProtocolFeature { pub const fn protocol_version(self) -> u32 { match self { ProtocolFeature::X => 1, } } pub const fn enabled(&self) {} }\npub const MIN_SUPPORTED_PROTOCOL_VERSION: u32 = 1;\nconst STABLE_PROTOCOL_VERSION: u32 = 1;\n",
    )
    .unwrap();
    fs::create_dir_all(r.join("core/store/src/db")).unwrap();
    fs::write(
        r.join("core/store/src/db/metadata.rs"),
        "pub const DB_VERSION: u32 = 1;\n",
    )
    .unwrap();
    sh(&r, &["git", "init", "-q"]);
    sh(&r, &["git", "add", "."]);
    sh(
        &r,
        &[
            "git",
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "-qm",
            "v1",
        ],
    );
    sh(&r, &["git", "tag", "v1"]);
    t
}

fn run(t: &Path) -> (i32, serde_json::Value) {
    let out = t.join("r.json");
    let st = Command::new(env!("CARGO_BIN_EXE_upgrade-monitor"))
        .args([
            "--repo",
            t.join("repo").to_str().unwrap(),
            "--old",
            "v1",
            "--new",
            "HEAD",
            "--roots",
            "a",
        ])
        .args([
            "--impact-map",
            t.join("map.toml").to_str().unwrap(),
            "--json",
            out.to_str().unwrap(),
        ])
        .args(["--scratch", t.to_str().unwrap()])
        .output()
        .unwrap();
    let code = st.status.code().unwrap();
    let v = if out.exists() {
        serde_json::from_str(&fs::read_to_string(out).unwrap()).unwrap()
    } else {
        serde_json::Value::Null
    };
    (code, v)
}

fn commit(t: &Path, file: &str) {
    let r = t.join("repo");
    fs::write(r.join(file), "pub fn g() {}\n").unwrap();
    sh(&r, &["git", "add", "."]);
    sh(
        &r,
        &[
            "git",
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "-qm",
            "v2",
        ],
    );
}

#[test]
fn change_outside_closure_is_clean() {
    let t = setup();
    commit(t.path(), "c/src/lib.rs");
    let (code, v) = run(t.path());
    assert_eq!(code, 0, "{v:#}");
    assert_eq!(v["old"]["stable_protocol_version"], 1);
    assert_eq!(v["verdict"], "NO_SEMANTIC_CHANGE_DETECTED");
    // protocol facts are absent in this synthetic tree, but nothing changed => no diff reasons
    assert_eq!(v["changed_files_outside_closure"], 1);
}

#[test]
fn change_in_transitive_dep_requires_revalidation() {
    let t = setup();
    commit(t.path(), "b/src/lib.rs");
    let (code, v) = run(t.path());
    assert_eq!(code, 3, "{v:#}");
    assert_eq!(v["verdict"], "REVALIDATION_REQUIRED");
    assert_eq!(v["changed_in_closure"][0]["crate_name"], "b");
    assert_eq!(v["impact"]["rule_hits"][0]["rule"], "b");
    assert!(v["impact"]["unmapped_files"].as_array().unwrap().is_empty());
}

#[test]
fn unknown_ref_is_an_error_not_clean() {
    let t = setup();
    let st = Command::new(env!("CARGO_BIN_EXE_upgrade-monitor"))
        .args([
            "--repo",
            t.path().join("repo").to_str().unwrap(),
            "--old",
            "v1",
            "--new",
            "nope",
        ])
        .args(["--impact-map", t.path().join("map.toml").to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(st.status.code(), Some(2));
}

#[test]
fn missing_protocol_facts_fail_closed() {
    let t = setup();
    let r = t.path().join("repo");
    fs::remove_file(r.join("core/primitives-core/src/version.rs")).unwrap();
    sh(&r, &["git", "add", "-A"]);
    sh(
        &r,
        &[
            "git",
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "-qm",
            "v2",
        ],
    );
    let (code, v) = run(t.path());
    assert_eq!(code, 3, "{v:#}");
}
