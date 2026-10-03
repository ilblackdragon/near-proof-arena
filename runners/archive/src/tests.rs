//! Hostile-archive fixtures (generated in-test) and property tests.

use super::*;
use proptest::prelude::*;
use std::collections::BTreeMap;
use std::os::unix::fs::PermissionsExt;

// ---------- raw tar crafting (bypasses tar::Builder's own path checks) ----

fn octal(field: &mut [u8], v: u64) {
    let s = format!("{:0width$o}", v, width = field.len() - 1);
    field[..s.len()].copy_from_slice(s.as_bytes());
    field[s.len()] = 0;
}

/// One ustar header + data. `name` may be up to 100 bytes (no prefix use).
fn raw_entry(name: &[u8], typeflag: u8, mode: u32, data: &[u8], link: &[u8]) -> Vec<u8> {
    assert!(name.len() <= 100);
    let mut h = [0u8; 512];
    h[..name.len()].copy_from_slice(name);
    octal(&mut h[100..108], mode as u64);
    octal(&mut h[108..116], 0);
    octal(&mut h[116..124], 0);
    octal(&mut h[124..136], data.len() as u64);
    octal(&mut h[136..148], 0);
    h[156] = typeflag;
    h[157..157 + link.len()].copy_from_slice(link);
    h[257..263].copy_from_slice(b"ustar\0");
    h[263..265].copy_from_slice(b"00");
    h[148..156].copy_from_slice(b"        ");
    let sum: u32 = h.iter().map(|&b| b as u32).sum();
    let s = format!("{:06o}\0 ", sum);
    h[148..156].copy_from_slice(s.as_bytes());
    let mut out = h.to_vec();
    out.extend_from_slice(data);
    let pad = (512 - data.len() % 512) % 512;
    out.extend(std::iter::repeat_n(0u8, pad));
    out
}

fn finish(mut v: Vec<u8>) -> Vec<u8> {
    v.extend(std::iter::repeat_n(0u8, 1024));
    v
}

fn file(name: &str, data: &[u8]) -> Vec<u8> {
    raw_entry(name.as_bytes(), b'0', 0o644, data, b"")
}

fn tar_of(entries: &[Vec<u8>]) -> Vec<u8> {
    finish(entries.concat())
}

fn zst(b: &[u8]) -> Vec<u8> {
    zstd::encode_all(b, 3).unwrap()
}

struct Tmp(tempfile::TempDir);
impl Tmp {
    fn new() -> Self {
        Tmp(tempfile::tempdir().unwrap())
    }
    fn dest(&self) -> PathBuf {
        self.0.path().join("x")
    }
}

fn expect_unsafe(bytes: &[u8], limits: &Limits, needle: &str) {
    let t = Tmp::new();
    match ingest_bytes(bytes, &t.dest(), limits) {
        Err(ArchiveError::Unsafe(m)) => assert!(m.contains(needle), "expected {needle:?} in {m:?}"),
        Err(e) => panic!("expected Unsafe({needle}), got {e:?}"),
        Ok(x) => panic!("expected rejection ({needle}), got tree {:?}", x.tree),
    }
    assert!(!t.dest().exists(), "destination must be removed on error");
}

// ---------- happy path ----------

fn sample_pkg() -> Vec<u8> {
    tar_of(&[
        raw_entry(b"./", b'5', 0o755, b"", b""),
        file("./candidate.toml", b"x"),
        raw_entry(b"./bin/", b'5', 0o755, b"", b""),
        raw_entry(b"./bin/run", b'0', 0o755, b"#!/bin/sh\n", b""),
        file("./src/a.rs", b"fn main() {}"),
    ])
}

#[test]
fn extracts_tar_and_zstd_identically() {
    let t = Tmp::new();
    let a = ingest_bytes(&sample_pkg(), &t.dest(), &Limits::default()).unwrap();
    assert_eq!(a.compression, Compression::None);
    let t2 = Tmp::new();
    let b = ingest_bytes(&zst(&sample_pkg()), &t2.dest(), &Limits::default()).unwrap();
    assert_eq!(b.compression, Compression::Zstd);
    assert_eq!(a.digest, b.digest);
    assert!(a.tree.is_exec("bin/run"));
    assert!(!a.tree.is_exec("src/a.rs"));
    assert!(a.tree.is_dir("src"));
    let m = fs::metadata(t.dest().join("bin/run")).unwrap();
    assert_eq!(m.permissions().mode() & 0o777, 0o755);
    let m = fs::metadata(t.dest().join("src/a.rs")).unwrap();
    assert_eq!(m.permissions().mode() & 0o777, 0o644);
    assert_eq!(fs::read(t.dest().join("src/a.rs")).unwrap(), b"fn main() {}");
    // Digest of the on-disk tree equals the streaming digest.
    assert_eq!(tree_from_dir(&t.dest(), &Limits::default()).unwrap(), a.tree);
}

#[test]
fn tree_digest_known_vector() {
    // [["a","file","sha256:<sha256('')>"],["b/c","exec","sha256:<sha256('x')>"]]
    let t = Tmp::new();
    let x = ingest_bytes(
        &tar_of(&[file("a", b""), raw_entry(b"b/c", b'0', 0o700, b"x", b"")]),
        &t.dest(),
        &Limits::default(),
    )
    .unwrap();
    let json = format!(
        r#"[["a","file","{}"],["b/c","exec","{}"]]"#,
        arena_types::Digest::of_bytes(b""),
        arena_types::Digest::of_bytes(b"x")
    );
    assert_eq!(x.digest, arena_types::Digest::of_bytes(json.as_bytes()));
    // Empty dirs don't change the digest.
    let t2 = Tmp::new();
    let y = ingest_bytes(
        &tar_of(&[raw_entry(b"zz/", b'5', 0o755, b"", b""), file("a", b""), raw_entry(b"b/c", b'0', 0o755, b"x", b"")]),
        &t2.dest(),
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(x.digest, y.digest);
}

#[test]
fn global_pax_header_is_ignored() {
    let t = Tmp::new();
    let x = ingest_bytes(
        &tar_of(&[raw_entry(b"pax_global_header", b'g', 0o644, b"52 comment=0000000000000000000000000000000000000000\n", b""), file("a", b"1")]),
        &t.dest(),
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(x.tree.files.len(), 1);
}

#[test]
fn pack_roundtrip_is_deterministic() {
    let t = Tmp::new();
    let a = ingest_bytes(&sample_pkg(), &t.dest(), &Limits::default()).unwrap();
    let p1 = pack_tree(&t.dest(), &a.tree, Vec::new()).unwrap();
    let p2 = pack_tree(&t.dest(), &a.tree, Vec::new()).unwrap();
    assert_eq!(p1, p2);
    let t2 = Tmp::new();
    let b = ingest_bytes(&p1, &t2.dest(), &Limits::default()).unwrap();
    assert_eq!(a.tree, b.tree);
}

#[test]
fn dest_must_be_fresh() {
    let t = Tmp::new();
    fs::create_dir(t.dest()).unwrap();
    assert!(matches!(ingest_bytes(&sample_pkg(), &t.dest(), &Limits::default()), Err(ArchiveError::Io(_))));
}

// ---------- hostile fixtures ----------

#[test]
fn rejects_symlink() {
    expect_unsafe(&tar_of(&[raw_entry(b"evil", b'2', 0o777, b"", b"/etc/passwd")]), &Limits::default(), "symlink");
}

#[test]
fn rejects_hardlink() {
    expect_unsafe(&tar_of(&[file("a", b"1"), raw_entry(b"b", b'1', 0o644, b"", b"a")]), &Limits::default(), "hardlink");
}

#[test]
fn rejects_devices_and_fifos() {
    expect_unsafe(&tar_of(&[raw_entry(b"c", b'3', 0o644, b"", b"")]), &Limits::default(), "device");
    expect_unsafe(&tar_of(&[raw_entry(b"b", b'4', 0o644, b"", b"")]), &Limits::default(), "device");
    expect_unsafe(&tar_of(&[raw_entry(b"f", b'6', 0o644, b"", b"")]), &Limits::default(), "fifo");
    expect_unsafe(&tar_of(&[raw_entry(b"s", b'S', 0o644, b"", b"")]), &Limits::default(), "sparse");
}

#[test]
fn rejects_absolute_and_traversal() {
    expect_unsafe(&tar_of(&[file("/etc/x", b"1")]), &Limits::default(), "absolute");
    expect_unsafe(&tar_of(&[file("../x", b"1")]), &Limits::default(), "dot component");
    expect_unsafe(&tar_of(&[file("a/../../x", b"1")]), &Limits::default(), "dot component");
    expect_unsafe(&tar_of(&[file("a//x", b"1")]), &Limits::default(), "empty path component");
    expect_unsafe(&tar_of(&[raw_entry(b"a\\..\\x", b'0', 0o644, b"1", b"")]), &Limits::default(), "forbidden character");
}

#[test]
fn rejects_non_utf8_and_long_paths() {
    expect_unsafe(&tar_of(&[raw_entry(b"bad\xff\xfe", b'0', 0o644, b"1", b"")]), &Limits::default(), "UTF-8");
    // GNU long name (> 255 bytes) through the tar crate's builder.
    let mut b = tar::Builder::new(Vec::new());
    let mut h = tar::Header::new_gnu();
    h.set_size(1);
    h.set_mode(0o644);
    let long = format!("{}/f", "d".repeat(300));
    b.append_data(&mut h, &long, &b"1"[..]).unwrap();
    expect_unsafe(&b.into_inner().unwrap(), &Limits::default(), "longer than 255");
    // PAX path record that smuggles a traversal.
    let rec = b"19 path=../../evil\n";
    let pax = tar_of(&[raw_entry(b"PaxHeaders/x", b'x', 0o644, rec, b""), file("innocent", b"1")]);
    expect_unsafe(&pax, &Limits::default(), "dot component");
}

#[test]
fn rejects_duplicates_and_collisions() {
    expect_unsafe(&tar_of(&[file("a", b"1"), file("a", b"2")]), &Limits::default(), "duplicate");
    expect_unsafe(&tar_of(&[file("a", b"1"), file("./a", b"2")]), &Limits::default(), "duplicate");
    expect_unsafe(&tar_of(&[file("README.md", b"1"), file("readme.md", b"2")]), &Limits::default(), "collision");
    expect_unsafe(&tar_of(&[file("Dir/a", b"1"), file("dir/b", b"2")]), &Limits::default(), "collision");
    expect_unsafe(&tar_of(&[file("caf\u{e9}", b"1"), file("cafe\u{301}", b"2")]), &Limits::default(), "collision");
    expect_unsafe(&tar_of(&[file("a", b"1"), file("a/b", b"2")]), &Limits::default(), "beneath file");
    expect_unsafe(&tar_of(&[file("a/b", b"1"), file("a", b"2")]), &Limits::default(), "conflicts with directory");
    expect_unsafe(&tar_of(&[raw_entry(b"d/", b'5', 0o755, b"", b""), raw_entry(b"d/", b'5', 0o755, b"", b"")]), &Limits::default(), "duplicate");
}

#[test]
fn rejects_setuid_setgid_sticky() {
    expect_unsafe(&tar_of(&[raw_entry(b"x", b'0', 0o4755, b"1", b"")]), &Limits::default(), "setuid");
    expect_unsafe(&tar_of(&[raw_entry(b"x", b'0', 0o2755, b"1", b"")]), &Limits::default(), "setuid");
    expect_unsafe(&tar_of(&[raw_entry(b"d/", b'5', 0o1777, b"", b"")]), &Limits::default(), "sticky");
}

#[test]
fn rejects_too_many_entries() {
    let entries: Vec<Vec<u8>> = (0..11).map(|i| file(&format!("f{i}"), b"")).collect();
    let limits = Limits { max_entries: 10, ..Limits::default() };
    expect_unsafe(&tar_of(&entries), &limits, "more than 10 entries");
}

#[test]
fn rejects_expanded_size() {
    let limits = Limits { max_expanded_bytes: 1000, ..Limits::default() };
    expect_unsafe(&tar_of(&[file("a", &[1u8; 600]), file("b", &[2u8; 600])]), &limits, "expanded size");
    // Header lies about size: claims 10 GiB with no data.
    let mut e = file("big", b"");
    octal(&mut e[124..136], (1 << 33) - 1);
    let sum_fix = {
        e[148..156].copy_from_slice(b"        ");
        let s: u32 = e[..512].iter().map(|&b| b as u32).sum();
        format!("{:06o}\0 ", s)
    };
    e[148..156].copy_from_slice(sum_fix.as_bytes());
    expect_unsafe(&tar_of(&[e]), &Limits::default(), "expanded size");
}

#[test]
fn rejects_compression_bomb_early() {
    // 1 GiB of zeros compresses to ~32 KiB with zstd: ratio >> 200. We feed
    // it through a reader that counts how much of the compressed stream was
    // consumed when the ingester gave up.
    let mut h = tar::Header::new_gnu();
    h.set_size(1 << 30);
    h.set_mode(0o644);
    h.set_path("zeros").unwrap();
    h.set_cksum();
    let mut enc = zstd::stream::write::Encoder::new(Vec::new(), 19).unwrap();
    enc.write_all(h.as_bytes()).unwrap();
    let chunk = vec![0u8; 1 << 20];
    for _ in 0..1024 {
        enc.write_all(&chunk).unwrap();
    }
    enc.write_all(&[0u8; 1024]).unwrap();
    let bomb = enc.finish().unwrap();
    assert!(bomb.len() < 1 << 20, "bomb is {} bytes", bomb.len());
    let t = Tmp::new();
    let r = ingest_bytes(&bomb, &t.dest(), &Limits::default());
    match r {
        Err(ArchiveError::Unsafe(m)) => assert!(m.contains("compression ratio"), "{m}"),
        other => panic!("expected ratio rejection, got {other:?}"),
    }
    assert!(!t.dest().exists());
}

#[test]
fn rejects_compressed_size_limit() {
    let limits = Limits { max_compressed_bytes: 1024, ..Limits::default() };
    expect_unsafe(&tar_of(&[file("a", &[7u8; 4096])]), &limits, "compressed size limit");
    // Streaming path (no up-front length check).
    let t = Tmp::new();
    let data = tar_of(&[file("a", &[7u8; 4096])]);
    assert!(matches!(ingest(&data[..], &t.dest(), &limits), Err(ArchiveError::Unsafe(_))));
}

#[test]
fn rejects_truncated_archive() {
    let full = tar_of(&[file("a", &[1u8; 2000])]);
    expect_unsafe(&full[..900], &Limits::default(), "");
    let z = zst(&full);
    expect_unsafe(&z[..z.len() / 2], &Limits::default(), "");
}

#[test]
fn rejects_file_for_root() {
    expect_unsafe(&tar_of(&[file("./", b"1")]), &Limits::default(), "archive root");
}

#[test]
fn tree_from_dir_rejects_symlinks_and_hardlinks() {
    let t = Tmp::new();
    let d = t.0.path().join("d");
    fs::create_dir(&d).unwrap();
    fs::write(d.join("a"), b"1").unwrap();
    std::os::unix::fs::symlink("/etc/passwd", d.join("l")).unwrap();
    assert!(tree_from_dir(&d, &Limits::default()).unwrap_err().is_unsafe());
    fs::remove_file(d.join("l")).unwrap();
    fs::hard_link(d.join("a"), d.join("h")).unwrap();
    assert!(tree_from_dir(&d, &Limits::default()).unwrap_err().is_unsafe());
    fs::remove_file(d.join("h")).unwrap();
    assert_eq!(tree_from_dir(&d, &Limits::default()).unwrap().files.len(), 1);
}

// ---------- property tests ----------

fn arb_component() -> impl Strategy<Value = String> {
    "[a-zA-Z0-9_][a-zA-Z0-9_.-]{0,11}".prop_filter("no dot names", |s| s != "." && s != "..")
}

fn arb_tree() -> impl Strategy<Value = BTreeMap<String, (bool, Vec<u8>)>> {
    prop::collection::btree_map(
        prop::collection::vec(arb_component(), 1..4).prop_map(|v| v.join("/")),
        (any::<bool>(), prop::collection::vec(any::<u8>(), 0..300)),
        0..20,
    )
}

/// Build a tar with tar::Builder from a map, dropping entries that would
/// conflict (file-vs-dir, case collisions) so the input is valid.
fn valid_subset(m: BTreeMap<String, (bool, Vec<u8>)>) -> BTreeMap<String, (bool, Vec<u8>)> {
    let mut b = tree::TreeBuilder::default();
    let mut out = BTreeMap::new();
    for (k, v) in m {
        if b.add(&k, false).is_ok() {
            b.set_file(k.clone(), TreeFile { mode: FileMode::File, digest: arena_types::Digest::of_bytes(b""), size: 0 });
            out.insert(k, v);
        }
    }
    out
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, ..ProptestConfig::default() })]

    #[test]
    fn prop_roundtrip_digest_matches(m in arb_tree(), compress in any::<bool>()) {
        let m = valid_subset(m);
        let mut b = tar::Builder::new(Vec::new());
        for (k, (exec, data)) in &m {
            let mut h = tar::Header::new_gnu();
            h.set_size(data.len() as u64);
            h.set_mode(if *exec { 0o755 } else { 0o644 });
            b.append_data(&mut h, k, &data[..]).unwrap();
        }
        let bytes = b.into_inner().unwrap();
        let bytes = if compress { zst(&bytes) } else { bytes };
        let t = Tmp::new();
        let x = ingest_bytes(&bytes, &t.dest(), &Limits::default()).unwrap();
        prop_assert_eq!(x.tree.files.len(), m.len());
        for (k, (exec, data)) in &m {
            prop_assert_eq!(&fs::read(t.dest().join(k)).unwrap(), data);
            prop_assert_eq!(x.tree.is_exec(k), *exec);
        }
        let on_disk = tree_from_dir(&t.dest(), &Limits::default()).unwrap();
        prop_assert_eq!(on_disk.digest(), x.digest.clone());
        let packed = pack_tree(&t.dest(), &x.tree, Vec::new()).unwrap();
        let t2 = Tmp::new();
        let y = ingest_bytes(&packed, &t2.dest(), &Limits::default()).unwrap();
        prop_assert_eq!(y.digest, x.digest);
    }

    #[test]
    fn prop_normalize_never_escapes(raw in prop::collection::vec(any::<u8>(), 0..300)) {
        if let Ok(Some(p)) = path::normalize(&raw) {
            prop_assert!(!p.starts_with('/'));
            prop_assert!(p.len() <= 255);
            prop_assert!(p.split('/').all(|c| !c.is_empty() && c != "." && c != ".."));
            prop_assert!(!p.chars().any(|c| c.is_control()));
        }
    }

    #[test]
    fn prop_garbage_never_escapes(prefix in prop::collection::vec(any::<u8>(), 0..2048), zstd_wrap in any::<bool>()) {
        let bytes = if zstd_wrap { zst(&prefix) } else { prefix };
        let t = Tmp::new();
        let _ = ingest_bytes(&bytes, &t.dest(), &Limits::default());
        // Nothing but (possibly) the destination exists next to it.
        let names: Vec<_> = fs::read_dir(t.0.path()).unwrap().map(|e| e.unwrap().file_name()).collect();
        prop_assert!(names.iter().all(|n| n == "x"));
    }

    #[test]
    fn prop_mutated_headers_never_escape(m in arb_tree(), flips in prop::collection::vec((any::<prop::sample::Index>(), any::<u8>()), 1..8)) {
        let m = valid_subset(m);
        let mut b = tar::Builder::new(Vec::new());
        for (k, (_, data)) in &m {
            let mut h = tar::Header::new_gnu();
            h.set_size(data.len() as u64);
            h.set_mode(0o644);
            b.append_data(&mut h, k, &data[..]).unwrap();
        }
        let mut bytes = b.into_inner().unwrap();
        let n = bytes.len();
        for (i, v) in flips { bytes[i.index(n)] = v; }
        let t = Tmp::new();
        if let Ok(x) = ingest_bytes(&bytes, &t.dest(), &Limits::default()) {
            // Whatever was accepted is internally consistent.
            prop_assert_eq!(tree_from_dir(&t.dest(), &Limits::default()).unwrap(), x.tree);
        }
        let names: Vec<_> = fs::read_dir(t.0.path()).unwrap().map(|e| e.unwrap().file_name()).collect();
        prop_assert!(names.iter().all(|n| n == "x"));
    }
}

// ---------- package validation ----------

const MANIFEST: &str = r#"
schema = "arena-candidate-v1"
name = "toy"
agent = "a"
challenge = "chl_00"
backend_family = "toy"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 1 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
[formal]
lean_project = "formal"
certificate = "Candidate.certificate"
"#;

fn pkg_with(manifest: &str, tweak: impl FnOnce(&mut BTreeMap<String, (u32, Vec<u8>)>)) -> Result<arena_types::CandidateManifest, PackageError> {
    let mut m: BTreeMap<String, (u32, Vec<u8>)> = BTreeMap::new();
    m.insert("candidate.toml".into(), (0o644, manifest.as_bytes().to_vec()));
    m.insert("README.md".into(), (0o644, b"hi".to_vec()));
    m.insert("source/".into(), (0o755, vec![]));
    m.insert("dependency-locks/".into(), (0o755, vec![]));
    m.insert("formal/Candidate.lean".into(), (0o644, b"".to_vec()));
    m.insert("build-recipe/build.sh".into(), (0o755, b"#!/bin/sh\n".to_vec()));
    tweak(&mut m);
    let entries: Vec<Vec<u8>> = m
        .iter()
        .map(|(k, (mode, d))| raw_entry(k.as_bytes(), if k.ends_with('/') { b'5' } else { b'0' }, *mode, d, b""))
        .collect();
    let t = Tmp::new();
    let x = ingest_bytes(&tar_of(&entries), &t.dest(), &Limits::default()).unwrap();
    validate_package(&x.root, &x.tree)
}

#[test]
fn package_ok() {
    let m = pkg_with(MANIFEST, |_| {}).unwrap();
    assert_eq!(m.name, "toy");
}

#[test]
fn package_layout_violations() {
    let layout = |r: Result<_, PackageError>, needle: &str| match r {
        Err(PackageError::Layout(m)) | Err(PackageError::Manifest(m)) => assert!(m.contains(needle), "{needle:?} not in {m:?}"),
        other => panic!("expected layout error {needle:?}, got {other:?}"),
    };
    layout(pkg_with(MANIFEST, |m| { m.remove("README.md"); }), "README.md");
    layout(pkg_with(MANIFEST, |m| { m.remove("source/"); }), "source/");
    layout(pkg_with(MANIFEST, |m| { m.remove("formal/Candidate.lean"); }), "lean_project");
    layout(pkg_with(MANIFEST, |m| { m.get_mut("build-recipe/build.sh").unwrap().0 = 0o644; }), "not executable");
    layout(pkg_with(MANIFEST, |m| { m.remove("build-recipe/build.sh"); m.insert("build-recipe/".into(), (0o755, vec![])); }), "not a regular file");
    layout(pkg_with(MANIFEST, |m| { m.insert("out/prove".into(), (0o755, vec![])); }), "already present");
    layout(pkg_with(&MANIFEST.replace("prove = \"out/prove\"", "prove = \"source/prove\""), |_| {}), "entry.prove");
    layout(pkg_with(&MANIFEST.replace("outputs = [\"out\"]", "outputs = [\"out\", \"out/x\"]"), |_| {}), "nested");
    layout(pkg_with(&MANIFEST.replace("outputs = [\"out\"]", "outputs = []"), |_| {}), "build.outputs");
    layout(pkg_with(&MANIFEST.replace("recipe = \"build-recipe/build.sh\"", "recipe = \"source/build.sh\""), |m| { m.insert("source/build.sh".into(), (0o755, vec![])); }), "under build-recipe");
    layout(pkg_with("not toml", |_| {}), "");
    layout(pkg_with(&format!("security_bits = 128\n{MANIFEST}"), |_| {}), "unknown field");
    layout(pkg_with(MANIFEST, |m| { m.remove("candidate.toml"); }), "missing");
    layout(pkg_with(MANIFEST, |m| { m.insert("candidate.toml".into(), (0o644, vec![b' '; 70_000])); }), "larger");
}
