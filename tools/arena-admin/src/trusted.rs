//! Frozen trusted trees: publish (`arena-admin freeze-trusted`) and the
//! registration gate shared by `arena-admin check-trusted` and the server.
//!
//! A challenge's `semantic_scope.formal_spec.tree_digest` names the exact
//! `formal-core/` + `spec/lean/` sources its admissions are judged against
//! (`arena_types::trusted_tree`). `freeze` extracts those two roots from a
//! git commit (git-tracked content only, never a working tree), recomputes
//! the digest from the extracted files, requires it to equal every expected
//! pin, and publishes the result read-only as `<store>/<hex>/`.

use anyhow::{bail, Context, Result};
use arena_types::challenge::Tier;
use arena_types::trusted_tree::{self, TRUSTED_ROOTS};
use arena_types::{ChallengeDefinition, Digest};
use std::path::{Path, PathBuf};
use std::process::Command;

pub const MANIFEST_SCHEMA: &str = "arena-trusted-tree-v1";

/// Challenges whose admissions depend on a judge reference build must have
/// their pinned trusted tree published before they are registered. Demo
/// challenges never yield an admission (and pin demo-local trees).
pub fn required(def: &ChallengeDefinition) -> bool {
    def.tier != Tier::Demo
}

/// The registration gate: `Ok(None)` when not required (demo tier),
/// `Ok(Some(dir))` when the pinned tree is in `store` and hashes to the pin.
pub fn check_available(store: &Path, def: &ChallengeDefinition) -> Result<Option<PathBuf>> {
    if !required(def) {
        return Ok(None);
    }
    let pin = &def.semantic_scope.formal_spec.tree_digest;
    let dir = trusted_tree::check(store, pin)
        .with_context(|| format!("challenge {:?} pins trusted tree {pin}", def.name))?;
    Ok(Some(dir))
}

fn git(repo: &Path, args: &[&str]) -> Result<Vec<u8>> {
    let out = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .context("running git")?;
    if !out.status.success() {
        bail!(
            "git {}: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(out.stdout)
}

#[derive(Debug)]
pub struct Frozen {
    pub digest: Digest,
    pub dir: PathBuf,
    pub commit: String,
    /// The entry was already published (and re-verified).
    pub existed: bool,
}

#[cfg(unix)]
fn set_mode(p: &Path, mode: u32) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(p, std::fs::Permissions::from_mode(mode))
}
#[cfg(not(unix))]
fn set_mode(_: &Path, _: u32) -> std::io::Result<()> {
    Ok(())
}

/// Make a published tree read-only (files 0444/0555, dirs 0555).
fn seal(dir: &Path) -> std::io::Result<()> {
    for e in std::fs::read_dir(dir)? {
        let p = e?.path();
        let md = std::fs::symlink_metadata(&p)?;
        if md.is_dir() {
            seal(&p)?;
        } else {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let exec = md.permissions().mode() & 0o111 != 0;
                set_mode(&p, if exec { 0o555 } else { 0o444 })?;
            }
        }
    }
    set_mode(dir, 0o555)
}

/// Make a (partially sealed) staging tree removable again.
fn unseal(dir: &Path) {
    let _ = set_mode(dir, 0o755);
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() && !p.is_symlink() {
                unseal(&p);
            }
        }
    }
}

/// Extract `formal-core/` + `spec/lean/` of `commit` into `store`, verify the
/// digest against every `expect`ed pin, publish as `<store>/<hex>/`.
pub fn freeze(repo: &Path, commit: &str, store: &Path, expect: &[Digest]) -> Result<Frozen> {
    let sha = String::from_utf8(git(
        repo,
        &["rev-parse", "--verify", &format!("{commit}^{{commit}}")],
    )?)?
    .trim()
    .to_string();
    let mut args = vec!["ls-tree", "-r", "-z", "--full-tree", sha.as_str(), "--"];
    args.extend(TRUSTED_ROOTS);
    let listing = git(repo, &args)?;
    std::fs::create_dir_all(store).with_context(|| store.display().to_string())?;
    let stage = store.join(format!(
        ".staging-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let res = (|| -> Result<Frozen> {
        std::fs::create_dir(&stage)?;
        let mut n = 0usize;
        for rec in listing.split(|b| *b == 0).filter(|r| !r.is_empty()) {
            let rec = std::str::from_utf8(rec).context("non-UTF-8 path in the trusted tree")?;
            let (meta, path) = rec
                .split_once('\t')
                .with_context(|| format!("bad ls-tree record {rec:?}"))?;
            let f: Vec<&str> = meta.split(' ').collect();
            let [mode, kind, obj] = f[..] else {
                bail!("bad ls-tree record {rec:?}");
            };
            if kind != "blob" || !(mode == "100644" || mode == "100755") {
                bail!("unsupported entry {path} (mode {mode}, {kind}): trusted trees hold regular files only");
            }
            if path
                .split('/')
                .any(|s| s.is_empty() || s == "." || s == "..")
            {
                bail!("unsafe path {path:?}");
            }
            let body = git(repo, &["cat-file", "blob", obj])?;
            let to = stage.join(path);
            std::fs::create_dir_all(to.parent().expect("has parent"))?;
            std::fs::write(&to, body)?;
            set_mode(&to, if mode == "100755" { 0o755 } else { 0o644 })?;
            n += 1;
        }
        for r in TRUSTED_ROOTS {
            if !stage.join(r).is_dir() {
                bail!("commit {sha} has no tracked files under {r}/");
            }
        }
        let digest = trusted_tree::digest_of(&stage)?;
        for want in expect {
            if want != &digest {
                bail!(
                    "commit {sha}: formal-core + spec/lean hash to {digest}, not the pinned {want} \
                     (wrong commit for this challenge)"
                );
            }
        }
        let dir = trusted_tree::entry_dir(store, &digest);
        if dir.exists() {
            // Already published: it must still be exactly this tree.
            trusted_tree::check(store, &digest).with_context(|| {
                format!(
                    "{} exists but does not verify; remove it (chmod -R u+w) and freeze again",
                    dir.display()
                )
            })?;
            unseal(&stage);
            std::fs::remove_dir_all(&stage)?;
            return Ok(Frozen {
                digest,
                dir,
                commit: sha.clone(),
                existed: true,
            });
        }
        seal(&stage)?;
        std::fs::rename(&stage, &dir)?;
        // Re-verify what is now published.
        trusted_tree::check(store, &digest)?;
        let manifest = serde_json::json!({
            "schema": MANIFEST_SCHEMA,
            "tree_digest": digest,
            "commit": sha,
            "roots": TRUSTED_ROOTS,
            "files": n,
        });
        std::fs::write(
            store.join(format!("{}.json", digest.hex())),
            serde_json::to_vec_pretty(&manifest)?,
        )?;
        Ok(Frozen {
            digest,
            dir,
            commit: sha.clone(),
            existed: false,
        })
    })();
    if stage.exists() {
        unseal(&stage);
        let _ = std::fs::remove_dir_all(&stage);
    }
    res
}
