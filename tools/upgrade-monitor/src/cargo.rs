//! Dependency closure of the runtime crates.
//!
//! * Workspace closure: `cargo metadata --no-deps` (offline), following
//!   normal and build dependencies — including *optional* ones, since a
//!   feature may enable them (over-approximation is the fail-closed choice).
//!   Dev-dependencies are excluded: they do not reach production binaries.
//! * External closure: walk `Cargo.lock` starting from the closure crates'
//!   non-dev external dependencies.

use anyhow::{bail, Context, Result};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::Path;
use std::process::Command;

#[derive(Deserialize)]
struct Metadata {
    packages: Vec<Package>,
    workspace_root: String,
}

#[derive(Deserialize)]
struct Package {
    name: String,
    manifest_path: String,
    dependencies: Vec<Dep>,
}

#[derive(Deserialize)]
struct Dep {
    name: String,
    kind: Option<String>,
    path: Option<String>,
}

#[derive(Clone, Debug)]
pub struct WsCrate {
    /// Directory relative to the workspace root ("" for the root package).
    pub dir: String,
    /// Non-dev path dependencies (workspace crate names).
    pub path_deps: Vec<String>,
    /// Non-dev external dependency package names.
    pub ext_deps: Vec<String>,
}

#[derive(Debug, Default)]
pub struct Workspace {
    pub crates: BTreeMap<String, WsCrate>,
}

pub fn metadata(root: &Path, toolchain: Option<&str>) -> Result<Workspace> {
    let mut cmd = Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
    cmd.current_dir(root).args(["metadata", "--no-deps", "--format-version", "1", "--offline"]);
    if let Some(t) = toolchain {
        cmd.env("RUSTUP_TOOLCHAIN", t);
    }
    // Do not let the analysed tree's .cargo/config or build env leak in more than needed.
    cmd.env_remove("RUSTC_WRAPPER");
    let out = cmd.output().context("running cargo metadata")?;
    if !out.status.success() {
        bail!("cargo metadata failed in {}: {}", root.display(), String::from_utf8_lossy(&out.stderr));
    }
    let m: Metadata = serde_json::from_slice(&out.stdout).context("parsing cargo metadata")?;
    let ws_root = Path::new(&m.workspace_root).canonicalize()?;
    let mut ws = Workspace::default();
    for p in m.packages {
        let dir = Path::new(&p.manifest_path)
            .parent()
            .context("manifest without parent")?
            .canonicalize()?
            .strip_prefix(&ws_root)
            .context("package outside workspace")?
            .to_string_lossy()
            .into_owned();
        let mut path_deps = BTreeSet::new();
        let mut ext_deps = BTreeSet::new();
        for d in p.dependencies {
            if d.kind.as_deref() == Some("dev") {
                continue;
            }
            if d.path.is_some() {
                path_deps.insert(d.name);
            } else {
                ext_deps.insert(d.name);
            }
        }
        ws.crates.insert(
            p.name,
            WsCrate { dir, path_deps: path_deps.into_iter().collect(), ext_deps: ext_deps.into_iter().collect() },
        );
    }
    Ok(ws)
}

impl Workspace {
    /// Transitive closure (workspace crates only) from `roots`. Unknown roots are an error.
    pub fn closure(&self, roots: &[String]) -> Result<BTreeSet<String>> {
        let mut seen = BTreeSet::new();
        let mut q: VecDeque<String> = VecDeque::new();
        for r in roots {
            if !self.crates.contains_key(r) {
                bail!("root crate {r:?} is not a workspace package");
            }
            q.push_back(r.clone());
        }
        while let Some(c) = q.pop_front() {
            if !seen.insert(c.clone()) {
                continue;
            }
            for d in &self.crates[&c].path_deps {
                if self.crates.contains_key(d) && !seen.contains(d) {
                    q.push_back(d.clone());
                }
            }
        }
        Ok(seen)
    }
}

// ---------------------------------------------------------------- Cargo.lock

#[derive(Deserialize)]
struct Lock {
    #[serde(default)]
    package: Vec<LockPkg>,
}

#[derive(Deserialize, Clone)]
struct LockPkg {
    name: String,
    version: String,
    source: Option<String>,
    #[serde(default)]
    dependencies: Vec<String>,
}

/// External crates (`name` -> set of `version`) reachable from the given
/// workspace crates.
pub fn external_closure(lock_text: &str, ws: &Workspace, closure: &BTreeSet<String>) -> Result<BTreeMap<String, BTreeSet<String>>> {
    let lock: Lock = toml::from_str(lock_text).context("parsing Cargo.lock")?;
    let mut by_name: BTreeMap<&str, Vec<&LockPkg>> = BTreeMap::new();
    for p in &lock.package {
        by_name.entry(p.name.as_str()).or_default().push(p);
    }
    // Resolve a lock dependency spec "name", "name version" or "name version (source)".
    let resolve = |spec: &str| -> Vec<&LockPkg> {
        let mut parts = spec.split(' ');
        let name = parts.next().unwrap_or_default();
        let ver = parts.next();
        by_name
            .get(name)
            .map(|v| v.iter().copied().filter(|p| ver.is_none_or(|x| p.version == x)).collect())
            .unwrap_or_default()
    };
    let mut seen: BTreeSet<(String, String)> = BTreeSet::new();
    let mut q: VecDeque<&LockPkg> = VecDeque::new();
    for c in closure {
        let wc = &ws.crates[c];
        let ext: BTreeSet<&str> = wc.ext_deps.iter().map(|s| s.as_str()).collect();
        // The workspace crate's own lock entry (source = None).
        let Some(entry) = by_name.get(c.as_str()).and_then(|v| v.iter().find(|p| p.source.is_none())) else {
            continue;
        };
        for spec in &entry.dependencies {
            let name = spec.split(' ').next().unwrap_or_default();
            if ext.contains(name) {
                q.extend(resolve(spec));
            }
        }
    }
    while let Some(p) = q.pop_front() {
        if p.source.is_none() {
            continue; // workspace crate: handled by the workspace closure
        }
        if !seen.insert((p.name.clone(), p.version.clone())) {
            continue;
        }
        for spec in &p.dependencies {
            q.extend(resolve(spec));
        }
    }
    let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (n, v) in seen {
        out.entry(n).or_default().insert(v);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lock_closure_follows_only_non_dev_external_deps() {
        let mut ws = Workspace::default();
        ws.crates.insert(
            "a".into(),
            WsCrate { dir: "a".into(), path_deps: vec![], ext_deps: vec!["x".into()] },
        );
        let lock = r#"
version = 4
[[package]]
name = "a"
version = "0.1.0"
dependencies = ["x", "devonly"]
[[package]]
name = "x"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
dependencies = ["y 2.0.0"]
[[package]]
name = "y"
version = "2.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
[[package]]
name = "y"
version = "3.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
[[package]]
name = "devonly"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
"#;
        let c = external_closure(lock, &ws, &["a".to_string()].into()).unwrap();
        assert_eq!(c.keys().cloned().collect::<Vec<_>>(), vec!["x", "y"]);
        assert_eq!(c["y"].iter().cloned().collect::<Vec<_>>(), vec!["2.0.0"]);
    }

    #[test]
    fn closure_rejects_unknown_root() {
        let ws = Workspace::default();
        assert!(ws.closure(&["nope".into()]).is_err());
    }
}
