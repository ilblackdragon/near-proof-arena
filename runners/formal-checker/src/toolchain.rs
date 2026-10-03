//! Pinned toolchain and tool discovery.
//!
//! The Lean toolchain is a single config value: `runners/formal-checker/lean-toolchain`.
//! Everything (judge reference build, sandboxed candidate elaboration,
//! `leanchecker`, `lean4export`, `arena-audit`) uses exactly that toolchain.
//! `scripts/setup-tools.sh` installs it and builds the pinned helper tools into
//! `$ARENA_FC_HOME` (default `~/.cache/arena-formal-checker`).

use crate::digest::sha256_file;
use arena_types::Digest;
use serde::Serialize;
use std::path::{Path, PathBuf};

/// The one pinned toolchain, e.g. `leanprover/lean4:v4.34.1`.
pub const LEAN_TOOLCHAIN: &str = include_str!("../lean-toolchain");

/// Pinned helper tool revisions (see `tools.toml`).
pub const TOOLS_TOML: &str = include_str!("../tools.toml");

pub fn lean_toolchain() -> &'static str {
    LEAN_TOOLCHAIN.trim()
}

/// elan directory name for a toolchain spec: `leanprover/lean4:v4.34.1` -> `leanprover--lean4---v4.34.1`.
pub fn elan_dir_name(spec: &str) -> String {
    spec.replace('/', "--").replace(':', "---")
}

#[derive(Clone, Debug, Serialize)]
pub struct ToolPaths {
    /// Toolchain root (contains `bin/lean`, `bin/leanchecker`, `lib/lean`).
    pub lean_sysroot: PathBuf,
    pub lean4export: PathBuf,
    /// Optional: independent Rust kernel. `None` = not installed (recorded, never PASS-by-default).
    pub nanoda: Option<PathBuf>,
    pub arena_audit: PathBuf,
}

#[derive(Debug, thiserror::Error)]
pub enum ToolError {
    #[error("tool missing: {0} (run runners/formal-checker/scripts/setup-tools.sh)")]
    Missing(String),
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

pub fn fc_home() -> PathBuf {
    if let Ok(p) = std::env::var("ARENA_FC_HOME") {
        return PathBuf::from(p);
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| "/root".into());
    PathBuf::from(home).join(".cache/arena-formal-checker")
}

fn elan_home() -> PathBuf {
    if let Ok(p) = std::env::var("ELAN_HOME") {
        return PathBuf::from(p);
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| "/root".into());
    PathBuf::from(home).join(".elan")
}

impl ToolPaths {
    /// Discover tools: env overrides `ARENA_LEAN_SYSROOT`, `ARENA_LEAN4EXPORT`,
    /// `ARENA_NANODA`, `ARENA_AUDIT_BIN`; otherwise the layout produced by setup-tools.sh.
    pub fn discover() -> Result<Self, ToolError> {
        let home = fc_home().join(elan_dir_name(lean_toolchain()));
        let env_or = |k: &str, d: PathBuf| std::env::var(k).map(PathBuf::from).unwrap_or(d);
        let lean_sysroot = env_or(
            "ARENA_LEAN_SYSROOT",
            elan_home().join("toolchains").join(elan_dir_name(lean_toolchain())),
        );
        let lean4export = env_or("ARENA_LEAN4EXPORT", home.join("bin/lean4export"));
        let nanoda = env_or("ARENA_NANODA", home.join("bin/nanoda_bin"));
        let arena_audit = env_or("ARENA_AUDIT_BIN", home.join("bin/arena-audit"));
        for (name, p) in [
            ("lean", lean_sysroot.join("bin/lean")),
            ("leanchecker", lean_sysroot.join("bin/leanchecker")),
            ("lean4export", lean4export.clone()),
            ("arena-audit", arena_audit.clone()),
        ] {
            if !p.is_file() {
                return Err(ToolError::Missing(format!("{name} at {}", p.display())));
            }
        }
        Ok(ToolPaths {
            lean_sysroot,
            lean4export,
            nanoda: nanoda.is_file().then_some(nanoda),
            arena_audit,
        })
    }

    pub fn lean(&self) -> PathBuf {
        self.lean_sysroot.join("bin/lean")
    }
    pub fn leanchecker(&self) -> PathBuf {
        self.lean_sysroot.join("bin/leanchecker")
    }

    /// Digest identifying the checker "image" in dev mode: toolchain spec, the
    /// pinned tool revisions and the bytes of every helper binary we execute.
    /// (In production this is the checker rootfs digest from the challenge.)
    pub fn image_digest(&self) -> Result<Digest, ToolError> {
        let mut parts = vec![
            ("toolchain".to_string(), lean_toolchain().to_string()),
            ("tools.toml".to_string(), Digest::of_bytes(TOOLS_TOML.as_bytes()).to_string()),
        ];
        let mut add = |label: &str, p: &Path| -> Result<(), ToolError> {
            parts.push((label.to_string(), sha256_file(p)?.to_string()));
            Ok(())
        };
        add("lean", &self.lean())?;
        add("leanchecker", &self.leanchecker())?;
        add("lean4export", &self.lean4export)?;
        add("arena-audit", &self.arena_audit)?;
        if let Some(n) = &self.nanoda {
            add("nanoda", n)?;
        }
        Ok(arena_types::sha256_digest(&parts).expect("no floats"))
    }
}
