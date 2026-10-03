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

/// Files whose content determines the helper-tool build (keep in sync with
/// `TOOLS_KEY_FILES` in `scripts/setup-tools.sh`), embedded at compile time.
pub const TOOLS_KEY_FILES: &[(&str, &str)] = &[
    ("lean-toolchain", include_str!("../lean-toolchain")),
    ("tools.toml", include_str!("../tools.toml")),
    (
        "scripts/setup-tools.sh",
        include_str!("../scripts/setup-tools.sh"),
    ),
    (
        "lean/ArenaAudit/lakefile.toml",
        include_str!("../lean/ArenaAudit/lakefile.toml"),
    ),
    (
        "lean/ArenaAudit/lake-manifest.json",
        include_str!("../lean/ArenaAudit/lake-manifest.json"),
    ),
    (
        "lean/ArenaAudit/Main.lean",
        include_str!("../lean/ArenaAudit/Main.lean"),
    ),
    (
        "lean/ArenaAudit/ArenaAudit.lean",
        include_str!("../lean/ArenaAudit/ArenaAudit.lean"),
    ),
    (
        "lean/ArenaAudit/ArenaAudit/Audit.lean",
        include_str!("../lean/ArenaAudit/ArenaAudit/Audit.lean"),
    ),
];

/// Content address of the helper tools this checker source expects
/// (16 hex chars; same algorithm as setup-tools.sh).
pub fn tools_key() -> String {
    use sha2::Digest as _;
    let mut listing = String::new();
    for (path, content) in TOOLS_KEY_FILES {
        listing.push_str(path);
        listing.push('\n');
        listing.push_str(&hex::encode(sha2::Sha256::digest(content.as_bytes())));
        listing.push('\n');
    }
    hex::encode(sha2::Sha256::digest(listing.as_bytes()))[..16].to_string()
}

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
    /// Optional: lean4lean (independent kernel in Lean, replays .olean).
    pub lean4lean: Option<PathBuf>,
    pub arena_audit: PathBuf,
}

#[derive(Debug, thiserror::Error)]
pub enum ToolError {
    #[error("tool missing: {0} (run runners/formal-checker/scripts/setup-tools.sh)")]
    Missing(String),
    #[error("helper tool mismatch: {0} (run runners/formal-checker/scripts/setup-tools.sh for this checkout)")]
    Mismatch(String),
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
        let key = tools_key();
        let home = fc_home().join(elan_dir_name(lean_toolchain())).join(&key);
        let env_or = |k: &str, d: PathBuf| std::env::var(k).map(PathBuf::from).unwrap_or(d);
        let lean_sysroot = env_or(
            "ARENA_LEAN_SYSROOT",
            elan_home()
                .join("toolchains")
                .join(elan_dir_name(lean_toolchain())),
        );
        let lean4export = env_or("ARENA_LEAN4EXPORT", home.join("bin/lean4export"));
        let nanoda = env_or("ARENA_NANODA", home.join("bin/nanoda_bin"));
        let arena_audit = env_or("ARENA_AUDIT_BIN", home.join("bin/arena-audit"));
        let lean4lean = env_or("ARENA_LEAN4LEAN", home.join("bin/lean4lean"));
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
        // Never run a helper built from different sources: the key baked into
        // arena-audit at build time must equal this checker's key.
        let out = std::process::Command::new(&arena_audit)
            .arg("version")
            .output()?;
        let baked = String::from_utf8_lossy(&out.stdout).trim().to_string();
        if !out.status.success() || baked != key {
            return Err(ToolError::Mismatch(format!(
                "arena-audit at {} reports tools key {baked:?}, this checker expects {key}",
                arena_audit.display()
            )));
        }
        Ok(ToolPaths {
            lean_sysroot,
            lean4export,
            nanoda: nanoda.is_file().then_some(nanoda),
            lean4lean: lean4lean.is_file().then_some(lean4lean),
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
            ("tools_key".to_string(), tools_key()),
            (
                "tools.toml".to_string(),
                Digest::of_bytes(TOOLS_TOML.as_bytes()).to_string(),
            ),
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
        if let Some(n) = &self.lean4lean {
            add("lean4lean", n)?;
        }
        Ok(arena_types::sha256_digest(&parts).expect("no floats"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Rust key must equal the one setup-tools.sh computes (same file list).
    #[test]
    fn tools_key_matches_setup_script() {
        let here = Path::new(env!("CARGO_MANIFEST_DIR"));
        let script = std::fs::read_to_string(here.join("scripts/setup-tools.sh")).unwrap();
        let files_line = script
            .lines()
            .find(|l| l.starts_with("TOOLS_KEY_FILES="))
            .unwrap();
        let files: Vec<&str> = files_line
            .trim_start_matches("TOOLS_KEY_FILES=")
            .trim_matches('"')
            .split_whitespace()
            .collect();
        assert_eq!(
            files,
            TOOLS_KEY_FILES.iter().map(|(p, _)| *p).collect::<Vec<_>>(),
            "file lists out of sync"
        );
        let out = std::process::Command::new("bash")
            .current_dir(here)
            .arg("-c")
            .arg(format!(
                "for f in {}; do printf '%s\\n%s\\n' \"$f\" \"$(sha256sum < \"$f\" | cut -c1-64)\"; done | sha256sum | cut -c1-16",
                files.join(" ")
            ))
            .output()
            .unwrap();
        assert_eq!(String::from_utf8(out.stdout).unwrap().trim(), tools_key());
    }

    /// A helper from another checker revision is an explicit error, never used.
    #[test]
    fn mismatched_arena_audit_is_rejected() {
        let dir = std::env::temp_dir().join(format!("fc-mismatch-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let fake = dir.join("arena-audit");
        std::fs::write(&fake, "#!/bin/sh\necho 0000000000000000\n").unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&fake, std::fs::Permissions::from_mode(0o755)).unwrap();
        // Only meaningful where the toolchain and other tools are installed.
        let Ok(real) = ToolPaths::discover() else {
            return;
        };
        let mut paths = real.clone();
        paths.arena_audit = fake.clone();
        std::env::set_var("ARENA_AUDIT_BIN", &fake);
        let r = ToolPaths::discover();
        std::env::remove_var("ARENA_AUDIT_BIN");
        assert!(matches!(r, Err(ToolError::Mismatch(_))), "{r:?}");
        let _ = paths;
    }
}
