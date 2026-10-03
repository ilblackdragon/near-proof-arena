//! Thin wrappers around the `git` CLI. Nothing here mutates the repository:
//! trees are materialised with `git archive` into a scratch directory.

use anyhow::{bail, Context, Result};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

pub fn git(repo: &Path, args: &[&str]) -> Result<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .stderr(Stdio::piped())
        .output()
        .context("running git")?;
    if !out.status.success() {
        bail!(
            "git {:?} failed: {}",
            args,
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    String::from_utf8(out.stdout).context("git output not UTF-8")
}

pub fn resolve_commit(repo: &Path, r: &str) -> Result<String> {
    let s = git(repo, &["rev-parse", "--verify", &format!("{r}^{{commit}}")]).with_context(|| {
        format!(
            "ref {r:?} not found in {}; fetch it first (e.g. `git -C {} fetch --depth 1 origin tag {r}`)",
            repo.display(),
            repo.display()
        )
    })?;
    Ok(s.trim().to_string())
}

/// `git archive <commit> | tar -x -C <dest>`.
pub fn materialize(repo: &Path, commit: &str, dest: &Path) -> Result<()> {
    std::fs::create_dir_all(dest)?;
    let mut archive = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["archive", "--format=tar", commit])
        .stdout(Stdio::piped())
        .spawn()
        .context("spawning git archive")?;
    let tar = Command::new("tar")
        .arg("-x")
        .arg("-C")
        .arg(dest)
        .stdin(archive.stdout.take().unwrap())
        .status()
        .context("running tar")?;
    let a = archive.wait()?;
    if !a.success() || !tar.success() {
        bail!("materialising {commit} failed");
    }
    Ok(())
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct ChangedFile {
    /// A, M, D, R, C, T (first letter of git's status).
    pub status: String,
    pub path: String,
    /// For renames/copies: the old path.
    pub old_path: Option<String>,
}

pub fn changed_files(repo: &Path, old: &str, new: &str) -> Result<Vec<ChangedFile>> {
    let out = git(
        repo,
        &[
            "diff",
            "--no-ext-diff",
            "--name-status",
            "-z",
            "-M",
            old,
            new,
        ],
    )?;
    let mut it = out.split('\0').filter(|s| !s.is_empty());
    let mut v = Vec::new();
    while let Some(st) = it.next() {
        let status = st[..1].to_string();
        if status == "R" || status == "C" {
            let from = it.next().context("malformed rename")?.to_string();
            let to = it.next().context("malformed rename")?.to_string();
            v.push(ChangedFile {
                status,
                path: to,
                old_path: Some(from),
            });
        } else {
            let p = it.next().context("malformed name-status")?.to_string();
            v.push(ChangedFile {
                status,
                path: p,
                old_path: None,
            });
        }
    }
    Ok(v)
}

pub fn diff_paths(repo: &Path, old: &str, new: &str, paths: &[String]) -> Result<String> {
    if paths.is_empty() {
        return Ok(String::new());
    }
    let mut args: Vec<&str> = vec!["diff", "--no-ext-diff", "-U1", old, new, "--"];
    args.extend(paths.iter().map(|s| s.as_str()));
    git(repo, &args)
}

pub fn scratch_dir(base: Option<&Path>) -> Result<PathBuf> {
    let base = base
        .map(Path::to_path_buf)
        .unwrap_or_else(std::env::temp_dir);
    let d = base.join(format!(
        "upgrade-monitor-{}-{}",
        std::process::id(),
        nanos()
    ));
    std::fs::create_dir_all(&d)?;
    Ok(d)
}

fn nanos() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0)
}
