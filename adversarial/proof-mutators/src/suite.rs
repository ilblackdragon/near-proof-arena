//! Walk and validate the `hostile-submissions/` tree: every case is a complete
//! candidate package plus an `expect.json`. This is the local well-formedness
//! check (run as a test and by the `check-suite` binary); the full e2e run
//! submits the packages to a live server.
//!
//! Some cases attack the packaging layer itself (an intentionally invalid
//! `candidate.toml`, or a malicious archive built by `make-archive.py`). For
//! those, a manifest that fails to parse is *expected*, not a loader error: the
//! cross-check [`Case::check`] enforces that a parse failure only happens when
//! the case expects a `PKG_WELLFORMED` failure.

use crate::expect::{Expect, ExpectError};
use arena_types::{CandidateManifest, ObligationId};
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct Case {
    pub name: String,
    pub dir: PathBuf,
    /// `Ok` for well-formed packages; `Err(message)` for cases that ship an
    /// intentionally invalid manifest (checked against `expect.json`).
    pub manifest: Result<CandidateManifest, String>,
    pub expect: Expect,
    /// True when the case ships a `make-archive.py` (archive-attack cases whose
    /// hostile payload is the archive encoding, not the directory).
    pub has_archive_builder: bool,
    /// For a derived case: the base package directory named by `BASE`.
    pub base: Option<PathBuf>,
}

#[derive(Debug, thiserror::Error)]
pub enum SuiteError {
    #[error("io {path}: {source}")]
    Io {
        path: String,
        source: std::io::Error,
    },
    #[error("case {case}: missing required path {missing}")]
    MissingPath { case: String, missing: String },
    #[error("case {case}: expect.json name {expect_case:?} != folder")]
    NameMismatch { case: String, expect_case: String },
    #[error("case {case}: {msg}")]
    Inconsistent { case: String, msg: String },
    #[error(transparent)]
    Expect(#[from] ExpectError),
}

/// The canonical location of the suite relative to the crate manifest.
pub fn default_root() -> PathBuf {
    // crate is adversarial/proof-mutators; suite is adversarial/hostile-submissions
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("hostile-submissions")
}

fn read(path: &Path) -> Result<String, SuiteError> {
    std::fs::read_to_string(path).map_err(|source| SuiteError::Io {
        path: path.display().to_string(),
        source,
    })
}

/// Load and validate every case under `root`.
pub fn load_all(root: &Path) -> Result<Vec<Case>, SuiteError> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(root)
        .map_err(|source| SuiteError::Io {
            path: root.display().to_string(),
            source,
        })?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    entries.sort();
    let mut cases = Vec::new();
    for dir in entries {
        let c = load_case(&dir)?;
        c.check()?;
        cases.push(c);
    }
    Ok(cases)
}

pub fn load_case(dir: &Path) -> Result<Case, SuiteError> {
    let name = dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or_default()
        .to_string();

    // A DERIVED case names a base package (repo-relative, e.g.
    // `examples/reexec-witness`) in `BASE` and ships only the files that
    // differ; the submitted package is base + overlay. The layout check then
    // applies to the union.
    let base = match std::fs::read_to_string(dir.join("BASE")) {
        Ok(s) => {
            let rel = s.trim();
            // hostile-submissions/<case> -> repo root is three levels up.
            let repo = dir
                .ancestors()
                .nth(3)
                .ok_or_else(|| SuiteError::Inconsistent {
                    case: name.clone(),
                    msg: "BASE: cannot locate the repo root".into(),
                })?;
            let b = repo.join(rel);
            if rel.is_empty()
                || rel.starts_with('/')
                || rel.split('/').any(|c| c == "..")
                || !b.is_dir()
            {
                return Err(SuiteError::Inconsistent {
                    case: name.clone(),
                    msg: format!("BASE {rel:?} is not a repo-relative package directory"),
                });
            }
            Some(b)
        }
        Err(_) => None,
    };

    // Required layout (CONTRACTS.md §3).
    let required = [
        "candidate.toml",
        "expect.json",
        "README.md",
        "build-recipe/build.sh",
        "source",
        "formal",
    ];
    for r in required {
        let in_base = base.as_ref().is_some_and(|b| b.join(r).exists());
        // expect.json is judge-side and always belongs to the case itself.
        let present = dir.join(r).exists() || (in_base && r != "expect.json");
        if !present {
            return Err(SuiteError::MissingPath {
                case: name.clone(),
                missing: r.to_string(),
            });
        }
    }

    let manifest_path = match (&base, dir.join("candidate.toml")) {
        (Some(b), p) if !p.exists() => b.join("candidate.toml"),
        (_, p) => p,
    };
    let manifest = match CandidateManifest::parse(&read(&manifest_path)?) {
        Ok(m) => Ok(m),
        Err(e) => Err(e.to_string()),
    };

    let expect = Expect::parse(&read(&dir.join("expect.json"))?)?;
    if expect.case != name {
        return Err(SuiteError::NameMismatch {
            case: name.clone(),
            expect_case: expect.case.clone(),
        });
    }

    Ok(Case {
        name,
        dir: dir.to_path_buf(),
        manifest,
        expect,
        has_archive_builder: dir.join("make-archive.py").exists(),
        base,
    })
}

impl Case {
    /// Cross-checks between the package and its `expect.json`.
    pub fn check(&self) -> Result<(), SuiteError> {
        let bad = |msg: String| {
            Err(SuiteError::Inconsistent {
                case: self.name.clone(),
                msg,
            })
        };
        let expects_pkg = self
            .expect
            .expected_failing_gates
            .contains(&ObligationId::PkgWellformed);

        match &self.manifest {
            Ok(_) => {}
            Err(e) => {
                // An invalid manifest is only allowed if the case is supposed to
                // fail PKG_WELLFORMED.
                if !expects_pkg {
                    return bad(format!(
                        "candidate.toml failed to parse ({e}) but the case does not \
                         expect a PKG_WELLFORMED failure"
                    ));
                }
            }
        }

        // Archive-attack cases must ship a builder; non-archive cases must not.
        let is_archive = self.expect.attack_family == "archive-attack";
        if is_archive && !self.has_archive_builder {
            return bad("archive-attack case is missing make-archive.py".into());
        }
        Ok(())
    }
}
