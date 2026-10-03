//! `upgrade-monitor`: semantic-impact report for a nearcore upgrade.
//!
//! Exit codes: 0 = NO_SEMANTIC_CHANGE_DETECTED, 3 = REVALIDATION_REQUIRED,
//! 2 = error (treat as REVALIDATION_REQUIRED). The tool fails closed: any
//! change inside the dependency closure of the runtime crates, any external
//! crate version change in that closure, any parameter/protocol-version
//! change, any parse failure, requires revalidation — even if existing Lean
//! proofs still compile.

mod cargo;
mod git;
mod impact;
mod protocol;
mod report;

use anyhow::{Context, Result};
use clap::Parser;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub const DEFAULT_ROOTS: &[&str] = &[
    "node-runtime",
    "near-vm-runner",
    "near-primitives",
    "near-primitives-core",
    "near-store",
    "near-parameters",
    "near-crypto",
];

#[derive(Parser)]
#[command(name = "upgrade-monitor", version)]
pub struct Args {
    /// nearcore git repository containing both refs (not modified).
    #[arg(long)]
    pub repo: PathBuf,
    /// Pinned ref (the challenge's nearcore tag/commit).
    #[arg(long)]
    pub old: String,
    /// Candidate newer ref.
    #[arg(long)]
    pub new: String,
    /// Governed path -> spec/obligation map.
    #[arg(long, default_value = "spec/impact-map.toml")]
    pub impact_map: PathBuf,
    /// Root crates of the semantic closure (comma separated).
    #[arg(long, value_delimiter = ',', default_values_t = DEFAULT_ROOTS.iter().map(|s| s.to_string()).collect::<Vec<_>>())]
    pub roots: Vec<String>,
    #[arg(long)]
    pub json: Option<PathBuf>,
    #[arg(long)]
    pub markdown: Option<PathBuf>,
    /// RUSTUP_TOOLCHAIN for `cargo metadata` (avoids installing the tree's pinned toolchain).
    #[arg(long, default_value = "stable")]
    pub toolchain: String,
    /// Scratch directory base (default: system temp dir).
    #[arg(long)]
    pub scratch: Option<PathBuf>,
    #[arg(long)]
    pub keep_scratch: bool,
}

const PARAM_DIR: &str = "core/parameters/res/runtime_configs/";
const BUILD_CONFIG_FILES: &[&str] = &["Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "rust-toolchain"];

fn main() {
    let args = Args::parse();
    match run(&args) {
        Ok(rep) => {
            eprintln!("{}", rep.verdict);
            for r in &rep.reasons {
                eprintln!("  - {r}");
            }
            std::process::exit(if rep.revalidation_required() { 3 } else { 0 });
        }
        Err(e) => {
            eprintln!("ERROR (treat as REVALIDATION_REQUIRED): {e:#}");
            std::process::exit(2);
        }
    }
}

fn run(args: &Args) -> Result<report::Report> {
    let repo = args.repo.canonicalize().context("repo path")?;
    let map = impact::ImpactMap::load(&args.impact_map)?;
    let old_c = git::resolve_commit(&repo, &args.old)?;
    let new_c = git::resolve_commit(&repo, &args.new)?;
    let scratch = git::scratch_dir(args.scratch.as_deref())?;
    let res = analyse(args, &repo, &map, &old_c, &new_c, &scratch);
    if !args.keep_scratch {
        let _ = std::fs::remove_dir_all(&scratch);
    }
    let rep = res?;
    if let Some(p) = &args.json {
        std::fs::write(p, serde_json::to_string_pretty(&rep)? + "\n")?;
    }
    if let Some(p) = &args.markdown {
        std::fs::write(p, report::markdown(&rep))?;
    }
    if args.json.is_none() && args.markdown.is_none() {
        println!("{}", serde_json::to_string_pretty(&rep)?);
    }
    Ok(rep)
}

struct Side {
    ws: cargo::Workspace,
    closure: BTreeSet<String>,
    missing_roots: Vec<String>,
    lock: String,
    facts: protocol::ProtocolFacts,
    includes: BTreeSet<String>,
}

fn side(root: &Path, args: &Args) -> Result<Side> {
    let ws = cargo::metadata(root, Some(&args.toolchain))?;
    let present: Vec<String> = args.roots.iter().filter(|r| ws.crates.contains_key(*r)).cloned().collect();
    let missing_roots = args.roots.iter().filter(|r| !ws.crates.contains_key(*r)).cloned().collect();
    let closure = ws.closure(&present)?;
    let lock = std::fs::read_to_string(root.join("Cargo.lock")).context("Cargo.lock missing")?;
    let includes = scan_includes(root, &ws, &closure)?;
    Ok(Side { facts: protocol::parse(root), ws, closure, missing_roots, lock, includes })
}

/// Files pulled in by literal `include_str!`/`include_bytes!` paths that
/// resolve outside the including crate's directory.
fn scan_includes(root: &Path, ws: &cargo::Workspace, closure: &BTreeSet<String>) -> Result<BTreeSet<String>> {
    let mut out = BTreeSet::new();
    for c in closure {
        let dir = root.join(&ws.crates[c].dir);
        let mut stack = vec![dir.clone()];
        while let Some(d) = stack.pop() {
            for e in std::fs::read_dir(&d)? {
                let p = e?.path();
                let ft = std::fs::symlink_metadata(&p)?.file_type();
                if ft.is_dir() {
                    if p.file_name().is_some_and(|n| n == "target") {
                        continue;
                    }
                    stack.push(p);
                } else if p.extension().is_some_and(|x| x == "rs") {
                    let Ok(text) = std::fs::read_to_string(&p) else { continue };
                    for mac in ["include_str!(\"", "include_bytes!(\""] {
                        let mut rest = text.as_str();
                        while let Some(i) = rest.find(mac) {
                            rest = &rest[i + mac.len()..];
                            let Some(j) = rest.find('"') else { break };
                            let lit = &rest[..j];
                            let target = normalize(&p.parent().unwrap().join(lit));
                            if let Ok(rel) = target.strip_prefix(root) {
                                if !target.starts_with(&dir) {
                                    out.insert(rel.to_string_lossy().into_owned());
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}

fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            other => out.push(other),
        }
    }
    out
}

/// Longest-prefix owner crate of a path.
fn owner<'a>(ws: &'a cargo::Workspace, path: &str) -> Option<&'a str> {
    ws.crates
        .iter()
        .filter(|(_, c)| c.dir.is_empty() || path.starts_with(&format!("{}/", c.dir)))
        .max_by_key(|(_, c)| c.dir.len())
        .map(|(n, _)| n.as_str())
}

fn analyse(
    args: &Args,
    repo: &Path,
    map: &impact::ImpactMap,
    old_c: &str,
    new_c: &str,
    scratch: &Path,
) -> Result<report::Report> {
    let (od, nd) = (scratch.join("old"), scratch.join("new"));
    git::materialize(repo, old_c, &od)?;
    git::materialize(repo, new_c, &nd)?;
    let old = side(&od.canonicalize()?, args)?;
    let new = side(&nd.canonicalize()?, args)?;

    let mut reasons = Vec::new();
    for (label, s) in [("old", &old), ("new", &new)] {
        if !s.missing_roots.is_empty() {
            reasons.push(format!("root crate(s) {:?} missing in {label} tree", s.missing_roots));
        }
    }
    let closure: BTreeSet<String> = old.closure.union(&new.closure).cloned().collect();
    let added_to_closure: Vec<String> = new.closure.difference(&old.closure).cloned().collect();
    let removed_from_closure: Vec<String> = old.closure.difference(&new.closure).cloned().collect();
    if !added_to_closure.is_empty() || !removed_from_closure.is_empty() {
        reasons.push(format!(
            "closure membership changed (+{:?} -{:?})",
            added_to_closure, removed_from_closure
        ));
    }
    let includes: BTreeSet<String> = old.includes.union(&new.includes).cloned().collect();

    // ---- changed files
    let changed = git::changed_files(repo, old_c, new_c)?;
    let mut in_closure = Vec::new();
    let mut build_config = Vec::new();
    let mut outside = 0usize;
    for f in &changed {
        let mut paths = vec![f.path.as_str()];
        if let Some(o) = &f.old_path {
            paths.push(o);
        }
        let mut hit: Option<String> = None;
        for p in &paths {
            for s in [&old, &new] {
                if let Some(c) = owner(&s.ws, p) {
                    if closure.contains(c) {
                        hit = Some(c.to_string());
                    }
                }
            }
            if includes.contains(*p) {
                hit.get_or_insert_with(|| "(include_*! target)".into());
            }
        }
        let is_build_cfg = paths.iter().any(|p| BUILD_CONFIG_FILES.contains(p) || p.starts_with(".cargo/"));
        if let Some(c) = hit {
            in_closure.push(report::ClosureChange { path: f.path.clone(), old_path: f.old_path.clone(), status: f.status.clone(), crate_name: c });
        } else if is_build_cfg {
            build_config.push(f.path.clone());
        } else {
            outside += 1;
        }
    }
    if !in_closure.is_empty() {
        reasons.push(format!("{} file(s) changed inside the runtime dependency closure", in_closure.len()));
    }
    if !build_config.is_empty() {
        reasons.push(format!("workspace build configuration changed: {build_config:?}"));
    }

    // ---- external crates
    let ext_old = cargo::external_closure(&old.lock, &old.ws, &old.closure)?;
    let ext_new = cargo::external_closure(&new.lock, &new.ws, &new.closure)?;
    let mut ext_changes = Vec::new();
    for name in ext_old.keys().chain(ext_new.keys()).collect::<BTreeSet<_>>() {
        let (a, b) = (ext_old.get(name).cloned().unwrap_or_default(), ext_new.get(name).cloned().unwrap_or_default());
        if a != b {
            ext_changes.push(report::ExternalChange { name: name.clone(), old_versions: a.into_iter().collect(), new_versions: b.into_iter().collect() });
        }
    }
    if !ext_changes.is_empty() {
        reasons.push(format!("{} external crate(s) in the closure changed version", ext_changes.len()));
    }

    // ---- parameters
    let param_files: Vec<String> = changed
        .iter()
        .filter(|f| f.path.starts_with(PARAM_DIR) || f.old_path.as_deref().is_some_and(|o| o.starts_with(PARAM_DIR)))
        .map(|f| format!("{} {}", f.status, f.path))
        .collect();
    let param_diff = if param_files.is_empty() {
        String::new()
    } else {
        let d = git::git(repo, &["diff", "--no-ext-diff", "-U0", old_c, new_c, "--", PARAM_DIR])?;
        truncate_lines(&d, 400)
    };
    if !param_files.is_empty() {
        reasons.push(format!("{} runtime parameter file(s) changed", param_files.len()));
    }

    // ---- protocol facts
    let pdiff = protocol::diff(&old.facts, &new.facts);
    if !pdiff.parse_errors.is_empty() {
        reasons.push(format!("protocol facts could not be fully parsed ({} issue(s)) — treated as changed", pdiff.parse_errors.len()));
    }
    if pdiff.old_stable != pdiff.new_stable {
        reasons.push(format!("STABLE_PROTOCOL_VERSION {:?} -> {:?}", pdiff.old_stable, pdiff.new_stable));
    }
    if !pdiff.features_added.is_empty() || !pdiff.features_removed.is_empty() || !pdiff.features_version_changed.is_empty() {
        reasons.push(format!(
            "ProtocolFeature set changed (+{} -{} ~{})",
            pdiff.features_added.len(),
            pdiff.features_removed.len(),
            pdiff.features_version_changed.len()
        ));
    }
    if !pdiff.db_constants_changed.is_empty() {
        reasons.push("database version constants changed".into());
    }

    // ---- version gates in changed closure sources
    let rs_paths: Vec<String> = in_closure.iter().filter(|c| c.path.ends_with(".rs") && c.status != "D").map(|c| c.path.clone()).collect();
    let mut gates: BTreeMap<String, report::GateRefs> = BTreeMap::new();
    for chunk in rs_paths.chunks(200) {
        let d = git::diff_paths(repo, old_c, new_c, chunk)?;
        let mut file = String::new();
        for line in d.lines() {
            if let Some(f) = line.strip_prefix("+++ b/") {
                file = f.to_string();
                continue;
            }
            if line.starts_with("+++") || line.starts_with("---") {
                continue;
            }
            let sign = match line.chars().next() {
                Some('+') => 1,
                Some('-') => -1,
                _ => continue,
            };
            let mut rest = line;
            while let Some(i) = rest.find("ProtocolFeature::") {
                rest = &rest[i + "ProtocolFeature::".len()..];
                let name: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
                let g = gates.entry(name).or_default();
                if sign > 0 { g.added_refs += 1 } else { g.removed_refs += 1 }
                if !g.files.contains(&file) {
                    g.files.push(file.clone());
                }
            }
        }
    }

    // ---- migrations
    let migrations: Vec<String> = changed
        .iter()
        .filter(|f| f.path.to_lowercase().contains("migration"))
        .map(|f| format!("{} {}", f.status, f.path))
        .collect();

    // ---- impact mapping
    let mut impact_inputs: Vec<String> = in_closure.iter().map(|c| c.path.clone()).collect();
    impact_inputs.extend(build_config.iter().map(|p| format!("@workspace/{p}")));
    impact_inputs.extend(ext_changes.iter().map(|e| format!("@external/{}", e.name)));
    if !pdiff.is_empty() {
        impact_inputs.push("@protocol/version".into());
    }
    if !migrations.is_empty() {
        impact_inputs.push("@migrations".into());
    }
    for r in &reasons {
        if r.starts_with("root crate") || r.starts_with("closure membership") {
            impact_inputs.push("@closure/membership".into());
        }
    }
    let impact = impact::evaluate(map, &impact_inputs);

    let mut closure_crates: Vec<report::CrateInfo> = closure
        .iter()
        .map(|c| {
            let dir = new.ws.crates.get(c).or_else(|| old.ws.crates.get(c)).map(|x| x.dir.clone()).unwrap_or_default();
            report::CrateInfo { name: c.clone(), dir, changed_files: in_closure.iter().filter(|x| &x.crate_name == c).count() }
        })
        .collect();
    closure_crates.sort_by(|a, b| a.name.cmp(&b.name));

    let verdict = if reasons.is_empty() { "NO_SEMANTIC_CHANGE_DETECTED" } else { "REVALIDATION_REQUIRED" };
    Ok(report::Report {
        schema: "arena-upgrade-impact-v1".into(),
        tool: format!("upgrade-monitor {}", env!("CARGO_PKG_VERSION")),
        verdict: verdict.into(),
        reasons,
        old: report::RefInfo { r#ref: args.old.clone(), commit: old_c.into(), stable_protocol_version: pdiff.old_stable },
        new: report::RefInfo { r#ref: args.new.clone(), commit: new_c.into(), stable_protocol_version: pdiff.new_stable },
        roots: args.roots.clone(),
        closure: report::ClosureInfo {
            crates: closure_crates,
            added: added_to_closure,
            removed: removed_from_closure,
            include_targets_outside_crates: includes.into_iter().collect(),
            external_crates_old: ext_old.values().map(|v| v.len()).sum(),
            external_crates_new: ext_new.values().map(|v| v.len()).sum(),
        },
        changed_files_total: changed.len(),
        changed_files_outside_closure: outside,
        changed_in_closure: in_closure,
        workspace_build_config_changes: build_config,
        external_crate_changes: ext_changes,
        parameters: report::ParamInfo { changed_files: param_files, diff_excerpt: param_diff },
        protocol: pdiff,
        version_gate_changes: gates,
        migrations,
        impact,
    })
}

fn truncate_lines(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    if lines.len() <= n {
        s.to_string()
    } else {
        format!("{}\n… ({} more lines truncated)\n", lines[..n].join("\n"), lines.len() - n)
    }
}
