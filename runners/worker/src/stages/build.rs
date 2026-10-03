//! `BUILD_REPRODUCIBLE`: run the recipe offline in the sandbox twice, each
//! time in fresh scratch, and require bit-identical output trees; then run
//! the judge's `prepare` twice on the bundle and require identical public
//! dirs. Produces `BuildOutputs` (entry-point digests, bundle + public
//! TreeDigests and their uploaded archives, formal tree digest).

use super::common;
use crate::executor::{describe_exit, ExecError, JobRun, StageOut, MAX_PACKAGE_BYTES};
use crate::gate::Gate;
use crate::jobs::{BuildJob, BuildOutputs, RunLimits};
use arena_sandbox::{CopyIn, ExitStatus, Mount, Rootfs, SandboxSpec};
use arena_types::{Digest, GateStatus, ObligationId, ReasonCode};
use std::path::{Path, PathBuf};
use std::time::Duration;

/// Worker-side build limits (the challenge fixes the wall budget and RAM).
const BUILD_PIDS: u32 = 512;
const BUILD_SCRATCH_MB: u64 = 4096;
const MAX_BUNDLE_OUTPUT: u64 = 2 << 30;

/// Identify the toolchain the build ran against. Returns (rootfs, digest
/// string, extra mounts).
fn toolchain(r: &JobRun<'_>) -> Result<(Rootfs, Digest, Vec<Mount>), ExecError> {
    // Host-dev toolchain: identified by a digest of its description. Not a
    // pinned image; only meaningful for DEMO-tier runs.
    let os = std::fs::read_to_string("/etc/os-release").unwrap_or_default();
    let mounts: Vec<(String, String)> = r.ctx.build.mounts.iter().map(|m| (m.host.display().to_string(), m.guest.clone())).collect();
    let desc = serde_json::json!({
        "kind": "host-dev",
        "os_release": os,
        "mounts": mounts,
        "path": r.ctx.build.path,
    });
    let d = arena_types::sha256_digest(&desc).map_err(|e| ExecError::Infra(e.to_string()))?;
    Ok((Rootfs::HostDev, d, r.ctx.build.mounts.clone()))
}

struct BuildRun {
    root: PathBuf,
    tree: arena_archive::Tree,
    wall_ns: u64,
}

fn fail_out(mut g: Gate, out: &mut StageOut, reason: ReasonCode, note: String) -> Result<StageOut, ExecError> {
    if reason != ReasonCode::BuildFailed && reason != ReasonCode::BuildNotReproducible {
        g.fail(ReasonCode::BuildFailed, note.clone());
    }
    g.fail(reason, note);
    out.gates.push(g.finish(GateStatus::Unknown, true));
    Ok(std::mem::take(out))
}

pub fn run(r: &mut JobRun<'_>, j: &BuildJob) -> Result<StageOut, ExecError> {
    let g = Gate::start(ObligationId::BuildReproducible);
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    let layout = r.ctx.sandbox.layout();
    if !layout.flexible_scratch || layout.scratch != arena_sandbox::SCRATCH {
        return Err(ExecError::Infra(format!(
            "sandbox backend {} cannot run builds yet (needs copy-in of the package into scratch)",
            r.ctx.sandbox.name()
        )));
    }
    let bytes = r.fetch(&j.ctx.package_digest, MAX_PACKAGE_BYTES)?;
    let pkg_dir = r.fresh("pkg");
    let x = match arena_archive::ingest_bytes(&bytes, &pkg_dir, &arena_archive::Limits::default()) {
        Ok(x) => x,
        Err(arena_archive::ArchiveError::Unsafe(m)) => return Err(ExecError::Infra(format!("package passed validation but is now unsafe: {m}"))),
        Err(e) => return Err(e.into()),
    };
    let manifest = match arena_archive::validate_package(&x.root, &x.tree) {
        Ok(m) => m,
        Err(arena_archive::PackageError::Io(e)) => return Err(e.into()),
        Err(e) => return Err(ExecError::Infra(format!("package passed validation but manifest is now invalid: {e}"))),
    };
    if manifest != j.manifest {
        return Err(ExecError::Infra("package manifest differs from the validated manifest".into()));
    }
    let (rootfs, tc_digest, mounts) = toolchain(r)?;
    let limits = RunLimits::from_challenge(&j.challenge);

    let mut builds: Vec<BuildRun> = vec![];
    for i in 1..=2 {
        let out_dir = r.fresh("build-out");
        let spec = build_spec(j, &x.root, &rootfs, &mounts, r, &out_dir);
        let o = r.run(&spec)?;
        let log = [&b"--- stdout ---\n"[..], &o.stdout_trunc, b"\n--- stderr ---\n", &o.stderr_trunc].concat();
        r.upload(&format!("build log {i}"), &log, true)?;
        if !o.exit.success() {
            let reason = match o.exit {
                ExitStatus::TimedOut => ReasonCode::Timeout,
                ExitStatus::OomKilled => ReasonCode::ResourceLimit,
                _ if o.pids_limit_hit => ReasonCode::ResourceLimit,
                _ => ReasonCode::BuildFailed,
            };
            let tail = String::from_utf8_lossy(&o.stderr_trunc[o.stderr_trunc.len().saturating_sub(600)..]).into_owned();
            return fail_out(g, &mut out, reason, format!("build {i} {}; stderr tail: {tail}", describe_exit(&o)));
        }
        if let Some(e) = &o.output_error {
            return fail_out(g, &mut out, ReasonCode::BuildFailed, format!("build {i} outputs rejected: {e}"));
        }
        let root = out_dir.join("work");
        std::fs::create_dir_all(&root)?;
        let tree = arena_archive::tree_from_dir(&root, &arena_archive::Limits { max_expanded_bytes: MAX_BUNDLE_OUTPUT, ..Default::default() })?;
        let mut missing = vec![];
        for o in &manifest.build.outputs {
            if !tree.has_content_at(o) {
                missing.push(o.clone());
            }
        }
        for e in [&manifest.entry.prepare, &manifest.entry.prove, &manifest.entry.verify] {
            if !tree.is_exec(e) {
                missing.push(format!("{e} (executable)"));
            }
        }
        if !missing.is_empty() {
            return fail_out(g, &mut out, ReasonCode::BuildFailed, format!("build {i} did not produce {}", missing.join(", ")));
        }
        builds.push(BuildRun { root, tree, wall_ns: o.wall_ns });
    }
    let (a, b) = (&builds[0], &builds[1]);
    let (da, db) = (a.tree.digest(), b.tree.digest());
    if da != db {
        let mut diff: Vec<&str> = a
            .tree
            .files
            .iter()
            .filter(|(p, f)| b.tree.files.get(*p) != Some(f))
            .map(|(p, _)| p.as_str())
            .chain(b.tree.files.keys().filter(|p| !a.tree.files.contains_key(*p)).map(|p| p.as_str()))
            .collect();
        diff.truncate(20);
        return fail_out(
            g,
            &mut out,
            ReasonCode::BuildNotReproducible,
            format!("two builds differ ({da} vs {db}); differing paths: {}", diff.join(", ")),
        );
    }
    let mut g = g;
    g.note(format!("two independent builds produced identical trees {da}"));
    let (bundle_archive, bundle_tree) = r.upload_tree("bundle", &a.root.clone(), &a.tree.clone(), false)?;

    // Judge-run prepare, twice: the public dir is part of the verified
    // surface, so it must be a deterministic function of the bundle.
    let bundle_root = a.root.clone();
    let mut prepared = vec![];
    for i in 1..=2 {
        match common::run_prepare(r, &bundle_root, &manifest.entry, &limits)? {
            Ok(p) => prepared.push(p),
            Err(f) => {
                let reason = if f.reason == ReasonCode::ProverFailed { ReasonCode::BuildFailed } else { f.reason };
                return fail_out(g, &mut out, reason, format!("judge-run prepare #{i}: {}", f.detail));
            }
        }
    }
    let (p1, p2) = (prepared[0].tree.digest(), prepared[1].tree.digest());
    if p1 != p2 {
        return fail_out(g, &mut out, ReasonCode::BuildNotReproducible, format!("judge-run prepare is nondeterministic ({p1} vs {p2})"));
    }
    let (public_archive, public_tree) = r.upload_tree("public_artifacts", &prepared[0].public_dir.clone(), &prepared[0].tree.clone(), true)?;
    g.note(format!(
        "prepare {} ms, public dir {} bytes, TreeDigest {public_tree}",
        prepared[0].outcome.wall_ns / 1_000_000,
        prepared[0].tree.total_bytes()
    ));

    let formal_tree = match &manifest.formal {
        Some(f) => arena_archive::tree_from_dir(&x.root.join(&f.lean_project), &arena_archive::Limits::default())?.digest(),
        None => arena_archive::Tree::default().digest(),
    };
    let file = |p: &str| a.tree.files[p].digest.clone();
    out.build = Some(BuildOutputs {
        prepare: file(&manifest.entry.prepare),
        prove: file(&manifest.entry.prove),
        verify: file(&manifest.entry.verify),
        bundle: bundle_tree,
        public_artifacts: public_tree,
        formal_tree,
        certificate_decl: manifest.formal.as_ref().map(|f| f.certificate.clone()).unwrap_or_default(),
        toolchain_image: Some(tc_digest.to_string()),
        build_ns: Some(a.wall_ns),
        bundle_archive: Some(bundle_archive),
        public_archive: Some(public_archive),
    });
    out.gates.push(g.finish(GateStatus::Pass, true));
    Ok(out)
}

fn build_spec(j: &BuildJob, pkg: &Path, rootfs: &Rootfs, mounts: &[Mount], r: &JobRun<'_>, out_dir: &Path) -> SandboxSpec {
    let m = &j.manifest;
    let mut s = SandboxSpec::new(vec![format!("/scratch/work/{}", m.build.recipe)]);
    s.rootfs = rootfs.clone();
    s.ro_mounts.push(Mount { host: pkg.to_path_buf(), guest: "/in/pkg".into() });
    s.ro_mounts.extend(mounts.iter().cloned());
    s.copy_in.push(CopyIn { from_guest: "/in/pkg".into(), to_scratch: "work".into() });
    s.cwd = "/scratch/work".into();
    s.env.push(("SOURCE_DATE_EPOCH".into(), "0".into()));
    s.env.push(("CARGO_NET_OFFLINE".into(), "true".into()));
    s.env.push(("ARENA_STAGE".into(), "build".into()));
    if let Some(p) = &r.ctx.build.path {
        s.env.push(("PATH".into(), p.clone()));
    }
    s.env.extend(r.ctx.build.env.iter().cloned());
    s.mem_bytes = j.challenge.resource_limits.max_ram_bytes.max(256 << 20);
    s.pids = BUILD_PIDS;
    s.rw_scratch_mb = BUILD_SCRATCH_MB;
    s.wall_timeout = Duration::from_millis(j.challenge.resource_limits.max_build_ms.max(1));
    s.collect = m.build.outputs.iter().map(|o| format!("work/{o}")).collect();
    s.out_dir = Some(out_dir.to_path_buf());
    s.max_output_bytes = MAX_BUNDLE_OUTPUT;
    s
}
