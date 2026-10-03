//! `BUILD_REPRODUCIBLE`: run the recipe offline in the sandbox twice, each
//! time in fresh scratch, and require bit-identical output trees.

use crate::executor::{describe_exit, ExecError, JobRun, StageOut, MAX_PACKAGE_BYTES};
use crate::gate::Gate;
use crate::jobs::BuildJob;
use arena_sandbox::{CopyIn, ExitStatus, Mount, Rootfs, SandboxSpec};
use arena_types::{Digest, GateStatus, ObligationId, ReasonCode};
use std::path::{Path, PathBuf};
use std::time::Duration;

/// Identify the toolchain the build ran against.
fn toolchain(r: &JobRun<'_>, j: &BuildJob) -> Result<(Rootfs, Digest, Vec<Mount>), ExecError> {
    match &j.toolchain_image {
        Some(d) => {
            let dir = r
                .ctx
                .build
                .images_dir
                .as_ref()
                .map(|p| p.join(d.hex()))
                .filter(|p| p.is_dir())
                .ok_or_else(|| ExecError::Infra(format!("toolchain image {d} not available on this worker")))?;
            let t = arena_archive::tree_from_dir(&dir, &arena_archive::Limits { max_expanded_bytes: 64 << 30, max_entries: 5_000_000, ..Default::default() })
                .map_err(|e| ExecError::Infra(format!("toolchain image {d}: {e}")))?;
            if &t.digest() != d {
                return Err(ExecError::Infra(format!("toolchain image dir for {d} does not match its digest")));
            }
            Ok((Rootfs::Image { path: dir, digest: d.clone() }, d.clone(), vec![]))
        }
        None => {
            // Host-dev toolchain: identified by a digest of its description.
            // Not a pinned image; only meaningful for DEMO-tier runs.
            let os = std::fs::read_to_string("/etc/os-release").unwrap_or_default();
            let mounts: Vec<(String, String)> =
                r.ctx.build.mounts.iter().map(|m| (m.host.display().to_string(), m.guest.clone())).collect();
            let desc = serde_json::json!({
                "kind": "host-dev",
                "os_release": os,
                "mounts": mounts,
                "path": r.ctx.build.path,
            });
            let d = arena_types::sha256_digest(&desc).map_err(|e| ExecError::Infra(e.to_string()))?;
            Ok((Rootfs::HostDev, d, r.ctx.build.mounts.clone()))
        }
    }
}

struct BuildRun {
    root: PathBuf,
    tree: arena_archive::Tree,
}

pub fn run(r: &mut JobRun<'_>, j: &BuildJob) -> Result<StageOut, ExecError> {
    let mut g = Gate::start(ObligationId::BuildReproducible);
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    let bytes = r.fetch(&j.package, MAX_PACKAGE_BYTES)?;
    let pkg_dir = r.fresh("pkg");
    let x = match arena_archive::ingest_bytes(&bytes, &pkg_dir, &arena_archive::Limits::default()) {
        Ok(x) => x,
        Err(arena_archive::ArchiveError::Unsafe(m)) => {
            g.fail(ReasonCode::ArchiveUnsafe, m);
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        Err(e) => return Err(e.into()),
    };
    let manifest = match arena_archive::validate_package(&x.root, &x.tree) {
        Ok(m) => m,
        Err(arena_archive::PackageError::Io(e)) => return Err(e.into()),
        Err(e) => {
            g.fail(ReasonCode::ManifestInvalid, e.to_string());
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
    };
    let layout = r.ctx.sandbox.layout();
    if !layout.flexible_scratch || layout.scratch != arena_sandbox::SCRATCH {
        return Err(ExecError::Infra(format!(
            "sandbox backend {} cannot run builds yet (needs copy-in of the package into scratch)",
            r.ctx.sandbox.name()
        )));
    }
    let (rootfs, tc_digest, mounts) = toolchain(r, j)?;
    r.record("toolchain_image", tc_digest.clone(), true, false);
    g.evidence("toolchain_image", tc_digest, true);

    let mut builds: Vec<BuildRun> = vec![];
    for i in 1..=2 {
        let out_dir = r.fresh("build-out");
        let spec = build_spec(j, &manifest, &x.root, &rootfs, &mounts, r, &out_dir);
        let o = r.run(&spec)?;
        let log = [&b"--- stdout ---\n"[..], &o.stdout_trunc, b"\n--- stderr ---\n", &o.stderr_trunc].concat();
        r.upload(&format!("build_log_{i}"), &log, false)?;
        if !o.exit.success() {
            let reason = match o.exit {
                ExitStatus::TimedOut => ReasonCode::Timeout,
                ExitStatus::OomKilled => ReasonCode::ResourceLimit,
                _ => ReasonCode::BuildFailed,
            };
            if reason != ReasonCode::BuildFailed {
                g.fail(ReasonCode::BuildFailed, format!("build {i} {}", describe_exit(&o)));
            }
            g.fail(reason, format!("build {i} {}", describe_exit(&o)));
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        if let Some(e) = &o.output_error {
            g.fail(ReasonCode::BuildFailed, format!("build {i} outputs rejected: {e}"));
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        let root = out_dir.join("work");
        std::fs::create_dir_all(&root)?;
        let tree = arena_archive::tree_from_dir(&root, &arena_archive::Limits { max_expanded_bytes: j.limits.max_output_bytes, ..Default::default() })?;
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
            g.fail(ReasonCode::BuildFailed, format!("build {i} did not produce {}", missing.join(", ")));
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        builds.push(BuildRun { root, tree });
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
        g.fail(ReasonCode::BuildNotReproducible, format!("two builds differ ({da} vs {db}); differing paths: {}", diff.join(", ")));
    } else {
        g.note(format!("two independent builds produced identical trees {da}"));
    }
    let (bundle, tree) = r.upload_tree("bundle", &a.root.clone(), &a.tree.clone(), false)?;
    g.evidence("bundle", bundle, false);
    g.evidence("bundle_tree", tree, true);
    // Per-entry-point digests (VerifiedSurface inputs for the server).
    for (name, p) in [("prepare", &manifest.entry.prepare), ("prove", &manifest.entry.prove), ("verify", &manifest.entry.verify)] {
        let d = a.tree.files[p].digest.clone();
        r.record(&format!("entry_{name}"), d, true, false);
    }
    out.manifest = Some(manifest);
    out.gates.push(g.finish(GateStatus::Pass, true));
    Ok(out)
}

fn build_spec(
    j: &BuildJob,
    m: &arena_types::CandidateManifest,
    pkg: &Path,
    rootfs: &Rootfs,
    mounts: &[Mount],
    r: &JobRun<'_>,
    out_dir: &Path,
) -> SandboxSpec {
    let mut s = SandboxSpec::new(vec![format!("/scratch/work/{}", m.build.recipe)]);
    s.rootfs = rootfs.clone();
    s.ro_mounts.push(Mount { host: pkg.to_path_buf(), guest: "/in/pkg".into() });
    s.ro_mounts.extend(mounts.iter().cloned());
    s.copy_in.push(CopyIn { from_guest: "/in/pkg".into(), to_scratch: "work".into() });
    s.cwd = "/scratch/work".into();
    s.env.push(("SOURCE_DATE_EPOCH".into(), j.source_date_epoch.to_string()));
    s.env.push(("CARGO_NET_OFFLINE".into(), "true".into()));
    s.env.push(("ARENA_STAGE".into(), "build".into()));
    if let Some(p) = &r.ctx.build.path {
        s.env.push(("PATH".into(), p.clone()));
    }
    s.env.extend(r.ctx.build.env.iter().cloned());
    s.mem_bytes = j.limits.mem_bytes;
    s.pids = j.limits.pids;
    s.rw_scratch_mb = j.limits.scratch_mb;
    s.wall_timeout = Duration::from_millis(j.limits.max_build_ms.max(1));
    s.collect = m.build.outputs.iter().map(|o| format!("work/{o}")).collect();
    s.out_dir = Some(out_dir.to_path_buf());
    s.max_output_bytes = j.limits.max_output_bytes;
    s
}
