//! Host-side supervisor: prepares the per-run job directory, starts the
//! delivery container (which runs jailer + Firecracker), applies a backstop
//! deadline, decodes the guest's output device and cleans up.

use crate::images::{self, TreeLimits};
use crate::native::*;
use arena_fc_proto::{
    self as proto, DriveRateLimit, GuestJob, GuestMount, GuestStatus, MountKind, ShimDrive,
    ShimJob, ShimResult, ShimStatus,
};
use arena_sandbox::{Diagnostics, Exit, InfraError, LimitEnforcement, SandboxOutcome};
use arena_types::Digest;
use sha2::{Digest as _, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufReader, Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Capabilities the delivery container needs (see docs/ISOLATION.md for the
/// per-capability justification; each was verified necessary by removing it).
pub const CONTAINER_CAPS: &[&str] = &[
    "SYS_ADMIN",
    "MKNOD",
    "CHOWN",
    "SETUID",
    "SETGID",
    "DAC_OVERRIDE",
];

/// Environment variable names a spec may set.
pub const ENV_ALLOWLIST: &[&str] = &[
    "PATH",
    "HOME",
    "LANG",
    "LC_ALL",
    "TZ",
    "TMPDIR",
    "RUST_BACKTRACE",
    "RUST_LOG",
    "RAYON_NUM_THREADS",
    "OMP_NUM_THREADS",
    // formal checking / native-lean (Lean runtime)
    "LEAN_PATH",
    "LEAN_ABORT_ON_PANIC",
    "ARENA_LEAN_SYSROOT",
];

#[derive(Clone, Debug)]
pub struct FirecrackerConfig {
    pub docker_bin: PathBuf,
    /// Delivery image (pin by id, `sha256:...`).
    pub runner_image: String,
    pub seccomp_profile: PathBuf,
    pub kernel: PathBuf,
    pub rootfs: PathBuf,
    /// Job directories and the bundle image cache live here. Must be on the
    /// same filesystem as kernel/rootfs to hardlink instead of copying.
    pub work_root: PathBuf,
    /// Range of host uids used for the jailed Firecracker (one per run).
    pub vmm_uid_base: u32,
    pub vmm_uid_count: u32,
    /// Guest RAM beyond `mem_bytes` (guest kernel, init, page tables).
    pub guest_overhead_mib: u64,
    /// Host cgroup headroom over guest RAM for the VMM process itself.
    pub vmm_overhead_mib: u64,
    pub boot_timeout: Duration,
    pub collect_timeout: Duration,
    /// Extra slack before the host forcibly kills the container.
    pub backstop_grace: Duration,
    pub max_output_files: u32,
    pub max_output_bytes: u64,
    pub tree_limits: TreeLimits,
    pub serial_cap_bytes: u64,
    pub max_vcpus: u32,
    pub max_scratch_mb: u64,
    /// Capabilities granted to the delivery container (default
    /// `CONTAINER_CAPS`; overridable only for experiments).
    pub container_caps: Vec<String>,
    /// Firecracker token-bucket limits applied to every data drive (rootfs,
    /// root image, bundles, scratch, output). `None` disables limiting.
    pub drive_rate_limit: Option<DriveRateLimit>,
    /// Size cap of the content-addressed image cache (bundles + root
    /// images); least-recently-used entries are evicted past it.
    pub cache_max_bytes: u64,
    /// Limits for staging a candidate root image (toolchains are large).
    pub root_image_limits: TreeLimits,
    /// Host-side hard timeout slack over the guest-enforced wall timeout.
    pub host_timeout_grace: Duration,
}

impl FirecrackerConfig {
    /// Default layout produced by `deploy/images/*` under `deps`
    /// (`$ARENA_FC_DEPS`, default `/data/illia/nearproof-deps/firecracker`).
    pub fn from_deps_dir(deps: &Path, work_root: &Path) -> Result<Self, InfraError> {
        let image = fs::read_to_string(deps.join("images/fc-runner.image"))
            .map_err(|e| {
                InfraError::Unavailable(format!(
                    "runner image id (run deploy/images/fc-runner/build.sh): {e}"
                ))
            })?
            .trim()
            .to_string();
        Ok(FirecrackerConfig {
            docker_bin: PathBuf::from("docker"),
            runner_image: image,
            seccomp_profile: deps.join("images/fc-runner-seccomp.json"),
            kernel: fs::canonicalize(deps.join("kernel/vmlinux"))?,
            rootfs: fs::canonicalize(deps.join("images/rootfs.ext4"))?,
            work_root: work_root.to_path_buf(),
            vmm_uid_base: 900_000,
            vmm_uid_count: 50_000,
            guest_overhead_mib: 128,
            vmm_overhead_mib: 96,
            boot_timeout: Duration::from_secs(20),
            collect_timeout: Duration::from_secs(120),
            backstop_grace: Duration::from_secs(30),
            max_output_files: 100_000,
            max_output_bytes: 4 << 30,
            tree_limits: TreeLimits::default(),
            serial_cap_bytes: 64 * 1024,
            max_vcpus: 32,
            max_scratch_mb: 64 * 1024,
            container_caps: CONTAINER_CAPS.iter().map(|c| c.to_string()).collect(),
            drive_rate_limit: Some(DriveRateLimit {
                bytes_per_s: 512 << 20,
                ops_per_s: 20_000,
                burst_bytes: 256 << 20,
            }),
            cache_max_bytes: 32 << 30,
            root_image_limits: TreeLimits {
                allow_symlinks: false,
                max_entries: 2_000_000,
                max_bytes: 32 << 30,
            },
            host_timeout_grace: Duration::from_secs(2),
        })
    }

    pub fn from_env(work_root: &Path) -> Result<Self, InfraError> {
        let deps = std::env::var_os("ARENA_FC_DEPS")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("/data/illia/nearproof-deps/firecracker"));
        Self::from_deps_dir(&deps, work_root)
    }
}

pub struct FirecrackerSandbox {
    cfg: FirecrackerConfig,
    kernel_digest: Digest,
    rootfs_digest: Digest,
    host_uid: u32,
    host_gid: u32,
    ncpus: u32,
}

fn random_hex(nbytes: usize) -> io::Result<String> {
    let mut b = vec![0u8; nbytes];
    File::open("/dev/urandom")?.read_exact(&mut b)?;
    Ok(hex::encode(b))
}

fn backend(s: impl Into<String>) -> InfraError {
    InfraError::Backend(s.into())
}

/// Removes the job directory on drop (best effort, with a container-side
/// cleanup if root-owned debris was left by a crashed run).
struct JobDir<'a> {
    path: PathBuf,
    sb: &'a FirecrackerSandbox,
}

impl Drop for JobDir<'_> {
    fn drop(&mut self) {
        if fs::remove_dir_all(&self.path).is_err() {
            let _ = self.sb.container_cleanup(&self.path);
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}

impl FirecrackerSandbox {
    /// Verifies the backend prerequisites and hashes kernel + rootfs.
    pub fn new(cfg: FirecrackerConfig) -> Result<Self, InfraError> {
        let out = Command::new(&cfg.docker_bin)
            .args(["image", "inspect", "--format", "{{.Id}}", &cfg.runner_image])
            .output()
            .map_err(|e| InfraError::Unavailable(format!("docker: {e}")))?;
        if !out.status.success() {
            return Err(InfraError::Unavailable(format!(
                "runner image {} missing: {}",
                cfg.runner_image,
                String::from_utf8_lossy(&out.stderr).trim()
            )));
        }
        if !cfg.seccomp_profile.is_file() {
            return Err(InfraError::Unavailable(format!(
                "seccomp profile {} missing",
                cfg.seccomp_profile.display()
            )));
        }
        if !Path::new("/dev/kvm").exists() {
            return Err(InfraError::Unavailable("/dev/kvm not present".into()));
        }
        let kernel_digest = images::file_digest(&cfg.kernel)?;
        let rootfs_digest = images::file_digest(&cfg.rootfs)?;
        fs::create_dir_all(cfg.work_root.join("jobs"))?;
        fs::create_dir_all(cfg.work_root.join("cache"))?;
        let ncpus = std::thread::available_parallelism()
            .map(|n| n.get() as u32)
            .unwrap_or(1);
        let (host_uid, host_gid) = unsafe { (libc::getuid(), libc::getgid()) };
        Ok(FirecrackerSandbox {
            cfg,
            kernel_digest,
            rootfs_digest,
            host_uid,
            host_gid,
            ncpus,
        })
    }

    pub fn config(&self) -> &FirecrackerConfig {
        &self.cfg
    }
    pub fn kernel_digest(&self) -> &Digest {
        &self.kernel_digest
    }
    pub fn rootfs_digest(&self) -> &Digest {
        &self.rootfs_digest
    }

    fn validate(&self, spec: &RunRequest) -> Result<(), InfraError> {
        let bad = |s: String| Err(InfraError::InvalidSpec(s));
        if spec.network.is_some() {
            return bad("network access is never available".into());
        }
        if spec.rootfs_digest != self.rootfs_digest {
            return bad(format!(
                "rootfs digest {} != installed {}",
                spec.rootfs_digest, self.rootfs_digest
            ));
        }
        if spec.argv.is_empty() || spec.argv.iter().any(|a| a.contains('\0')) {
            return bad("argv empty or contains NUL".into());
        }
        for (k, v) in &spec.env {
            if !ENV_ALLOWLIST.contains(&k.as_str())
                && !arena_sandbox::ENV_ALLOWLIST.contains(&k.as_str())
            {
                return bad(format!("env var {k} not in allowlist"));
            }
            if v.contains('\0') {
                return bad(format!("env var {k} contains NUL"));
            }
        }
        if spec.cpu_set.len() as u32 > self.cfg.max_vcpus
            || spec.cpu_set.iter().any(|c| *c >= self.ncpus)
        {
            return bad(format!(
                "cpu_set {:?} invalid on a {}-cpu host",
                spec.cpu_set, self.ncpus
            ));
        }
        let mut cs = spec.cpu_set.clone();
        cs.sort();
        cs.dedup();
        if cs.len() != spec.cpu_set.len() {
            return bad("duplicate cpus in cpu_set".into());
        }
        if spec.mem_bytes < (16 << 20) || spec.mem_bytes > (512u64 << 30) {
            return bad(format!("mem_bytes {} out of range", spec.mem_bytes));
        }
        if spec.pids == 0 || spec.pids > 1 << 20 {
            return bad("pids out of range".into());
        }
        if spec.rw_scratch_mb < 8 || spec.rw_scratch_mb > self.cfg.max_scratch_mb {
            return bad(format!("rw_scratch_mb {} out of range", spec.rw_scratch_mb));
        }
        if spec.wall_timeout.is_zero() {
            return bad("zero wall_timeout".into());
        }
        if spec.ro_mounts.len() > proto::MAX_MOUNTS {
            return bad("too many ro_mounts".into());
        }
        let mut guest_paths: Vec<&str> = Vec::new();
        let overlaps = |a: &str, b: &str| {
            a == b || a.starts_with(&format!("{b}/")) || b.starts_with(&format!("{a}/"))
        };
        for m in &spec.ro_mounts {
            let g = m.guest_path.as_str();
            if !proto::GUEST_MOUNT_PREFIXES.iter().any(|p| g.starts_with(p)) {
                return bad(format!(
                    "guest path {g:?} must be under {:?}",
                    proto::GUEST_MOUNT_PREFIXES
                ));
            }
            abs_guest(g)?;
            if !g
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"._-/+".contains(&b))
            {
                return bad(format!("guest path {g:?} has unsupported characters"));
            }
            if overlaps(g, proto::GUEST_SCRATCH) || guest_paths.iter().any(|p| overlaps(p, g)) {
                return bad(format!("guest path {g:?} overlaps another mount"));
            }
            guest_paths.push(g);
        }
        for r in &spec.rw_dirs {
            let g = r.guest_path.as_str();
            if !proto::GUEST_MOUNT_PREFIXES.iter().any(|p| g.starts_with(p)) {
                return bad(format!(
                    "rw path {g:?} must be under {:?}",
                    proto::GUEST_MOUNT_PREFIXES
                ));
            }
            abs_guest(g)?;
            if overlaps(g, proto::GUEST_SCRATCH) || guest_paths.iter().any(|p| overlaps(p, g)) {
                return bad(format!("rw path {g:?} overlaps another mount"));
            }
            if !fs::symlink_metadata(&r.host_dir)
                .map(|m| m.is_dir())
                .unwrap_or(false)
            {
                return bad(format!(
                    "rw dir {} is not a directory",
                    r.host_dir.display()
                ));
            }
            guest_paths.push(g);
        }
        if spec.rw_dirs.len() > 4 {
            return bad("too many rw dirs".into());
        }
        abs_guest(&spec.cwd)?;
        for (from, to) in &spec.copy_in {
            abs_guest(from)?;
            rel_scratch(to)?;
        }
        for p in spec.scratch_dirs.iter().chain(&spec.collect) {
            rel_scratch(p)?;
        }
        if spec.collect.len() > 256 || spec.scratch_dirs.len() > 256 || spec.copy_in.len() > 64 {
            return bad("too many collect/scratch_dirs/copy_in entries".into());
        }
        Ok(())
    }

    /// Ensure the root image for `img` is in the cache (verifying its digest
    /// on a staged copy when building it).
    fn prepare_root_image(&self, img: &RootImage, staging: &Path) -> Result<PathBuf, InfraError> {
        let cached = self
            .cfg
            .work_root
            .join("cache")
            .join(format!("root-{}.ext4", img.digest.hex()));
        if cached.exists() {
            images::touch(&cached);
            return Ok(cached);
        }
        let st_dir = staging.join(format!("root-{}", random_hex(6)?));
        let st = images::stage_tree(&img.dir, &st_dir, &self.cfg.root_image_limits)?;
        let lim = arena_archive::Limits {
            max_expanded_bytes: self.cfg.root_image_limits.max_bytes,
            max_entries: self.cfg.root_image_limits.max_entries,
            ..Default::default()
        };
        let got = arena_archive::tree_from_dir(&st_dir, &lim)
            .map_err(|e| InfraError::InvalidSpec(format!("root image {}: {e}", img.dir.display())))?
            .digest();
        if got != img.digest {
            return Err(InfraError::InvalidSpec(format!(
                "root image {} has digest {got}, expected {}",
                img.dir.display(),
                img.digest
            )));
        }
        let tmp = self.cfg.work_root.join("cache").join(format!(
            ".root-{}.{}.tmp",
            img.digest.hex(),
            random_hex(4)?
        ));
        images::build_ro_image(&st, &tmp)?;
        fs::rename(&tmp, &cached)?;
        let _ = fs::remove_dir_all(&st_dir);
        images::evict_cache(&self.cfg.work_root.join("cache"), self.cfg.cache_max_bytes);
        Ok(cached)
    }

    /// Stage + hash a read-only mount; returns (cached image path, kind).
    fn prepare_mount(
        &self,
        m: &RoMount,
        staging: &Path,
        allow_symlinks: bool,
    ) -> Result<(PathBuf, MountKind), InfraError> {
        let md = fs::symlink_metadata(&m.host_path)
            .map_err(|e| InfraError::InvalidSpec(format!("{}: {e}", m.host_path.display())))?;
        let (src_dir, kind, tmp_src);
        if md.is_dir() {
            src_dir = m.host_path.clone();
            kind = MountKind::Dir;
            tmp_src = None;
        } else if md.is_file() {
            let name = m
                .host_path
                .file_name()
                .and_then(|n| n.to_str())
                .filter(|n| {
                    proto::validate_rel_path(n).is_ok()
                        && n.bytes()
                            .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
                })
                .ok_or_else(|| {
                    InfraError::InvalidSpec(format!(
                        "{}: unsupported file name",
                        m.host_path.display()
                    ))
                })?
                .to_string();
            // wrap the single file into a one-entry tree
            let wrap = staging.join(format!("wrap-{}", random_hex(6)?));
            fs::create_dir(&wrap)?;
            let mut inp = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW)
                .open(&m.host_path)?;
            let mut out = File::create(wrap.join(&name))?;
            io::copy(&mut inp, &mut out)?;
            src_dir = wrap.clone();
            kind = MountKind::File { name };
            tmp_src = Some(wrap);
        } else {
            return Err(InfraError::InvalidSpec(format!(
                "{}: not a file or directory",
                m.host_path.display()
            )));
        }
        let st_dir = staging.join(format!("tree-{}", random_hex(6)?));
        let lim = TreeLimits {
            allow_symlinks,
            ..self.cfg.tree_limits.clone()
        };
        let st = images::stage_tree(&src_dir, &st_dir, &lim)?;
        if let Some(t) = tmp_src {
            let _ = fs::remove_dir_all(t);
        }
        let key = match &kind {
            MountKind::Dir => format!("dir-{}", st.digest.hex()),
            MountKind::File { name } => format!(
                "file-{}-{}",
                hex::encode(Sha256::digest(name.as_bytes())),
                st.digest.hex()
            ),
        };
        let cached = self.cfg.work_root.join("cache").join(format!("{key}.ext4"));
        if cached.exists() {
            images::touch(&cached);
        } else {
            let tmp = self
                .cfg
                .work_root
                .join("cache")
                .join(format!(".{key}.{}.tmp", random_hex(4)?));
            images::build_ro_image(&st, &tmp)?;
            fs::rename(&tmp, &cached)?; // atomic; concurrent builders produce equivalent images
            images::evict_cache(&self.cfg.work_root.join("cache"), self.cfg.cache_max_bytes);
        }
        let _ = fs::remove_dir_all(&st_dir);
        Ok((cached, kind))
    }

    fn container_name(id: &str) -> String {
        format!("arena-fc-{id}")
    }

    fn container_cleanup(&self, jobdir: &Path) -> Result<(), InfraError> {
        let st = Command::new(&self.cfg.docker_bin)
            .args([
                "run",
                "--rm",
                "--network",
                "none",
                "--cap-drop",
                "ALL",
                "--cap-add",
                "CHOWN",
                "--security-opt",
                "no-new-privileges",
            ])
            .arg("-v")
            .arg(format!("{}:/job", jobdir.display()))
            .arg(&self.cfg.runner_image)
            .args([
                "cleanup",
                "/job",
                &self.host_uid.to_string(),
                &self.host_gid.to_string(),
            ])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()?;
        if !st.success() {
            return Err(backend("container cleanup failed"));
        }
        Ok(())
    }

    /// Start the container and wait for it with a backstop deadline.
    fn run_container(
        &self,
        id: &str,
        jobdir: &Path,
        job: &ShimJob,
        deadline: Duration,
    ) -> Result<(u64, String), InfraError> {
        let mem_limit = job.vmm_mem_max_bytes + (64 << 20);
        let mut cmd = Command::new(&self.cfg.docker_bin);
        cmd.args(["run", "--rm", "--name", &Self::container_name(id)])
            .args([
                "--network",
                "none",
                "--device",
                "/dev/kvm",
                "--cap-drop",
                "ALL",
            ]);
        for c in &self.cfg.container_caps {
            cmd.args(["--cap-add", c]);
        }
        cmd.args([
            "--security-opt",
            "no-new-privileges",
            "--security-opt",
            "apparmor=unconfined",
        ])
        .arg("--security-opt")
        .arg(format!("seccomp={}", self.cfg.seccomp_profile.display()))
        .args([
            "--read-only",
            "--cgroupns",
            "private",
            "--ipc",
            "none",
            "--user",
            "0:0",
            "--log-driver",
            "none",
        ])
        .args([
            "--memory",
            &mem_limit.to_string(),
            "--memory-swap",
            &mem_limit.to_string(),
        ])
        .args(["--pids-limit", "128", "--ulimit", "core=0"]);
        if let Some(cs) = &job.cpuset {
            cmd.args(["--cpuset-cpus", cs]);
        }
        cmd.arg("-v")
            .arg(format!("{}:/job", jobdir.display()))
            .arg(&self.cfg.runner_image)
            .args(["run", "/job"])
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let t0 = Instant::now();
        let mut child = cmd
            .spawn()
            .map_err(|e| InfraError::Unavailable(format!("docker run: {e}")))?;
        let mut so = child.stdout.take().unwrap();
        let mut se = child.stderr.take().unwrap();
        let t_out = std::thread::spawn(move || {
            let mut v = Vec::new();
            let _ = (&mut so).take(64 * 1024).read_to_end(&mut v);
            let _ = io::copy(&mut so, &mut io::sink());
            v
        });
        let t_err = std::thread::spawn(move || {
            let mut v = Vec::new();
            let _ = (&mut se).take(64 * 1024).read_to_end(&mut v);
            let _ = io::copy(&mut se, &mut io::sink());
            v
        });
        let mut killed = false;
        let status = loop {
            if let Some(st) = child.try_wait()? {
                break st;
            }
            if !killed && t0.elapsed() > deadline {
                let _ = Command::new(&self.cfg.docker_bin)
                    .args(["kill", &Self::container_name(id)])
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .status();
                killed = true;
            }
            std::thread::sleep(Duration::from_millis(2));
        };
        let total_ns = t0.elapsed().as_nanos() as u64;
        let mut msg = String::from_utf8_lossy(&t_out.join().unwrap_or_default()).into_owned();
        msg.push_str(&String::from_utf8_lossy(&t_err.join().unwrap_or_default()));
        if killed {
            return Err(backend(format!(
                "backstop deadline hit; container killed: {msg}"
            )));
        }
        // shim exits 1 on supervisor error but still writes result.json
        if !status.success() && !jobdir.join(proto::SHIM_RESULT_FILE).exists() {
            return Err(backend(format!(
                "container failed ({status}): {}",
                msg.trim()
            )));
        }
        Ok((total_ns, msg))
    }

    fn materialize_outputs(
        &self,
        r: &mut dyn Read,
        out_dir: &Path,
        rw_hosts: &[PathBuf],
        limits: &proto::DecodeLimits,
    ) -> Result<(Vec<(String, Digest)>, proto::CollectSummary), InfraError> {
        let mut outputs = Vec::new();
        let mut rw_violations = Vec::new();
        let rw_prefix = format!("{}/", proto::RW_SCRATCH_DIR);
        let res = proto::decode_files(r, limits, |path, exec, _size, rd| {
            let mode = if exec { 0o755 } else { 0o644 };
            let (mut f, is_rw) = if let Some(rest) = path.strip_prefix(&rw_prefix) {
                // write back into a judge-owned host dir without following
                // any symlink that is already there
                let (idx, rel) = rest.split_once('/').unwrap_or((rest, ""));
                let host = idx.parse::<usize>().ok().and_then(|i| rw_hosts.get(i));
                match (host, rel.is_empty()) {
                    (Some(h), false) => match safe_replace(h, rel, mode) {
                        Ok(f) => (f, true),
                        Err(e) => {
                            rw_violations.push(format!("{path}: {e}"));
                            io::copy(rd, &mut io::sink())?;
                            return Ok(());
                        }
                    },
                    _ => {
                        rw_violations.push(format!("{path}: not under a read-write dir"));
                        io::copy(rd, &mut io::sink())?;
                        return Ok(());
                    }
                }
            } else {
                let dst = out_dir.join(path);
                if let Some(parent) = dst.parent() {
                    fs::create_dir_all(parent)?;
                }
                let f = OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .custom_flags(libc::O_NOFOLLOW)
                    .mode(mode)
                    .open(&dst)?;
                (f, false)
            };
            let mut h = Sha256::new();
            let mut buf = vec![0u8; 1 << 20];
            loop {
                let n = rd.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                h.update(&buf[..n]);
                f.write_all(&buf[..n])?;
            }
            let d =
                Digest::try_from(format!("sha256:{}", hex::encode(h.finalize()))).expect("digest");
            if !is_rw {
                outputs.push((path.to_string(), d));
            }
            Ok(())
        });
        match res {
            Ok(mut summary) => {
                outputs.sort();
                if !rw_violations.is_empty() {
                    summary.complete = false;
                    summary.violations.extend(rw_violations);
                }
                Ok((outputs, summary))
            }
            Err(proto::DecodeError::Malformed(m)) => Err(InfraError::GuestProtocol(m)),
            Err(proto::DecodeError::Sink(e)) => Err(InfraError::Io(e)),
        }
    }

    fn run_inner(&self, spec: &RunRequest) -> Result<SandboxOutcome, InfraError> {
        self.validate(spec)?;
        // output dir: must be absent or empty
        match fs::read_dir(&spec.out_dir) {
            Ok(mut rd) => {
                if rd.next().is_some() {
                    return Err(InfraError::InvalidSpec(format!(
                        "out_dir {} not empty",
                        spec.out_dir.display()
                    )));
                }
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => fs::create_dir_all(&spec.out_dir)?,
            Err(e) => return Err(e.into()),
        }

        let id = format!("r{}", random_hex(8)?);
        let nonce = random_hex(16)?;
        let jobdir = self.cfg.work_root.join("jobs").join(&id);
        fs::create_dir(&jobdir)?;
        let guard = JobDir {
            path: jobdir.clone(),
            sb: self,
        };
        let input = jobdir.join(proto::SHIM_INPUT_DIR);
        let staging = jobdir.join("staging");
        fs::create_dir(&input)?;
        fs::create_dir(&staging)?;

        // kernel + rootfs (shared, read-only, verified at startup)
        images::link_or_copy(&self.cfg.kernel, &input.join("vmlinux"))?;
        images::link_or_copy(&self.cfg.rootfs, &input.join("rootfs.ext4"))?;
        let mut drives = vec![
            ShimDrive {
                drive_id: "rootfs".into(),
                file: "rootfs.ext4".into(),
                read_only: true,
                is_root: true,
                chown_to_vmm: false,
                rate_limit: self.cfg.drive_rate_limit,
            },
            ShimDrive {
                drive_id: "ctl".into(),
                file: "ctl.img".into(),
                read_only: true,
                is_root: false,
                chown_to_vmm: false,
                rate_limit: None,
            },
            ShimDrive {
                drive_id: "out".into(),
                file: "out.img".into(),
                read_only: false,
                is_root: false,
                chown_to_vmm: true,
                rate_limit: self.cfg.drive_rate_limit,
            },
            ShimDrive {
                drive_id: "scratch".into(),
                file: "scratch.img".into(),
                read_only: false,
                is_root: false,
                chown_to_vmm: true,
                rate_limit: self.cfg.drive_rate_limit,
            },
        ];
        let mut mounts = Vec::new();
        for (i, m) in spec.ro_mounts.iter().enumerate() {
            let (img, kind) = self.prepare_mount(m, &staging, spec.allow_mount_symlinks)?;
            let file = format!("ro{i}.ext4");
            images::link_or_copy(&img, &input.join(&file))?;
            drives.push(ShimDrive {
                drive_id: format!("ro{i}"),
                file,
                read_only: true,
                is_root: false,
                chown_to_vmm: false,
                rate_limit: self.cfg.drive_rate_limit,
            });
            mounts.push(GuestMount {
                dev_index: proto::FIRST_MOUNT_DEV_INDEX + i as u32,
                guest_path: m.guest_path.clone(),
                kind,
            });
        }
        let root_dev_index = match &spec.root_image {
            Some(img) => {
                let cached = self.prepare_root_image(img, &staging)?;
                images::link_or_copy(&cached, &input.join("rootimg.ext4"))?;
                drives.push(ShimDrive {
                    drive_id: "rootimg".into(),
                    file: "rootimg.ext4".into(),
                    read_only: true,
                    is_root: false,
                    chown_to_vmm: false,
                    rate_limit: self.cfg.drive_rate_limit,
                });
                Some(proto::FIRST_MOUNT_DEV_INDEX + spec.ro_mounts.len() as u32)
            }
            None => None,
        };
        // read-write dirs: seed images (uncached; contents change every run)
        let mut rw_dirs = Vec::new();
        for (i, r) in spec.rw_dirs.iter().enumerate() {
            let empty = fs::read_dir(&r.host_dir)?.next().is_none();
            let dev_index = if empty {
                None
            } else {
                let st_dir = staging.join(format!("rw{i}"));
                let lim = TreeLimits {
                    allow_symlinks: true,
                    ..self.cfg.tree_limits.clone()
                };
                let st = images::stage_tree(&r.host_dir, &st_dir, &lim)?;
                let file = format!("rwseed{i}.ext4");
                images::build_ro_image(&st, &input.join(&file))?;
                drives.push(ShimDrive {
                    drive_id: format!("rwseed{i}"),
                    file,
                    read_only: true,
                    is_root: false,
                    chown_to_vmm: false,
                    rate_limit: self.cfg.drive_rate_limit,
                });
                Some(drives.len() as u32 - 1)
            };
            rw_dirs.push(proto::GuestRwDir {
                dev_index,
                guest_path: r.guest_path.clone(),
            });
        }
        let _ = fs::remove_dir_all(&staging);

        // scratch + output devices, fresh per run
        images::build_scratch_image(&input.join("scratch.img"), spec.rw_scratch_mb)?;
        let max_output_bytes = self
            .cfg
            .max_output_bytes
            .min(spec.rw_scratch_mb << 20)
            .min(spec.max_output_bytes);
        let out_dev_bytes =
            (max_output_bytes + (4 << 20) + 2 * proto::STREAM_CAP as u64).div_ceil(4096) * 4096;
        images::build_raw_image(&input.join("out.img"), &[], out_dev_bytes)?;

        let mut env: Vec<(String, String)> = spec.env.clone();
        for (k, v) in [
            ("PATH", "/usr/local/bin:/usr/bin:/bin"),
            ("HOME", proto::GUEST_SCRATCH),
            ("TMPDIR", "/tmp"),
            ("LANG", "C.UTF-8"),
            ("TZ", "UTC"),
        ] {
            if !env.iter().any(|(ek, _)| ek == k) {
                env.push((k.into(), v.into()));
            }
        }
        let guest = GuestJob {
            version: proto::PROTO_VERSION,
            nonce: nonce.clone(),
            argv: spec.argv.clone(),
            env,
            mem_limit_bytes: spec.mem_bytes,
            pids_max: spec.pids,
            nofile: 4096,
            scratch_dev_index: proto::SCRATCH_DEV_INDEX,
            out_dev_index: proto::OUT_DEV_INDEX,
            out_dev_bytes,
            mounts,
            max_output_files: self.cfg.max_output_files,
            max_output_bytes,
            root_dev_index,
            copy_in: spec.copy_in.clone(),
            scratch_dirs: spec.scratch_dirs.clone(),
            cwd: spec.cwd.clone(),
            collect: spec
                .collect
                .iter()
                .cloned()
                .chain((0..spec.rw_dirs.len()).map(|i| format!("{}/{i}", proto::RW_SCRATCH_DIR)))
                .collect(),
            rw_dirs,
            timeout_ms: spec.wall_timeout.as_millis() as u64,
        };
        let ctl = proto::encode_control(&guest);
        if ctl.len() > proto::MAX_CONTROL_LEN {
            return Err(InfraError::InvalidSpec("argv/env too large".into()));
        }
        images::build_raw_image(&input.join("ctl.img"), &ctl, 4096)?;
        fs::set_permissions(
            input.join("ctl.img"),
            std::os::unix::fs::PermissionsExt::from_mode(0o444),
        )?;

        let vcpus = spec.cpu_set.len().max(1) as u32;
        let guest_mem_mib = spec.mem_bytes.div_ceil(1 << 20) + self.cfg.guest_overhead_mib;
        let vmm_uid = self.cfg.vmm_uid_base
            + (u32::from_str_radix(&nonce[..8], 16).unwrap() % self.cfg.vmm_uid_count);
        let cpuset = (!spec.cpu_set.is_empty()).then(|| {
            spec.cpu_set
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(",")
        });
        let shim = ShimJob {
            version: proto::PROTO_VERSION,
            id: id.clone(),
            nonce: nonce.clone(),
            vcpus,
            guest_mem_mib,
            cpuset,
            vmm_mem_max_bytes: (guest_mem_mib + self.cfg.vmm_overhead_mib) << 20,
            vmm_pids_max: 32 + vcpus,
            vmm_fsize_limit: (spec.rw_scratch_mb << 20).max(out_dev_bytes) + (1 << 20),
            kernel_file: "vmlinux".into(),
            boot_args: [
                "console=ttyS0",
                "reboot=k",
                "panic=1",
                "pci=off",
                "nomodule",
                "quiet",
                "loglevel=3",
                "i8042.noaux",
                "i8042.nomux",
                "i8042.dumbkbd",
                "init=/sbin/arena-init",
                "random.trust_cpu=on",
            ]
            .join(" "),
            drives,
            vmm_uid,
            vmm_gid: vmm_uid,
            host_uid: self.host_uid,
            host_gid: self.host_gid,
            boot_timeout_ms: self.cfg.boot_timeout.as_millis() as u64,
            // the guest kills at wall_timeout and still reports; the host
            // kills (losing stdout/stderr) only if the guest fails to
            run_timeout_ms: (spec.wall_timeout
                + self.cfg.host_timeout_grace
                + spec.wall_timeout / 50)
                .as_millis() as u64,
            collect_timeout_ms: self.cfg.collect_timeout.as_millis() as u64,
            serial_cap_bytes: self.cfg.serial_cap_bytes,
        };
        fs::write(
            jobdir.join(proto::SHIM_JOB_FILE),
            serde_json::to_vec_pretty(&shim).unwrap(),
        )?;

        let deadline = self.cfg.boot_timeout
            + spec.wall_timeout
            + self.cfg.collect_timeout
            + self.cfg.backstop_grace;
        let (total_ns, docker_msg) = self.run_container(&id, &jobdir, &shim, deadline)?;
        let res: ShimResult = serde_json::from_slice(
            &fs::read(jobdir.join(proto::SHIM_RESULT_FILE))
                .map_err(|e| backend(format!("no shim result ({e}): {docker_msg}")))?,
        )
        .map_err(|e| backend(format!("bad shim result: {e}")))?;

        let mut diag = Diagnostics {
            backend: "firecracker".into(),
            total_ns,
            boot_ns: res.boot_ns,
            vmm_wall_ns: res.vmm_wall_ns,
            teardown_ns: res.teardown_ns,
            host_oom_kills: res.cgroup.oom_kill,
            serial_tail: res.serial_tail.clone(),
            ..Default::default()
        };
        let host_figures = |exit: Exit, wall_ns: u64, diag: Diagnostics| {
            let mut o = SandboxOutcome::empty(exit, BACKEND_NAME, None);
            o.wall_ns = wall_ns;
            o.cpu_ns = res.cgroup.cpu_usage_ns;
            o.peak_rss_bytes = res.cgroup.memory_peak_bytes;
            o.limits = LimitEnforcement::CgroupV2;
            o.diagnostics = diag;
            o
        };
        match &res.status {
            ShimStatus::Error { error } => return Err(backend(format!("shim: {error}"))),
            ShimStatus::BootTimeout => {
                return Err(backend(format!(
                    "guest did not boot in time; serial: {}",
                    tail(&res.serial_tail)
                )))
            }
            ShimStatus::CollectTimeout => return Err(backend("guest output collection timed out")),
            ShimStatus::TimedOut => {
                return Ok(host_figures(
                    Exit::TimedOut,
                    res.run_wall_ns
                        .unwrap_or(spec.wall_timeout.as_nanos() as u64),
                    diag,
                ));
            }
            ShimStatus::VmmExited { .. } => {}
        }

        // Decode the guest's output device (hostile input, strict limits).
        let out_img = jobdir.join(proto::SHIM_OUT_IMAGE);
        let f = File::open(&out_img).map_err(|e| backend(format!("output image: {e}")))?;
        let mut r = BufReader::with_capacity(1 << 20, f.take(out_dev_bytes));
        let header = match proto::decode_header(&mut r) {
            Ok(h) => h,
            Err(e) => {
                if res.cgroup.oom_kill > 0 {
                    // the VMM itself was OOM-killed by the host cgroup
                    return Ok(host_figures(
                        Exit::OomKilled,
                        res.run_wall_ns.unwrap_or(0),
                        diag,
                    ));
                }
                let what = if res.boot_ns.is_none() {
                    "VM exited before the guest started"
                } else {
                    "no guest report"
                };
                return Err(backend(format!(
                    "{what} ({e}); serial: {}",
                    tail(&res.serial_tail)
                )));
            }
        };
        if header.report.nonce != nonce {
            return Err(InfraError::GuestProtocol("report nonce mismatch".into()));
        }
        let rep = &header.report;
        diag.guest_wall_ns = Some(rep.guest_wall_ns);
        diag.guest_cpu_ns = Some(rep.guest_cpu_ns);
        diag.guest_peak_mem_bytes = Some(rep.guest_peak_mem_bytes);
        diag.stdout_total_bytes = Some(rep.stdout_total_bytes);
        diag.stderr_total_bytes = Some(rep.stderr_total_bytes);
        let mut stderr = header.stderr;
        let exit = match &rep.status {
            GuestStatus::Exited { code } => Exit::Exited(*code),
            GuestStatus::Signaled { signal } => Exit::Signaled(*signal),
            GuestStatus::OomKilled => Exit::OomKilled,
            GuestStatus::TimedOut => Exit::TimedOut,
            GuestStatus::SpawnFailed { error } => {
                stderr =
                    format!("arena: failed to execute {:?}: {error}\n", spec.argv[0]).into_bytes();
                Exit::ExecFailed
            }
            GuestStatus::InitError { error } => {
                return Err(backend(format!("guest init: {error}")))
            }
        };
        let wall_ns = res.run_wall_ns.ok_or_else(|| {
            InfraError::GuestProtocol("guest reported a result without console markers".into())
        })?;
        let limits = proto::DecodeLimits {
            max_files: self.cfg.max_output_files as u64,
            max_total_bytes: max_output_bytes,
        };
        let rw_hosts: Vec<PathBuf> = spec.rw_dirs.iter().map(|r| r.host_dir.clone()).collect();
        let (outputs, summary) =
            match self.materialize_outputs(&mut r, &spec.out_dir, &rw_hosts, &limits) {
                Ok(x) => x,
                Err(e) => {
                    // never leave a partial output tree behind
                    if let Ok(rd) = fs::read_dir(&spec.out_dir) {
                        for e in rd.flatten() {
                            let _ =
                                fs::remove_dir_all(e.path()).or_else(|_| fs::remove_file(e.path()));
                        }
                    }
                    return Err(e);
                }
            };
        diag.output_violations = summary.violations;
        diag.outputs_complete = summary.complete;
        drop(guard);
        let mut o = SandboxOutcome::empty(exit, BACKEND_NAME, None);
        o.wall_ns = wall_ns;
        o.cpu_ns = res.cgroup.cpu_usage_ns;
        o.peak_rss_bytes = res.cgroup.memory_peak_bytes;
        o.max_process_rss_bytes = diag.guest_peak_mem_bytes.unwrap_or(0);
        o.stdout_bytes = diag
            .stdout_total_bytes
            .unwrap_or(header.stdout.len() as u64);
        o.stderr_bytes = diag.stderr_total_bytes.unwrap_or(stderr.len() as u64);
        o.stdout_trunc = header.stdout;
        o.stderr_trunc = stderr;
        o.entry_wall_ns = diag.guest_wall_ns;
        o.outputs = outputs;
        o.diagnostics = diag;
        Ok(o)
    }
}

fn tail(s: &str) -> &str {
    let n = s.len();
    let mut start = n.saturating_sub(2000);
    while !s.is_char_boundary(start) {
        start += 1;
    }
    &s[start..]
}

pub const BACKEND_NAME: &str = "firecracker";

/// Guest layout of this backend: identical paths to bwrap-dev, with
/// copy-in, scratch dirs, arbitrary cwd and collect supported.
pub const FC_LAYOUT: arena_sandbox::GuestLayout = arena_sandbox::GuestLayout {
    scratch: proto::GUEST_SCRATCH,
    inputs: proto::GUEST_INPUTS,
    mount_prefixes: proto::GUEST_MOUNT_PREFIXES,
    flexible_scratch: true,
    rw_binds: false,
};

/// Create-or-replace `base/rel` as a regular file, refusing to traverse or
/// replace symlinks or non-regular entries.
fn safe_replace(base: &Path, rel: &str, mode: u32) -> io::Result<File> {
    proto::validate_rel_path(rel).map_err(io::Error::other)?;
    let mut cur = base.to_path_buf();
    let comps: Vec<&str> = rel.split('/').collect();
    for c in &comps[..comps.len() - 1] {
        cur.push(c);
        match fs::symlink_metadata(&cur) {
            Ok(m) if m.is_dir() => {}
            Ok(_) => return Err(io::Error::other("parent is not a real directory")),
            Err(e) if e.kind() == io::ErrorKind::NotFound => fs::create_dir(&cur)?,
            Err(e) => return Err(e),
        }
    }
    cur.push(comps[comps.len() - 1]);
    match fs::symlink_metadata(&cur) {
        Ok(m) if m.is_file() => fs::remove_file(&cur)?,
        Ok(_) => return Err(io::Error::other("exists and is not a regular file")),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .custom_flags(libc::O_NOFOLLOW)
        .mode(mode)
        .open(&cur)
}

fn abs_guest(p: &str) -> Result<(), InfraError> {
    let rel = p
        .strip_prefix('/')
        .ok_or_else(|| InfraError::InvalidSpec(format!("guest path {p:?} must be absolute")))?;
    if rel.is_empty() {
        return Ok(());
    }
    proto::validate_rel_path(rel)
        .map_err(|e| InfraError::InvalidSpec(format!("guest path {p:?}: {e}")))
}

fn rel_scratch(p: &str) -> Result<(), InfraError> {
    proto::validate_rel_path(p)
        .map_err(|e| InfraError::InvalidSpec(format!("scratch path {p:?}: {e}")))
}

impl FirecrackerSandbox {
    /// Run a native request (operator CLI, VM tests).
    pub fn run_native(&self, req: &RunRequest) -> Result<SandboxOutcome, InfraError> {
        self.run_inner(req)
    }

    /// Translate a shared `SandboxSpec` (validated against [`FC_LAYOUT`]).
    fn translate(
        &self,
        spec: &arena_sandbox::SandboxSpec,
        out_dir: PathBuf,
    ) -> Result<RunRequest, InfraError> {
        spec.validate_for(&FC_LAYOUT)?;
        let root_image = match &spec.rootfs {
            arena_sandbox::Rootfs::BackendDefault => None,
            arena_sandbox::Rootfs::Image { path, digest } => Some(RootImage {
                dir: path.clone(),
                digest: digest.clone(),
            }),
            arena_sandbox::Rootfs::HostDev => {
                return Err(InfraError::InvalidSpec(
                    "firecracker has no host-dev rootfs; use a pinned toolchain image".into(),
                ))
            }
        };
        Ok(RunRequest {
            rootfs_digest: self.rootfs_digest.clone(),
            root_image,
            ro_mounts: spec
                .ro_mounts
                .iter()
                .map(|m| RoMount {
                    host_path: m.host.clone(),
                    guest_path: m.guest.clone(),
                })
                .collect(),
            // arena_sandbox::SandboxSpec has no read-write binds on main yet
            rw_dirs: vec![],
            allow_mount_symlinks: false,
            rw_scratch_mb: spec.rw_scratch_mb,
            copy_in: spec
                .copy_in
                .iter()
                .map(|c| (c.from_guest.clone(), c.to_scratch.clone()))
                .collect(),
            scratch_dirs: spec.scratch_dirs.clone(),
            argv: spec.argv.clone(),
            cwd: spec.cwd.clone(),
            env: spec.env.clone(),
            cpu_set: spec.cpu_set.clone().unwrap_or_default(),
            mem_bytes: spec.mem_bytes,
            pids: spec.pids,
            wall_timeout: spec.wall_timeout,
            network: None,
            collect: spec.collect.clone(),
            out_dir,
            max_output_bytes: spec.max_output_bytes,
        })
    }
}

impl arena_sandbox::Sandbox for FirecrackerSandbox {
    fn name(&self) -> &str {
        BACKEND_NAME
    }
    /// Production isolation: no tier cap.
    fn tier_cap(&self) -> Option<arena_types::challenge::Tier> {
        None
    }
    fn layout(&self) -> arena_sandbox::GuestLayout {
        FC_LAYOUT
    }

    /// Outputs: the guest collects exactly `spec.collect` (scratch-relative);
    /// they are materialized at `spec.out_dir/<path>`.
    fn run(&self, spec: &arena_sandbox::SandboxSpec) -> Result<SandboxOutcome, InfraError> {
        let (root, tmp_root) = match &spec.out_dir {
            Some(d) => {
                if d.exists() {
                    return Err(InfraError::InvalidSpec(format!(
                        "out_dir {} already exists",
                        d.display()
                    )));
                }
                (d.clone(), false)
            }
            None => (
                self.cfg
                    .work_root
                    .join("jobs")
                    .join(format!("discard-{}", random_hex(8)?)),
                true,
            ),
        };
        let res = self
            .translate(spec, root.clone())
            .and_then(|req| self.run_inner(&req));
        let mut o = match res {
            Ok(o) => o,
            Err(e) => {
                let _ = fs::remove_dir_all(&root);
                return Err(e);
            }
        };
        o.stdout_trunc.truncate(spec.output_trunc_bytes);
        o.stderr_trunc.truncate(spec.output_trunc_bytes);
        if !o.diagnostics.output_violations.is_empty() || !o.diagnostics.outputs_complete {
            o.output_error = Some(format!(
                "output collection incomplete: {}",
                o.diagnostics.output_violations.join("; ")
            ));
            o.outputs.clear();
            let _ = fs::remove_dir_all(&root);
            let _ = fs::create_dir_all(&root);
        }
        if tmp_root {
            o.outputs.clear();
            let _ = fs::remove_dir_all(&root);
        } else if o.output_error.is_none() {
            let lim = arena_archive::Limits {
                max_expanded_bytes: spec.max_output_bytes.max(1),
                ..Default::default()
            };
            match arena_archive::tree_from_dir(&root, &lim) {
                Ok(t) => o.outputs_tree = Some(t.digest()),
                Err(e) => o.output_error = Some(e.to_string()),
            }
        }
        Ok(o)
    }
}
