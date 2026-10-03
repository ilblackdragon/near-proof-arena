//! Wire formats shared by the three parties of the Firecracker runner:
//!
//! * the host library (`arena-firecracker`), which writes the *control*
//!   block and parses the *output* device after the VM is gone;
//! * the in-container shim (`arena-fc-shim`), which watches the serial
//!   console for the start/exit markers;
//! * the in-guest init (`arena-init`), which reads the control block and
//!   writes the output device.
//!
//! Both block devices are raw (no filesystem): the host never mounts or
//! fsck's anything the guest wrote. Everything coming *from* the guest is
//! treated as hostile input and decoded with explicit limits.
//!
//! Output device layout (little endian):
//!
//! ```text
//! "ARENAOUT" u32 version
//! u32 report_len  report JSON (GuestReport)
//! u32 stdout_len  stdout bytes
//! u32 stderr_len  stderr bytes
//! repeated: u8 tag
//!   tag 1 = file: u16 path_len, path utf8, u8 exec(0|1), u64 size, size bytes
//!   tag 2 = end:  u32 len, JSON (CollectSummary)
//! ```

use serde::{Deserialize, Serialize};
use std::io::{self, Read, Write};

pub const CTL_MAGIC: &[u8; 8] = b"ARENACTL";
pub const OUT_MAGIC: &[u8; 8] = b"ARENAOUT";
pub const PROTO_VERSION: u32 = 2;

/// Guest mount point of the per-run scratch disk (default cwd, `HOME`).
/// Same layout as the bwrap-dev backend (`arena_sandbox::SCRATCH`).
pub const GUEST_SCRATCH: &str = "/scratch";
/// `TMPDIR`; `/tmp` is a bind mount of it (on the scratch disk).
pub const GUEST_TMP_DIR: &str = "/scratch/tmp";
/// Root for read-only inputs.
pub const GUEST_INPUTS: &str = "/in";
/// Every read-only mount must live under one of these prefixes.
pub const GUEST_MOUNT_PREFIXES: &[&str] = &["/in/", "/opt/", "/arena/"];
/// Scratch-relative directory holding the guest copies of read-write dirs.
pub const RW_SCRATCH_DIR: &str = ".rw";
/// Fixed drive order (`/dev/vda` = index 0). Mount drives follow.
pub const ROOTFS_DEV_INDEX: u32 = 0;
pub const CTL_DEV_INDEX: u32 = 1;
pub const OUT_DEV_INDEX: u32 = 2;
pub const SCRATCH_DEV_INDEX: u32 = 3;
pub const FIRST_MOUNT_DEV_INDEX: u32 = 4;
/// Firecracker attaches at most this many drives comfortably; we cap mounts.
pub const MAX_MOUNTS: usize = 16;

/// `/dev/vdX` path for a drive index.
pub fn dev_path(index: u32) -> String {
    assert!(index < 26);
    format!("/dev/vd{}", (b'a' + index as u8) as char)
}

/// Unprivileged identity the candidate runs as inside the guest.
pub const CANDIDATE_UID: u32 = 1000;
pub const CANDIDATE_GID: u32 = 1000;

/// Serial-console marker lines (`<prefix> <nonce> ...`). Only guest init
/// (root) can write to the console; the candidate's stdio goes to pipes.
pub const MARKER_START: &str = "ARENA-START";
pub const MARKER_EXIT: &str = "ARENA-EXIT";
/// Per-step markers in steps mode (`<prefix> <nonce> <index> ...`), printed
/// between the overall START and EXIT markers.
pub const MARKER_STEP_START: &str = "ARENA-STEP-START";
pub const MARKER_STEP_EXIT: &str = "ARENA-STEP-EXIT";
/// Most steps one guest job may run.
pub const MAX_STEPS: usize = 64;
/// Per-step stdout/stderr kept in the report (steps mode).
pub const STEP_STREAM_CAP: usize = 2048;

/// Captured stdout/stderr cap (CONTRACTS §4: 64 KiB).
pub const STREAM_CAP: usize = 64 * 1024;
pub const MAX_PATH_LEN: usize = 255;
pub const MAX_CONTROL_LEN: usize = 1 << 20;
pub const MAX_REPORT_LEN: usize = 512 * 1024;
pub const MAX_SUMMARY_LEN: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MountKind {
    /// The image root is mounted at `guest_path`.
    Dir,
    /// The image contains exactly one file, `name`, which is bind-mounted
    /// (read-only) at `guest_path`.
    File { name: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestMount {
    /// `/dev/vdX` index of the backing drive (0 = vda).
    pub dev_index: u32,
    pub guest_path: String,
    pub kind: MountKind,
}

/// Job description handed to `arena-init` through the control drive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestJob {
    pub version: u32,
    /// Random per-run nonce echoed in the console markers.
    pub nonce: String,
    pub argv: Vec<String>,
    pub env: Vec<(String, String)>,
    /// Memory limit for the candidate cgroup inside the guest (bytes).
    pub mem_limit_bytes: u64,
    pub pids_max: u32,
    pub nofile: u64,
    pub scratch_dev_index: u32,
    pub out_dev_index: u32,
    /// Size of the output device; init never writes beyond it.
    pub out_dev_bytes: u64,
    pub mounts: Vec<GuestMount>,
    pub max_output_files: u32,
    pub max_output_bytes: u64,
    /// Drive holding an alternative candidate root image (e.g. a pinned
    /// build toolchain); `None` = the arena rootfs itself.
    pub root_dev_index: Option<u32>,
    /// `(absolute guest path, scratch-relative destination)` copied into
    /// scratch (owned by the candidate) before the entry point starts.
    pub copy_in: Vec<(String, String)>,
    /// Scratch-relative directories created after `copy_in`.
    pub scratch_dirs: Vec<String>,
    /// Absolute guest working directory.
    pub cwd: String,
    /// Scratch-relative files/directories collected after the run.
    pub collect: Vec<String>,
    /// Guest-enforced wall timeout (the host enforces a hard one later).
    pub timeout_ms: u64,
    /// Read-write directories: initial content (if any) comes from a
    /// read-only drive, lives on scratch at `<RW_SCRATCH_DIR>/<i>` and is
    /// bind-mounted at `guest_path`; it is collected back after the run.
    #[serde(default)]
    pub rw_dirs: Vec<GuestRwDir>,
    /// Seccomp violation-detection policy for the candidate tree.
    #[serde(default)]
    pub syscall_policy: arena_seccomp::Policy,
    /// Steps mode (non-empty): instead of `argv`/`collect`, run each step in
    /// order in this one guest. Before every step init wipes the scratch
    /// work dir, `/dev/shm` and re-applies `copy_in`/`scratch_dirs`; every
    /// step runs as a fresh process tree in a fresh cgroup and IPC namespace,
    /// sees only its own `binds`, and is killed (whole cgroup) when it ends.
    /// Nothing written by one step is visible to the next.
    #[serde(default)]
    pub steps: Vec<GuestStep>,
    /// Drive with the per-step input files (mounted root-only, outside the
    /// candidate root; `GuestStep::binds` sources are relative to it).
    #[serde(default)]
    pub steps_dev_index: Option<u32>,
}

/// One step of a steps-mode job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestStep {
    pub argv: Vec<String>,
    /// `(source relative to the steps drive, absolute guest path)`: a single
    /// file bind-mounted read-only for this step only.
    pub binds: Vec<(String, String)>,
    /// Scratch-relative files/dirs collected after this step; returned
    /// under `<STEP_OUT_PREFIX><index>/<path>`.
    pub collect: Vec<String>,
    pub timeout_ms: u64,
}

/// Output-path prefix of step `i`'s collected files: `.step<i>/<path>`.
pub const STEP_OUT_PREFIX: &str = ".step";

/// Per-step result in steps mode.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StepReport {
    pub status: GuestStatus,
    /// Guest monotonic clock, spawn -> exit of the step's entry process.
    pub guest_wall_ns: u64,
    pub guest_cpu_ns: u64,
    pub guest_peak_mem_bytes: u64,
    pub oom_kills: u64,
    /// First `STEP_STREAM_CAP` bytes, lossy UTF-8.
    pub stdout: String,
    pub stderr: String,
    pub stdout_total_bytes: u64,
    pub stderr_total_bytes: u64,
    /// Problems copying this step's outputs out of scratch (symlinks,
    /// special files, limits); non-empty means the outputs are unusable.
    pub collect_violations: Vec<String>,
    /// Sandbox violations (seccomp) during this step.
    #[serde(default)]
    pub violations: Vec<arena_seccomp::Violation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestRwDir {
    pub dev_index: Option<u32>,
    pub guest_path: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum GuestStatus {
    Exited {
        code: i32,
    },
    Signaled {
        signal: i32,
    },
    /// The candidate cgroup hit its memory limit and the OOM killer fired.
    OomKilled,
    /// init killed the candidate at `timeout_ms` (stdout/stderr preserved).
    TimedOut,
    /// The candidate could not be started (e.g. argv[0] missing).
    SpawnFailed {
        error: String,
    },
    /// init itself failed before/while running the candidate.
    InitError {
        error: String,
    },
}

/// Diagnostic report written by guest init. Exit status is necessarily
/// reported by the guest; resource figures here are *diagnostic* — the host
/// cgroup accounting is authoritative.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestReport {
    pub version: u32,
    pub nonce: String,
    pub status: GuestStatus,
    pub guest_wall_ns: u64,
    pub guest_cpu_ns: u64,
    pub guest_peak_mem_bytes: u64,
    pub oom_kills: u64,
    pub stdout_total_bytes: u64,
    pub stderr_total_bytes: u64,
    /// Steps mode: one entry per step that was started (in order).
    #[serde(default)]
    pub steps: Vec<StepReport>,
    /// Sandbox violations observed by init's seccomp listener (all steps).
    #[serde(default)]
    pub violations: Vec<arena_seccomp::Violation>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectSummary {
    pub files: u64,
    pub bytes: u64,
    /// Policy violations observed while collecting (symlinks, special files,
    /// limits exceeded, unreadable entries). Collection stops at a limit.
    pub violations: Vec<String>,
    pub complete: bool,
}

// ---------------------------------------------------------------------------
// paths

/// Relative output path rules (CONTRACTS §1/§3): non-empty, at most 255
/// bytes, `/`-separated, no empty / `.` / `..` components, no NUL, no
/// leading `/`, no backslash, no control characters.
pub fn validate_rel_path(p: &str) -> Result<(), String> {
    if p.is_empty() || p.len() > MAX_PATH_LEN {
        return Err(format!("path length {} out of range", p.len()));
    }
    if p.starts_with('/') {
        return Err("absolute path".into());
    }
    if p.chars().any(|c| c == '\0' || c == '\\' || c.is_control()) {
        return Err("forbidden character in path".into());
    }
    for comp in p.split('/') {
        if comp.is_empty() || comp == "." || comp == ".." {
            return Err(format!("bad path component {comp:?}"));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// control block

pub fn encode_control(job: &GuestJob) -> Vec<u8> {
    let json = serde_json::to_vec(job).expect("GuestJob serializes");
    let mut out = Vec::with_capacity(json.len() + 12);
    out.extend_from_slice(CTL_MAGIC);
    out.extend_from_slice(&(json.len() as u32).to_le_bytes());
    out.extend_from_slice(&json);
    // pad to a whole number of 4 KiB sectors-ish blocks
    let padded = out.len().div_ceil(4096) * 4096;
    out.resize(padded, 0);
    out
}

pub fn decode_control(buf: &[u8]) -> Result<GuestJob, String> {
    if buf.len() < 12 || &buf[..8] != CTL_MAGIC {
        return Err("bad control magic".into());
    }
    let len = u32::from_le_bytes(buf[8..12].try_into().unwrap()) as usize;
    if len > MAX_CONTROL_LEN || 12 + len > buf.len() {
        return Err("bad control length".into());
    }
    let job: GuestJob = serde_json::from_slice(&buf[12..12 + len]).map_err(|e| e.to_string())?;
    if job.version != PROTO_VERSION {
        return Err(format!("control version {} unsupported", job.version));
    }
    Ok(job)
}

// ---------------------------------------------------------------------------
// output device: writer (guest side)

pub struct OutWriter<W: Write> {
    w: W,
    written: u64,
    limit: u64,
}

impl<W: Write> OutWriter<W> {
    /// `limit` is the device size; the writer refuses to go beyond it
    /// (reserving room for the end record).
    pub fn new(w: W, limit: u64) -> Self {
        OutWriter {
            w,
            written: 0,
            limit,
        }
    }

    pub fn written(&self) -> u64 {
        self.written
    }

    /// Bytes still available for file records (keeps room for the trailer).
    pub fn remaining(&self) -> u64 {
        self.limit
            .saturating_sub(self.written)
            .saturating_sub(MAX_SUMMARY_LEN as u64 + 8)
    }

    fn put(&mut self, b: &[u8]) -> io::Result<()> {
        if self.written + b.len() as u64 > self.limit {
            return Err(io::Error::other("output device full"));
        }
        self.w.write_all(b)?;
        self.written += b.len() as u64;
        Ok(())
    }

    pub fn write_header(
        &mut self,
        report: &GuestReport,
        stdout: &[u8],
        stderr: &[u8],
    ) -> io::Result<()> {
        let rep = serde_json::to_vec(report).map_err(io::Error::other)?;
        assert!(rep.len() <= MAX_REPORT_LEN);
        let stdout = &stdout[..stdout.len().min(STREAM_CAP)];
        let stderr = &stderr[..stderr.len().min(STREAM_CAP)];
        self.put(OUT_MAGIC)?;
        self.put(&PROTO_VERSION.to_le_bytes())?;
        self.put(&(rep.len() as u32).to_le_bytes())?;
        self.put(&rep)?;
        self.put(&(stdout.len() as u32).to_le_bytes())?;
        self.put(stdout)?;
        self.put(&(stderr.len() as u32).to_le_bytes())?;
        self.put(stderr)
    }

    /// Writes one file record of exactly `size` bytes taken from `r`
    /// (zero-padded if `r` ends early; returns the number of real bytes).
    pub fn write_file(
        &mut self,
        path: &str,
        exec: bool,
        size: u64,
        r: &mut dyn Read,
    ) -> io::Result<u64> {
        validate_rel_path(path).map_err(io::Error::other)?;
        if 1 + 2 + path.len() as u64 + 1 + 8 + size > self.remaining() {
            return Err(io::Error::other("output device full"));
        }
        self.put(&[1u8])?;
        self.put(&(path.len() as u16).to_le_bytes())?;
        self.put(path.as_bytes())?;
        self.put(&[exec as u8])?;
        self.put(&size.to_le_bytes())?;
        let mut left = size;
        let mut real = 0u64;
        let mut buf = vec![0u8; 1 << 16];
        while left > 0 {
            let want = left.min(buf.len() as u64) as usize;
            let n = match r.read(&mut buf[..want]) {
                Ok(0) => break,
                Ok(n) => n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            };
            self.put(&buf[..n])?;
            left -= n as u64;
            real += n as u64;
        }
        if left > 0 {
            let zeros = vec![0u8; 1 << 16];
            while left > 0 {
                let n = left.min(zeros.len() as u64) as usize;
                self.put(&zeros[..n])?;
                left -= n as u64;
            }
        }
        Ok(real)
    }

    pub fn finish(mut self, summary: &CollectSummary) -> io::Result<W> {
        let mut s = serde_json::to_vec(summary).map_err(io::Error::other)?;
        if s.len() > MAX_SUMMARY_LEN {
            let mut small = summary.clone();
            small.violations.truncate(16);
            small.violations.push("violations truncated".into());
            s = serde_json::to_vec(&small).map_err(io::Error::other)?;
        }
        // The end record uses the space reserved by `remaining()`.
        self.put(&[2u8])?;
        self.put(&(s.len() as u32).to_le_bytes())?;
        self.put(&s)?;
        self.w.flush()?;
        Ok(self.w)
    }
}

// ---------------------------------------------------------------------------
// output device: reader (host side, hostile input)

#[derive(Clone, Debug)]
pub struct DecodeLimits {
    pub max_files: u64,
    pub max_total_bytes: u64,
}

#[derive(Debug)]
pub struct DecodedHeader {
    pub report: GuestReport,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

#[derive(Debug)]
pub enum DecodeError {
    /// The stream is malformed or exceeds limits (guest misbehaviour).
    Malformed(String),
    /// The sink failed (host I/O problem).
    Sink(io::Error),
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeError::Malformed(s) => write!(f, "malformed output stream: {s}"),
            DecodeError::Sink(e) => write!(f, "output sink: {e}"),
        }
    }
}

impl std::error::Error for DecodeError {}

fn mal<T>(s: impl Into<String>) -> Result<T, DecodeError> {
    Err(DecodeError::Malformed(s.into()))
}

fn read_exact_m(r: &mut dyn Read, buf: &mut [u8]) -> Result<(), DecodeError> {
    r.read_exact(buf)
        .map_err(|e| DecodeError::Malformed(format!("truncated: {e}")))
}

fn read_u32(r: &mut dyn Read) -> Result<u32, DecodeError> {
    let mut b = [0u8; 4];
    read_exact_m(r, &mut b)?;
    Ok(u32::from_le_bytes(b))
}

fn read_blob(r: &mut dyn Read, max: usize) -> Result<Vec<u8>, DecodeError> {
    let len = read_u32(r)? as usize;
    if len > max {
        return mal(format!("blob of {len} bytes exceeds {max}"));
    }
    let mut v = vec![0u8; len];
    read_exact_m(r, &mut v)?;
    Ok(v)
}

pub fn decode_header(r: &mut dyn Read) -> Result<DecodedHeader, DecodeError> {
    let mut magic = [0u8; 8];
    read_exact_m(r, &mut magic)?;
    if &magic != OUT_MAGIC {
        return mal("bad output magic (guest did not write a report)");
    }
    let v = read_u32(r)?;
    if v != PROTO_VERSION {
        return mal(format!("output version {v}"));
    }
    let rep = read_blob(r, MAX_REPORT_LEN)?;
    let report: GuestReport = serde_json::from_slice(&rep)
        .map_err(|e| DecodeError::Malformed(format!("report json: {e}")))?;
    let stdout = read_blob(r, STREAM_CAP)?;
    let stderr = read_blob(r, STREAM_CAP)?;
    Ok(DecodedHeader {
        report,
        stdout,
        stderr,
    })
}

/// Decodes file records after the header, calling `sink(path, exec, size,
/// reader)` for each; the sink must consume exactly `size` bytes (the reader
/// is bounded to them). Paths are validated and must be unique.
pub fn decode_files(
    r: &mut dyn Read,
    limits: &DecodeLimits,
    mut sink: impl FnMut(&str, bool, u64, &mut dyn Read) -> io::Result<()>,
) -> Result<CollectSummary, DecodeError> {
    let mut seen = std::collections::BTreeSet::new();
    let mut files = 0u64;
    let mut total = 0u64;
    loop {
        let mut tag = [0u8; 1];
        read_exact_m(r, &mut tag)?;
        match tag[0] {
            1 => {
                let mut lb = [0u8; 2];
                read_exact_m(r, &mut lb)?;
                let len = u16::from_le_bytes(lb) as usize;
                if len == 0 || len > MAX_PATH_LEN {
                    return mal("bad path length");
                }
                let mut pb = vec![0u8; len];
                read_exact_m(r, &mut pb)?;
                let path = String::from_utf8(pb)
                    .map_err(|_| DecodeError::Malformed("non-utf8 path".into()))?;
                validate_rel_path(&path).map_err(DecodeError::Malformed)?;
                let mut eb = [0u8; 1];
                read_exact_m(r, &mut eb)?;
                if eb[0] > 1 {
                    return mal("bad exec flag");
                }
                let mut sb = [0u8; 8];
                read_exact_m(r, &mut sb)?;
                let size = u64::from_le_bytes(sb);
                files += 1;
                total = total.saturating_add(size);
                if files > limits.max_files {
                    return mal("too many output files");
                }
                if total > limits.max_total_bytes {
                    return mal("outputs exceed byte limit");
                }
                // a file and a directory of the same name cannot coexist
                for (i, _) in path.match_indices('/') {
                    if seen.contains(&path[..i]) {
                        return mal(format!("path {path:?} nested under a file"));
                    }
                }
                let prefix = format!("{path}/");
                if seen
                    .range(prefix.clone()..)
                    .next()
                    .is_some_and(|p: &String| p.starts_with(&prefix))
                {
                    return mal(format!("path {path:?} is a directory of another output"));
                }
                if !seen.insert(path.clone()) {
                    return mal(format!("duplicate path {path:?}"));
                }
                let mut bounded = CountingTake {
                    inner: &mut *r,
                    left: size,
                    n: 0,
                };
                sink(&path, eb[0] == 1, size, &mut bounded).map_err(DecodeError::Sink)?;
                if bounded.n != size {
                    // drain whatever the sink did not consume
                    io::copy(&mut bounded, &mut io::sink()).map_err(DecodeError::Sink)?;
                    if bounded.n != size {
                        return mal("truncated file record");
                    }
                }
            }
            2 => {
                let s = read_blob(r, MAX_SUMMARY_LEN)?;
                let summary: CollectSummary = serde_json::from_slice(&s)
                    .map_err(|e| DecodeError::Malformed(format!("summary json: {e}")))?;
                if summary.files != files || summary.bytes != total {
                    return mal("summary does not match records");
                }
                return Ok(summary);
            }
            t => return mal(format!("bad record tag {t}")),
        }
    }
}

struct CountingTake<'a, 'b> {
    inner: &'a mut (dyn Read + 'b),
    left: u64,
    n: u64,
}

impl Read for CountingTake<'_, '_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.left == 0 {
            return Ok(0);
        }
        let max = buf.len().min(self.left.min(usize::MAX as u64) as usize);
        let k = self.inner.read(&mut buf[..max])?;
        self.left -= k as u64;
        self.n += k as u64;
        Ok(k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn report() -> GuestReport {
        GuestReport {
            version: PROTO_VERSION,
            nonce: "n".into(),
            status: GuestStatus::Exited { code: 3 },
            guest_wall_ns: 1,
            guest_cpu_ns: 2,
            guest_peak_mem_bytes: 3,
            oom_kills: 0,
            stdout_total_bytes: 5,
            stderr_total_bytes: 0,
            steps: vec![],
            violations: vec![],
        }
    }

    #[test]
    fn roundtrip() {
        let mut w = OutWriter::new(Vec::new(), 1 << 20);
        w.write_header(&report(), b"hello", b"").unwrap();
        w.write_file("a/b.bin", false, 3, &mut &b"xyz"[..]).unwrap();
        w.write_file("c", true, 4, &mut &b"12"[..]).unwrap(); // short -> padded
        let buf = w
            .finish(&CollectSummary {
                files: 2,
                bytes: 7,
                violations: vec![],
                complete: true,
            })
            .unwrap();
        let mut r: &[u8] = &buf;
        let h = decode_header(&mut r).unwrap();
        assert_eq!(h.stdout, b"hello");
        assert_eq!(h.report.status, GuestStatus::Exited { code: 3 });
        let mut got = Vec::new();
        let lim = DecodeLimits {
            max_files: 10,
            max_total_bytes: 100,
        };
        let s = decode_files(&mut r, &lim, |p, x, _, rd| {
            let mut v = Vec::new();
            rd.read_to_end(&mut v)?;
            got.push((p.to_string(), x, v));
            Ok(())
        })
        .unwrap();
        assert!(s.complete);
        assert_eq!(got[0], ("a/b.bin".into(), false, b"xyz".to_vec()));
        assert_eq!(got[1], ("c".into(), true, b"12\0\0".to_vec()));
    }

    #[test]
    fn rejects_hostile_paths_and_limits() {
        for p in ["", "/abs", "a/../b", "a//b", ".", "a/./b", "x\0y", "a\\b"] {
            assert!(validate_rel_path(p).is_err(), "{p:?}");
        }
        assert!(validate_rel_path(&"a".repeat(256)).is_err());
        // handcraft a record with a traversal path
        let mut w = OutWriter::new(Vec::new(), 1 << 20);
        w.write_header(&report(), b"", b"").unwrap();
        let mut buf = w.finish(&CollectSummary::default()).unwrap();
        let n = buf.len();
        buf.truncate(
            n - (1
                + 4
                + serde_json::to_vec(&CollectSummary::default())
                    .unwrap()
                    .len()),
        );
        buf.push(1);
        buf.extend_from_slice(&5u16.to_le_bytes());
        buf.extend_from_slice(b"../x0");
        let mut r: &[u8] = &buf;
        decode_header(&mut r).unwrap();
        let lim = DecodeLimits {
            max_files: 10,
            max_total_bytes: 100,
        };
        assert!(matches!(
            decode_files(&mut r, &lim, |_, _, _, _| Ok(())),
            Err(DecodeError::Malformed(_))
        ));
        // size limit
        let mut w = OutWriter::new(Vec::new(), 1 << 20);
        w.write_header(&report(), b"", b"").unwrap();
        w.write_file("big", false, 200, &mut io::repeat(1)).unwrap();
        let buf = w
            .finish(&CollectSummary {
                files: 1,
                bytes: 200,
                violations: vec![],
                complete: true,
            })
            .unwrap();
        let mut r: &[u8] = &buf;
        decode_header(&mut r).unwrap();
        assert!(decode_files(&mut r, &lim, |_, _, _, _| Ok(())).is_err());
    }

    #[test]
    fn rejects_file_dir_conflicts_and_dups() {
        for pair in [("a", "a/b"), ("a/b", "a"), ("x", "x")] {
            let mut w = OutWriter::new(Vec::new(), 1 << 20);
            w.write_header(&report(), b"", b"").unwrap();
            w.write_file(pair.0, false, 1, &mut &b"1"[..]).unwrap();
            w.write_file(pair.1, false, 1, &mut &b"1"[..]).unwrap();
            let buf = w
                .finish(&CollectSummary {
                    files: 2,
                    bytes: 2,
                    violations: vec![],
                    complete: true,
                })
                .unwrap();
            let mut r: &[u8] = &buf;
            decode_header(&mut r).unwrap();
            let lim = DecodeLimits {
                max_files: 10,
                max_total_bytes: 100,
            };
            assert!(
                decode_files(&mut r, &lim, |_, _, _, rd| io::copy(rd, &mut io::sink())
                    .map(|_| ()))
                .is_err(),
                "{pair:?}"
            );
        }
    }

    #[test]
    fn control_roundtrip() {
        let job = GuestJob {
            version: PROTO_VERSION,
            nonce: "abc".into(),
            argv: vec!["/bin/true".into()],
            env: vec![("PATH".into(), "/bin".into())],
            mem_limit_bytes: 1 << 20,
            pids_max: 10,
            nofile: 64,
            scratch_dev_index: 3,
            out_dev_index: 2,
            out_dev_bytes: 1 << 20,
            mounts: vec![GuestMount {
                dev_index: 4,
                guest_path: "/in/b".into(),
                kind: MountKind::Dir,
            }],
            max_output_files: 10,
            max_output_bytes: 100,
            root_dev_index: Some(5),
            copy_in: vec![("/in/b".into(), "work".into())],
            scratch_dirs: vec!["out/public".into()],
            cwd: "/scratch/work".into(),
            collect: vec!["out".into()],
            timeout_ms: 1000,
            rw_dirs: vec![GuestRwDir {
                dev_index: Some(6),
                guest_path: "/arena/out".into(),
            }],
            steps: vec![GuestStep {
                argv: vec!["/bin/true".into()],
                binds: vec![("s0/0".into(), "/in/request.bin".into())],
                collect: vec!["out".into()],
                timeout_ms: 10,
            }],
            steps_dev_index: Some(7),
            syscall_policy: arena_seccomp::Policy::Strict,
        };
        let enc = encode_control(&job);
        assert_eq!(enc.len() % 4096, 0);
        assert_eq!(decode_control(&enc).unwrap(), job);
        assert!(decode_control(&enc[..10]).is_err());
    }
}

// ---------------------------------------------------------------------------
// host library <-> in-container shim (both trusted; JSON files in /job)

pub const SHIM_JOB_FILE: &str = "job.json";
pub const SHIM_RESULT_FILE: &str = "result.json";
/// Directory (inside the job dir) holding the drive images and kernel
/// before the shim moves them into the jail.
pub const SHIM_INPUT_DIR: &str = "in";
/// Where the shim leaves the output drive image after the run.
pub const SHIM_OUT_IMAGE: &str = "out.img";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShimDrive {
    pub drive_id: String,
    /// File name inside `in/` (moved into the jail root).
    pub file: String,
    pub read_only: bool,
    pub is_root: bool,
    /// Whether the jailed Firecracker uid must own it (writable drives).
    pub chown_to_vmm: bool,
    pub rate_limit: Option<DriveRateLimit>,
}

/// Firecracker token-bucket I/O limits for one drive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DriveRateLimit {
    pub bytes_per_s: u64,
    pub ops_per_s: u64,
    /// One-time burst allowance in bytes on top of the sustained rate.
    pub burst_bytes: u64,
}

impl DriveRateLimit {
    /// Firecracker `rate_limiter` JSON (buckets refilled every 100 ms).
    pub fn to_firecracker_json(&self) -> serde_json::Value {
        let per_100ms = |x: u64| (x / 10).max(1);
        serde_json::json!({
            "bandwidth": { "size": per_100ms(self.bytes_per_s), "one_time_burst": self.burst_bytes, "refill_time": 100 },
            "ops": { "size": per_100ms(self.ops_per_s), "refill_time": 100 },
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShimJob {
    pub version: u32,
    /// `[a-zA-Z0-9-]{1,60}`; used as jailer id.
    pub id: String,
    pub nonce: String,
    pub vcpus: u32,
    pub guest_mem_mib: u64,
    /// cgroup v2 `cpuset.cpus` list for the VMM, e.g. "2,3".
    pub cpuset: Option<String>,
    /// Host cgroup `memory.max` for the VMM process (guest RAM + overhead).
    pub vmm_mem_max_bytes: u64,
    pub vmm_pids_max: u32,
    /// Firecracker file-size rlimit (bounds writes to writable images).
    pub vmm_fsize_limit: u64,
    pub kernel_file: String,
    pub boot_args: String,
    pub drives: Vec<ShimDrive>,
    pub vmm_uid: u32,
    pub vmm_gid: u32,
    pub host_uid: u32,
    pub host_gid: u32,
    pub boot_timeout_ms: u64,
    pub run_timeout_ms: u64,
    pub collect_timeout_ms: u64,
    pub serial_cap_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum ShimStatus {
    /// Firecracker exited by itself (guest rebooted / crashed).
    VmmExited {
        code: Option<i32>,
        signal: Option<i32>,
    },
    /// The candidate exceeded `run_timeout_ms`; the VM was killed.
    TimedOut,
    /// The guest did not reach the start marker in time; the VM was killed.
    BootTimeout,
    /// Output collection overran `collect_timeout_ms`; the VM was killed.
    CollectTimeout,
    /// Supervisor-side failure (infrastructure).
    Error { error: String },
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostCgroupStats {
    pub memory_peak_bytes: u64,
    pub cpu_usage_ns: u64,
    pub oom_kill: u64,
    pub pids_peak: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShimResult {
    pub version: u32,
    pub status: ShimStatus,
    /// jailer spawn -> VMM exit.
    pub vmm_wall_ns: u64,
    /// jailer spawn -> START marker observed on the serial console.
    pub boot_ns: Option<u64>,
    /// START marker -> EXIT marker (host clock). The authoritative candidate
    /// wall time; on timeout, START -> kill.
    pub run_wall_ns: Option<u64>,
    /// EXIT marker -> VMM exit (output collection + reboot).
    pub teardown_ns: Option<u64>,
    pub cgroup: HostCgroupStats,
    pub serial_tail: String,
    /// Steps mode: host-clock STEP-START -> STEP-EXIT per step index (the
    /// authoritative per-step wall time); `None` if a marker was missing.
    #[serde(default)]
    pub step_wall_ns: Vec<Option<u64>>,
}
