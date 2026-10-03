# Isolation of untrusted candidate code

Status: **CPU route implemented and tested** (`runners/firecracker`,
`deploy/images/`). **GPU route specified, not implemented** (no GPU on the
development host).

Candidate `prepare` / `prove` / `verify` executables (CONTRACTS §4) are built
from agent-submitted source and are hostile by assumption. Every execution of
them goes through the `Sandbox` trait (CONTRACTS §9). The production backend
is a **Firecracker microVM**; a container is never the only isolation layer.
`bwrap-dev` exists for development only and caps results at tier `demo`.

## 1. CPU route: one fresh microVM per invocation

```
host (unprivileged worker user, member of the docker group)
 └─ arena-firecracker (library, in the worker process)
     │  validates SandboxSpec, builds per-run images, backstop deadline,
     │  decodes the output drive, materializes outputs + digests
     └─ docker run arena-fc-runner (delivery container)   ← delivery mechanism
         └─ arena-fc-shim (PID 1, root, 6 caps)
             └─ jailer → firecracker (uid 9xxxxx, 0 caps, seccomp, chroot,
                 │                    cgroup memory/pids/cpuset, rlimits)
                 └─ KVM microVM                            ← SECURITY BOUNDARY
                     └─ arena-init (guest PID 1)
                         └─ candidate argv (uid 1000, cleared env, guest cgroup)
```

Per invocation:

1. **Images (host, unprivileged).** Each read-only mount is copied into a
   staging tree (rejecting symlinks, hardlinks, devices, fifos, sockets,
   `..`/absolute/over-long paths, normalizing modes to 0644/0755), hashed with
   the CONTRACTS §1 `TreeDigest`, and imaged with `mkfs.ext4 -d` (no journal).
   Images are cached by tree digest and are read-only (0444, attached
   `is_read_only`, `lost+found` removed so the guest sees exactly the tree);
   the cache is evicted LRU by allocated size (default cap 32 GiB; entries are
   hardlinked into job dirs, so eviction never disturbs a running VM). A
   `Rootfs::Image` (e.g. the pinned build toolchain, §4) is staged the same
   way, its `arena_archive` TreeDigest re-verified on the staged copy, and
   cached as `root-<digest>.ext4`. A fresh sparse scratch filesystem (`mkfs.ext4`, owned by
   the guest candidate uid) and a fresh raw output device are created for
   every run; the control drive (JSON job: argv, env, limits, mounts, nonce)
   is raw too. Kernel and rootfs are hardlinked (0444) from the pinned,
   digest-verified install; `SandboxSpec.rootfs_digest` must equal the
   installed rootfs digest or the run is refused.
2. **Delivery container.** `docker run --rm --network none --device /dev/kvm
   --cap-drop ALL --cap-add SYS_ADMIN,MKNOD,CHOWN,SETUID,SETGID,DAC_OVERRIDE
   --security-opt no-new-privileges --security-opt apparmor=unconfined
   --security-opt seccomp=<docker default + pivot_root> --read-only
   --cgroupns private --ipc none --memory M --memory-swap M --pids-limit 128
   --ulimit core=0 [--cpuset-cpus C] -v <jobdir>:/job arena-fc-runner run /job`.
   The image is `FROM scratch` with three static binaries (firecracker, jailer,
   arena-fc-shim): no shell, no libc, no package manager.
3. **Shim.** Makes its namespaced cgroup2 tree writable, moves itself into a
   leaf, moves the run's images into the jail directory, chowns only the two
   writable drives (0600) to a per-run random VMM uid, and starts
   `jailer --uid U --gid U --chroot-base-dir /job/jail --cgroup-version 2
   --cgroup memory.max=… --cgroup memory.swap.max=0 --cgroup pids.max=…
   [--cgroup cpuset.cpus=…] --resource-limit fsize=… --resource-limit
   no-file=256 -- --no-api --config-file vm.json`. Firecracker's default
   seccomp filters stay on (no `--no-seccomp`, no `--seccomp-filter`).
4. **VM.** `vm.json` attaches only virtio-blk drives — `vda` rootfs (ro),
   `vdb` control (ro), `vdc` output (rw, raw), `vdd` scratch (rw, ext4),
   `vde…` bundles (ro), optionally a root image (ro) — and the serial
   console. Every data drive has a Firecracker token-bucket rate limiter
   (default 512 MiB/s, 20k IOPS, 256 MiB one-time burst; configurable). **No network interface, no
   vsock, no balloon, no API socket, no MMDS.** Boot args: `console=ttyS0
   reboot=k panic=1 pci=off nomodule quiet init=/sbin/arena-init`, rootfs
   mounted read-only. The guest kernel has `CONFIG_MODULES` off.
5. **Guest init.** Mounts `/proc`, sysfs ro, cgroup2, `/dev/shm`. Builds the
   candidate root as a **read-only overlayfs** of a tmpfs mount-point skeleton
   over either the arena rootfs (bind of `/`, ro) or the job's root image,
   and mounts into it: `/proc` (`hidepid=2`), `/dev`, `/sys` (ro), the scratch
   disk at `/scratch` (nosuid,nodev; `/tmp` is a bind of `/scratch/tmp`) and
   the bundles read-only under `/in/…` / `/opt/…` — the same layout as
   bwrap-dev. Performs `copy_in` (regular files and directories only,
   `O_NOFOLLOW`, re-owned by the candidate) and `scratch_dirs`; sets
   `vm.overcommit_memory=1`; creates cgroup `job` with `memory.max = mem_bytes`,
   `memory.swap.max = 0`, `memory.oom.group = 1`, `pids.max = pids`; forks the
   candidate into it with `oom_score_adj 0` (init itself is −1000),
   `chroot` into the candidate root + `chdir(cwd)`,
   `RLIMIT_CORE=0`, `RLIMIT_NOFILE`, `RLIMIT_NPROC`, `setsid`,
   `PR_SET_NO_NEW_PRIVS`, `setgroups([])`, uid/gid 1000, a cleared env plus
   the allowlisted variables, stdin `/dev/null`, stdout/stderr to pipes
   truncated at 64 KiB. Setuid/setgid bits are stripped from the rootfs at
   build time. Init prints `ARENA-START <nonce>` on the console immediately
   before exec and `ARENA-EXIT <nonce>` immediately after `wait`. At
   `wall_timeout` (guest clock) init itself kills the cgroup and reports
   `TimedOut` with the truncated stdout/stderr; the host only hard-kills the
   VM if the guest has not exited `2 s + 2 %` later. Afterwards init kills the
   whole cgroup (`cgroup.kill`), writes the report and the scratch-relative
   `collect` paths (regular files only, `O_NOFOLLOW`; missing paths skipped;
   symlinks/specials are violations → `output_error`; limits on count, bytes,
   depth and path length) to the raw output drive, and reboots, which makes
   Firecracker exit.
6. **Teardown.** The shim records the VMM cgroup's `memory.peak`, `cpu.stat`,
   `memory.events`, `pids.peak`, moves the output image out, deletes the jail
   (and with it the scratch image), hands the job dir back to the host uid.
   The library decodes the output drive and deletes the job directory. No
   per-run state survives except the read-only, content-addressed bundle
   image cache.

### Measurement semantics (`SandboxOutcome`)

| field | source | authority |
|---|---|---|
| `exit` | guest init report (`Exited`/`Signaled`/`OomKilled`), host for `TimedOut` (and host-cgroup OOM) | see §2 |
| `wall_ns` | **host clock**: shim timestamps of the `ARENA-START`/`ARENA-EXIT` console lines (to the kill on timeout). Excludes VM boot. | authoritative unless the guest kernel is compromised (§2) |
| `cpu_ns` | host cgroup `cpu.stat usage_usec` of the VMM (vCPUs + device emulation, incl. ~60 ms boot/teardown) | authoritative |
| `peak_rss_bytes` | host cgroup `memory.peak` of the VMM: guest RAM actually touched + VMM overhead + host page cache charged for drive I/O | authoritative upper bound |
| `diagnostics.guest_*` | guest cgroup `cpu.stat`, `memory.peak`, guest wall clock | diagnostic only |
| `diagnostics.boot_ns`, `vmm_wall_ns`, `teardown_ns`, `total_ns` | host | diagnostic |

The per-candidate memory **limit** is enforced by the guest cgroup
(`memory.max = mem_bytes`), backed by a host cgroup limit of guest RAM
(`mem_bytes` + 128 MiB) + 96 MiB VMM overhead, backed by the container
memory limit (+64 MiB). The wall-clock **limit** is enforced on the host
(shim `cgroup.kill`, then the library's backstop `docker kill`).

## 2. Threat model by layer

The attacker controls the candidate executables and their inputs that it
authored (bundle, its own public params). It does not control the judge's
challenge, the rootfs, the kernel, init, the shim or the host.

| layer | protects against | if it falls, the attacker gets | notes |
|---|---|---|---|
| guest uid 1000 + no_new_privs + cgroup + rlimits | candidate tampering with init, the report, console markers, limits; fork bombs; memory hogs | **guest root**: can forge its exit code (it controls that anyway), the guest-reported diagnostics, and the timing markers (could print `ARENA-EXIT` early and keep working until the host timeout) | tested: console, kmsg, `/dev/vd*`, cgroup files are not writable; `CapEff=0`; NNP=1 |
| guest kernel (6.1 CI build, no modules) | — | same as guest root | a guest-kernel exploit is the realistic way to guest root; budget for it (below) |
| **KVM + Firecracker device model (virtio-blk, serial, i8042, RTC only)** | everything on the host | code execution as the jailed VMM uid on the host | **the security boundary.** Minimal device surface: no net, no vsock, no balloon, no API. Firecracker's own seccomp filter allows only its required syscalls. |
| jailer: chroot (pivot_root + mount ns), per-run uid, 0 capabilities, NNP, seccomp, cgroup memory/pids/cpuset, fsize/nofile rlimits | an escaped VMM reading host files, signalling other processes, exhausting host memory/pids, writing unbounded files | the escaped process sees only its jail: kernel/rootfs (0444, not owned), its own two drive files, `/dev/kvm`, `/dev/net/tun` (useless without `CAP_NET_ADMIN` and a netns with only `lo`), `/dev/userfaultfd` | verified on a live run: uid 906755, CapEff 0, NNP 1, Seccomp 2 (two filters), cpus pinned, `memory.max`, `pids.max=34`, `memory.swap.max=0` |
| delivery container: network none, pid/ipc/uts/mount/cgroup namespaces, Docker seccomp (+pivot_root), read-only rootfs, memory/pids limits, only `/job` mounted | an escapee that also defeats the chroot: no network, no other host paths, cannot see host processes | the container's root (shim) has `SYS_ADMIN` etc.; but the escaped process is a *different, unprivileged uid* with an empty capability set, so it would additionally need a local kernel privilege escalation | AppArmor is **disabled** for this container (see §3) |
| host kernel | — | host | shared with every tenant; patch promptly; KVM is the main attack surface |

Two consequences worth stating explicitly:

* **Guest compromise does not let a candidate cheat correctness.** The exit
  status, stdout, and outputs come from the guest, but they are candidate
  data anyway: the judge independently checks `claim.bin == expected_claim`,
  certified verifier artifacts are pinned by digest (ARTIFACT_BINDING), and
  verdicts never rely on a guest-reported number.
* **Guest compromise can shorten the measured `wall_ns`** by emitting the
  exit marker early. Bounds: the run still has to finish before the host
  timeout, outputs are only collected after the VMM exits, and the host
  also reports `vmm_wall_ns` (VMM lifetime, which cannot be forged). The
  benchmark should cross-check `wall_ns ≤ vmm_wall_ns − boot_ns` and flag runs
  where `vmm_wall_ns − wall_ns` deviates from the calibrated boot+teardown
  overhead (p95 ≈ 120 ms here), or score on `vmm_wall_ns − calibrated
  overhead` for the official board.

### Escape-attempt detection (`SANDBOX_VIOLATION`)

Containment alone makes escape attempts harmless but silent. The sandbox
inits (guest `arena-init`; bwrap-dev helper init) therefore install a seccomp
**user-notification** filter (`runners/seccomp`) on the candidate tree as the
last step before exec (after the uid drop and `no_new_privs`). Listed
syscalls block and are delivered to the init over a listener fd that the
child creates with `SECCOMP_FILTER_FLAG_NEW_LISTENER`, passes over a
close-on-exec socketpair and closes — the candidate never holds it. The init
records the event and answers `-EPERM`: the call never executes, and the
outcome's `violations` lists it. The worker turns any violation into
`SANDBOX_VIOLATION` on the gate of the job that ran the command; the formal
checker turns it into a `SANDBOX_VIOLATION` finding.

| policy | used for | violations |
|---|---|---|
| `strict` (default) | `prepare` / `prove` / `verify`, benchmark batches | kernel attack surface: `ptrace`, `process_vm_{readv,writev}`, `pidfd_getfd`, the mount family (`mount`, `umount2`, `pivot_root`, `chroot`, `open_tree`, `move_mount`, `fs*`, `mount_setattr`), `unshare`, `setns`, `open_by_handle_at`, module and `kexec` loading, `bpf`, `perf_event_open`, keyrings, `syslog`, setting clocks/time/hostname, swap, `reboot`, `iopl`/`ioperm`, `quotactl`, `acct`, … ; `socket(AF_INET/AF_INET6/AF_NETLINK/AF_PACKET)`; any non-x86_64 or x32 ABI syscall |
| `tooling` | build recipes, Lean elaboration/rechecking | the same minus the socket rule (a network attempt in a build simply fails and is judged by its effect, e.g. `BUILD_FAILED`) |
| `off` | — | — |

**Sound** (no false positives): an entry exists only if a process of the
candidate tree executed that syscall with those arguments; filters are
inherited by every descendant and cannot be removed. Not complete: an attempt
whose task is killed before the init reads the notification is blocked but may
go uncounted; socket creation through `io_uring` (`IORING_OP_SOCKET`) is not
inspected (there is no network either way); file accesses are not classified
(a failed write to a read-only mount is indistinguishable from an
honest-but-buggy program, so `sandbox-escape-filesystem` stays
`PROVER_FAILED`). Validated free of false positives on: the toy candidate
(e2e), `stark-plonky3` (build under `tooling` + prepare/prove/verify under
`strict`, `runners/firecracker/scripts/honest-backend-check.sh`), `zkvm-sp1`
(same script), `reexec-witness` end to end on Firecracker
(`tests/e2e/milestone-d.sh`: the reference and its PROVER_ONLY child ADMITTED
with all 13 gates PASS — build, FORMAL_CHECK incl. native-lean, conformance,
adversarial, benchmark — and both NEAR hostile cases as expected), the
30-case formal-checker corpus (bwrap-dev and Firecracker) and the gated
worker/Firecracker suites. See `docs/e2e-results/hostile-seccomp/`.

### Host-side parsing of guest-written data

The host never mounts, fsck's or otherwise parses a filesystem the guest
wrote. The scratch ext4 image is deleted unread. The only guest-written data
the host reads is the raw output drive, decoded by `arena-fc-proto` with
explicit limits: magic + version; report JSON ≤ 64 KiB; stdout/stderr ≤ 64
KiB each; per-file path validation (relative, ≤ 255 bytes, no `.`/`..`/empty
components, no NUL/backslash/control chars), no duplicates, no file/dir
conflicts, file-count and total-byte limits, record sizes bounded by the
device size, and a trailer whose counts must match. Files are created with
`O_CREAT|O_EXCL|O_NOFOLLOW` under an empty output directory we own. The
report must echo the per-run nonce. A malformed stream is
`InfraError::GuestProtocol` (→ `SANDBOX_VIOLATION`) and partial outputs are
deleted.

## 3. What the Docker wrapper does and does not add

Why it exists: the worker user cannot open `/dev/kvm` on this host and the
jailer needs root to build its chroot. Docker (rootful) gives a root process
with KVM access without granting the worker user root on the host. It is a
**delivery mechanism**; the guarantees above do not depend on it, except the
"second fence" row.

It adds: separate pid/ipc/uts/mount namespaces, `--network none` (netns with
only `lo`), a read-only `FROM scratch` root with three binaries, only `/job`
bind-mounted, memory/pids/cpuset limits on everything inside, Docker's seccomp
profile, `no-new-privileges`, `--cap-drop ALL` + 6 capabilities.

It does **not** add: protection against the host kernel/KVM attack surface
(shared), or anything against an attacker who obtains the shim's root.

Capabilities — each verified necessary by removing it alone and re-running
(`ARENA_FC_CAPS=… arena-fc-run …`):

| cap | needed for | failure without it |
|---|---|---|
| `SYS_ADMIN` | remount the namespaced cgroup2 fs rw (shim); jailer `unshare(CLONE_NEWNS)`, bind mount, `pivot_root` | `remount /sys/fs/cgroup rw: EPERM` |
| `MKNOD` | jailer creates `/dev/kvm`, `/dev/net/tun`, `/dev/userfaultfd` in the jail | `Failed to create /dev/net/tun via mknod: EPERM` |
| `CHOWN` | jailer chowns jail + device nodes to the VMM uid; shim chowns writable drives and reclaims/returns directories | `chown /job: EPERM` |
| `SETUID`, `SETGID` | jailer drops to the per-run VMM uid/gid before exec | `Failed to exec into Firecracker: EPERM` |
| `DAC_OVERRIDE` | jailer creates `/dev` etc. inside the chroot it already handed to the VMM uid | `Failed to create directory /dev: EACCES` |

Not granted (Docker defaults dropped): `SYS_CHROOT` (verified unnecessary:
jailer uses `pivot_root`), `FOWNER`, `FSETID`, `KILL` (the shim kills via
`cgroup.kill`), `NET_RAW`, `NET_BIND_SERVICE`, `SETPCAP`, `SETFCAP`,
`AUDIT_WRITE`.

Security options:

* **seccomp**: Docker's default profile (moby v28.0.0, sha256 pinned in
  `deploy/images/firecracker/PINS`) plus one rule allowing `pivot_root` when
  `CAP_SYS_ADMIN` is held (without it: `Failed to pivot root: EPERM`).
  Generated by `deploy/images/fc-runner/build.sh`.
* **AppArmor `unconfined`**: Docker's `docker-default` profile denies
  `mount`, which both the shim (cgroup remount) and jailer (mount
  propagation, bind mount) need (`Failed to change the propagation type to
  slave: EACCES`). Loading a custom AppArmor profile requires host root,
  which this lane deliberately did not use. Production: load a dedicated
  profile allowing exactly `mount`/`remount` on `/sys/fs/cgroup/` and
  `/job/jail/**`, `pivot_root`, and nothing else.
* Membership in the `docker` group is root-equivalent on the host. Treat the
  worker account as privileged infrastructure (it is not reachable by
  candidates: they never execute outside a VM).

**Production recommendation**: run jailer + Firecracker natively from a small
root-owned supervisor (systemd unit, `DeviceAllow=/dev/kvm`) on dedicated
runner hosts, dropping Docker, or keep Docker but with the custom AppArmor
profile above. The library's container invocation is isolated in
`FirecrackerSandbox::run_container` to make that swap local.

## 4. Pins and reproducibility

`deploy/images/firecracker/PINS` (fetch with `fetch.sh`, binaries stored in
`/data/illia/nearproof-deps/firecracker`, never in git):

| artifact | pin |
|---|---|
| Firecracker / jailer | v1.17.0 release tgz `06094a11…ade558`; firecracker `99ad0f5c…5de7a5`, jailer `65ef226e…c9c8434f` (full digests in PINS) |
| guest kernel | Firecracker CI `vmlinux-6.1.155` (`firecracker-ci/v1.15`), `e20e46d0…af53af3d4f2`; config `024b2aae…bef7c3`; `CONFIG_MODULES` off (checked) |
| rootfs base | `debian:bookworm-slim@sha256:88200866…07ea4171` (glibc; matches typical Rust build images) |
| build toolchain base | `rust:1.96.0-slim-bookworm@sha256:4732ca96…198e1950` (rustc/cargo 1.96.0, gcc 12.2 as `cc`) |
| Docker seccomp base | moby v28.0.0 `default.json`, `9c1025c8…ae9c76` |

The rootfs is rebuilt by `deploy/images/rootfs/build.sh`: the base is
`docker export`ed, extracted into a tmpfs, setuid bits stripped, `arena-init`
(static musl, path-remapped, stripped) added, mtimes clamped to
`SOURCE_DATE_EPOCH`, ext4 built with fixed UUID/hash seed and
`E2FSPROGS_FAKE_TIME`, and inode ctimes clamped with `debugfs` (mke2fs copies
them from the source tree). `build.sh --check` builds twice and fails unless
the images are bit-identical (verified). The resulting digest is the value
challenges pin in `SandboxSpec.rootfs_digest`.

**Build toolchain image** (`deploy/images/toolchain/build.sh [--check]`): the
pinned Rust image is flattened into a directory satisfying the CONTRACTS §1
tree rules — symlinks dereferenced, hardlinks split, dangling links dropped,
setuid/sticky bits cleared, Docker-managed `/etc/{hostname,hosts,resolv.conf}`
normalized, and the 8 case-colliding kernel netfilter headers
(`xt_CONNMARK.h` vs `xt_connmark.h`, …) reduced to their lowercase member —
and named by its TreeDigest under
`/data/illia/nearproof-deps/toolchain-images/<hex>/`, with `<hex>.json`
recording base image, `rustc`/`cc` versions and the env a build uses
(`PATH=/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:…`,
`CARGO_HOME=/scratch/.cargo`, `CARGO_NET_OFFLINE=true`). Two flattenings are
identical (`--check`, verified): current digest
`sha256:57a89fc6…28ebc117` (8879 files, 1.84 GB). This digest is the
`BuildJob.toolchain_image` / `toolchain_image` evidence of
BUILD_REPRODUCIBLE; the worker re-hashes the directory and the Firecracker
backend re-verifies the staged copy before imaging it. No Lean toolchain is
included (the formal checker has its own pinned environment).

**Lean checker image** (`deploy/images/lean-checker/build.sh [--check]`):
the candidate root for formal checking (runners/formal-checker) and for the
judge-built `verify_route = "native-lean"` verifier. Same tree rules and
naming as the toolchain image (`deploy/images/lib/sanitize_tree.py`).
Contents, at the guest paths the formal checker uses:
`/arena/tc` = Lean v4.34.1 release toolchain (tarball sha256 pinned; elan-free;
`lean`, `lake`, `leanchecker`, `leanc` with its bundled clang + lld + glibc
stubs, so `lean -c` + `leanc` link native executables without a system C
compiler), `/arena/tools/{lean4export,nanoda_bin,lean4lean,arena-audit}` built
from source at the revisions in `runners/formal-checker/tools.toml` (lake in a
pinned `buildpack-deps:bookworm-scm` builder; nanoda in the pinned Rust image,
`--locked`, path-remapped, stripped; ArenaAudit from this repository), on a
flattened pinned `debian:bookworm-slim` userland. `--check` performs two fully
independent builds (tools recompiled from source) and requires equal
TreeDigests — verified:
`sha256:706f29e08fcb5dfddc3d90eeb945a6a53c0c20b3cb4e8604848f02e4404826cc`
(23 022 files, 4.08 GB; one build ≈ 63 s on 32 cores). `<hex>.json` records
the toolchain, tarball and builder digests and each tool's revision + sha256.

The formal checker's `UntrustedRunner` seam maps onto the Firecracker backend
with: the image as `root_image`; read-only mounts whose host path *is* the
same file inside the image dir are served by the image (the checker's
`ToolPaths` point into the image, so its cache key covers the same bytes);
**read-write dirs** (`RunRequest::rw_dirs`: seeded from a read-only drive —
judge-planted symlinks allowed — kept on scratch, bind-mounted at the guest
path, and written back: new/changed regular files only, host symlinks never
followed or replaced, guest-made symlinks never returned); stdout redirected
to a file in a read-write dir for reports over 64 KiB;
`allow_mount_symlinks` for the judge's `.olean` link farms (symlinks are part
of the image cache key). The reference adapter is
`runners/firecracker/tests/lean_checker.rs::FirecrackerLeanRunner`; when
`arena_sandbox::SandboxSpec` gains `rw_binds` (runners-core), `translate`
maps them to `rw_dirs`.

*Offline dependencies*: the build VM has no network and no registry. Rust
packages vendor their dependencies (`cargo vendor`) inside the package and
point `.cargo/config.toml` `[source.crates-io] replace-with` at the vendored
directory; `cargo build --offline --locked` then verifies the vendored
`.cargo-checksum.json` files against `Cargo.lock`. The gated worker test
`build_through_firecracker_with_pinned_toolchain` builds exactly such a
package (vendored crate + C file via `cc`) twice in microVMs and requires
bit-identical outputs.

## 5. Measured on this host (Linux 6.8, 32 cores, KVM via Docker)

`runners/firecracker/scripts/latency.sh` (release build, `/bin/true`,
256 MiB, 1 vCPU):

| phase | sequential p50 / p95 | 8 in parallel p50 / p95 |
|---|---|---|
| boot: jailer spawn → guest start marker | 60 / 81 ms | 82 / 87 ms |
| candidate wall (`/bin/true`, host clock) | 8.9 / 9.2 ms | 8.6 / 10.8 ms |
| teardown: exit marker → VMM exit (report + reboot) | 22 / 36 ms | 28 / 42 ms |
| VMM lifetime | 93 / 125 ms | 119 / 133 ms |
| end to end incl. `docker run` | 232 / 270 ms | 345 / 415 ms |
| host cgroup CPU per run | 65 / 88 ms | 85 / 90 ms |
| host cgroup memory.peak | 52 MiB | 52 MiB |

Other measurements: `sleep 1` measures 1007–1010 ms on the host clock
(marker to marker), agreeing with the guest's own clock within 0.6 ms; a 1 GiB output file is collected
and hashed in ≈ 3.4 s; a 16 GiB scratch disk costs no extra preparation time
(sparse + lazy init); host-side preparation (images, hashing kernel+rootfs at
sandbox construction) adds ≈ 0.1 s. Disk rate limiting: a 48 MiB `O_DIRECT`
write to scratch takes 18 ms with the default limits and 3.6 s at a 16 MiB/s
limit. Toolchain image: first use (stage 1.84 GB + verify digest + `mkfs`)
≈ 14 s, cached afterwards; `rustc -V; cargo -V; cc --version` inside it in a
VM ≈ 0.3 s; the full worker build test (two Rust+C builds + conformance)
≈ 19 s.

Lean in microVMs (lean-checker image): first use stages + images the 4.08 GB
root once (≈ 27 s), cached afterwards. The **entire formal-checker corpus
(30 cases: 4 positive, 26 negative) passes through Firecracker** with the
expectations of `tests/corpus/*/expect.json` — 150 microVM runs, mean 2.3 s
per run (Lean start + `.olean` loading over virtio-blk), 10–33 s per case,
423 s serial; all four recheckers (leanchecker, nanoda, lean4lean,
arena-audit + NDJSON audit) ran in VMs. `lean -c` + `leanc` + run of a
native verifier inside a VM: 1.6 s.

## 6. Residual risks and follow-ups

1. **AppArmor disabled for the delivery container** and Docker-group =
   root-equivalent (see §3). Fix: custom AppArmor profile or native
   supervisor on dedicated hosts.
2. **Guest kernel is a Firecracker CI build**, not an arena-built, hardened
   kernel. Follow-up: build from a pinned config (no modules, no unneeded
   drivers/filesystems/syscalls such as io_uring, userfaultfd, BPF for
   unprivileged users), reproducibly.
3. **Timing under guest-kernel compromise** (§2): cross-check
   `wall_ns` against `vmm_wall_ns`.
4. **Microarchitectural side channels** between concurrent tenants: pin VMs
   to dedicated physical cores (`cpu_set`), disable host SMT on benchmark
   hosts, never co-schedule a candidate with secret-holding processes. The
   VM has no secrets (no witness of another tenant ever enters it).
5. **Host page cache** is charged to the VMM cgroup, so `peak_rss_bytes`
   includes drive I/O cache; use the guest figure to reason about the
   candidate's own RSS.
6. **Timeouts** keep stdout/stderr only when the guest enforces them; if the
   guest is wedged (or compromised) the host hard-kill still loses them.
7. **Bundle staging** reads every byte on every run (hash + copy) before the
   cache lookup; for multi-GiB public params cache by (path, inode, mtime) to
   skip re-staging. The cache is LRU-evicted by size.
8. **Disk I/O rate limits** are global defaults, not per-challenge policy;
   the output drive is limited too, which bounds collection speed
   (≈ 512 MiB/s).
9. The Rust **toolchain image** has no Lean (Lean lives in the separate
   lean-checker image), and both images duplicate `/usr/lib` by
   dereferencing the merged-usr symlinks. Read-write dirs do not propagate
   deletions, and each formal-checker step re-stages its (small) read-only
   inputs.
10. The jailer is run without `--new-pid-ns` (the container already provides
   a pid namespace, and `--new-pid-ns` daemonizes, which breaks waiting).

## 7. GPU route (SPECIFIED, NOT IMPLEMENTED)

No GPU exists on the development host, so nothing below is implemented or
tested. Firecracker has no PCI/GPU passthrough; a GPU candidate therefore
needs a different VMM or a whole-machine boundary. The requirements are the
same as the CPU route: the candidate never shares a kernel, a GPU context or
GPU memory with another tenant or with the arena, and the measurements are
taken outside the candidate's control.

**Option A — dedicated disposable GPU workers (preferred for simplicity).**
One bare-metal (or full cloud VM) GPU instance per job, imaged from a pinned,
measured image (kernel, NVIDIA driver, CUDA userspace, arena-init equivalent),
with no network except an attested job-fetch/result-upload channel to the
control plane, destroyed (not reused) after the job. Measurement is done by a
supervisor outside the instance (cloud API / BMC timestamps for lifecycle and
a host agent that is not reachable by the candidate), or by an
in-instance agent whose results are only trusted for diagnostics.

**Option B — VFIO passthrough into a microVM** (cloud-hypervisor or QEMU
`-M q35` with `vfio-pci`), on a host the arena controls:

* **IOMMU required** (`intel_iommu=on`/`amd_iommu=on`), the GPU and every
  function in its IOMMU group bound to `vfio-pci`; never pass through a GPU
  whose group contains other host devices. No peer-to-peer (disable
  NVLink/P2P to devices outside the VM), ACS enabled on the path.
* **One tenant per physical GPU at a time.** No MPS, no shared time-slicing,
  no MIG sharing between tenants (MIG partitions may be used only if each
  partition is passed to one VM *and* the threat model accepts shared
  L2/memory controllers — default: not allowed for scored runs).
* **Device reset between tenants**: function-level reset or secondary bus
  reset via VFIO after every VM, verified by re-reading the device state; if
  the reset fails, the GPU is quarantined, not reused.
* **VRAM scrub**: after reset, a trusted scrubber VM (arena image) writes and
  verifies a pattern over all VRAM (and clears ECC error counters) before the
  device is returned to the pool; the scrub result is logged with the job.
* **Driver/firmware pinning**: the guest image pins the NVIDIA driver and CUDA
  versions (digests in a PINS file like the CPU route); the host pins the GPU
  VBIOS/firmware version and refuses devices whose firmware differs
  (a candidate with device access must not be able to persist firmware
  changes — use GPUs/firmware that support signed firmware and verify the
  version after every job).
* **Host-side completion measurement**: as in the CPU route, the guest emits
  start/exit markers on a host-observed serial console and the host timestamps
  them; the VMM process lifetime bounds them; GPU utilization/power from the
  host side (NVML is not available on the host once the GPU is bound to
  vfio-pci, so use BMC/PDU telemetry for power) is diagnostic.
* No network device, no shared filesystems (virtio-fs is not allowed), raw
  output drive decoded with limits, exactly as on the CPU route.
* VMM hardening: cloud-hypervisor with its seccomp filters and a jailer
  equivalent (dedicated uid, chroot/mount ns, cgroup limits); QEMU only with
  `-sandbox on`, a minimal machine type and no default devices.

Either option needs a GPU host lab to validate reset/scrub behaviour on the
exact GPU SKU before any GPU result can be admitted; until then GPU challenges
must not be offered at tier `formal`.

## 8. Commands

```bash
# one-time: pinned binaries + kernel, reproducible rootfs, delivery image
deploy/images/firecracker/fetch.sh
deploy/images/rootfs/build.sh --check      # builds twice, compares
deploy/images/fc-runner/build.sh           # prints image id, writes seccomp profile

# run something
cargo run -p arena-firecracker --bin arena-fc-run -- --mem-mb 256 --cpus 2,3 \
    --ro /path/bundle:/in/bundle -- /in/bundle/out/prove --help
# build-style run: copy the package into scratch, build with the toolchain image
cargo run -p arena-firecracker --bin arena-fc-run -- --mem-mb 2048 \
    --root-image /data/illia/nearproof-deps/toolchain-images/<hex> \
    --env PATH=/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin \
    --ro /path/pkg:/in/pkg --copy-in /in/pkg:work --cwd /scratch/work \
    --collect work/out -- ./build-recipe/build.sh

# tests (boot real VMs) and latency
deploy/images/toolchain/build.sh --check    # pinned build toolchain image
ARENA_FC_TESTS=1 cargo test -p arena-firecracker -- --test-threads=4
ARENA_FC_TESTS=1 ARENA_DEV_UNSAFE=1 cargo test -p arena-worker --test firecracker
deploy/images/lean-checker/build.sh --check          # pinned Lean checker image
ARENA_FC_TESTS=1 cargo test -p arena-firecracker --test lean_checker -- --nocapture
ARENA_FC_TESTS=1 FC_CASES=$(ls runners/formal-checker/tests/corpus | paste -sd,) \
  cargo test -p arena-firecracker --test lean_checker corpus -- --nocapture   # all 30
runners/firecracker/scripts/latency.sh 30 1
```
