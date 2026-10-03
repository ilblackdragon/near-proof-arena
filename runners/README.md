# runners — judge-side execution

Crates (runners-core lane unless noted):

| crate | path | what |
|---|---|---|
| `arena-archive` | `runners/archive` | safe `tar` / `tar.zst` ingestion, `TreeDigest`, package layout + `candidate.toml` validation, deterministic `pack_tree` |
| `arena-sandbox` | `runners/sandbox` | the `Sandbox` trait (CONTRACTS §9) and the `bwrap-dev` backend (**DEMO-only**) |
| `arena-firecracker` | `runners/firecracker` (runners-vm lane) | production microVM backend; implements `arena_sandbox::Sandbox` |
| `arena-measure` | `runners/measure` | trusted measurement harness and the bench-spec-v1 score function |
| `arena-worker` | `runners/worker` | `arena-worker` daemon: lease → fetch by digest → sandbox → upload → complete |

Untrusted code runs **only** through `Sandbox::run`. Nothing the candidate
prints or writes is used for measurement; every artifact the worker reads
from the store is re-hashed against its digest; every tree the sandbox hands
back is re-ingested with the hostile-archive checks.

## Testing

```sh
export RUSTC_WRAPPER=sccache
ARENA_DEV_UNSAFE=1 cargo test -j 8 -p arena-archive -p arena-sandbox -p arena-measure -p arena-worker
# real microVMs (docker group + /dev/kvm via the fc-runner image, assets from deploy/images/*):
ARENA_DEV_UNSAFE=1 ARENA_FC_TESTS=1 cargo test -j 8 -p arena-firecracker -p arena-worker
```

The bwrap tests **fail** (they do not skip) without `ARENA_DEV_UNSAFE=1`,
bubblewrap and unprivileged user namespaces. `ARENA_SANDBOX_CGROUP=off`
forces the rlimit fallback; `=require` refuses to run without a delegated
cgroup.

## archive

`ingest(reader, dest, limits)` streams the archive (zstd detected by magic)
into a directory it creates (mode 0700) and removes on any error. Rejected:
symlinks, hardlinks, char/block devices, fifos, sparse and other exotic entry
types; absolute paths, `.`/`..`/empty components, backslashes, control
characters, non-UTF-8, > 255 bytes (incl. GNU long names / PAX paths);
duplicates; case/NFC collisions (`README.md` vs `readme.md`, `é` vs `e◌́`);
file-vs-directory conflicts; setuid/setgid/sticky bits; > 100 000 entries;
> 2 GiB expanded (checked against the header *before* reading and against
bytes actually copied); > 256 MiB compressed; decompressed/compressed ratio
> 200 once past 16 MiB (checked continuously, so a 1 GiB-of-zeros bomb is
aborted after a few MB); zstd window > 128 MiB. Files are created
`O_CREAT|O_EXCL|O_NOFOLLOW`, then chmod 0644/0755 (exec iff any x bit).

TreeDigest = `Digest(JCS([[path, "file"|"exec", "sha256:…"], …]))`, sorted by
path bytes, directories not included — computed through the shared
`arena_types::tree_digest_entries`.

`validate_package(root, tree)` checks, against the extracted tree (no TOCTOU):
`candidate.toml` is a regular file ≤ 64 KiB parsed by
`CandidateManifest::parse`; `README.md`, `source/`, `dependency-locks/`,
`build-recipe/` exist (and `formal.lean_project` when present);
`build.recipe` is an **executable** file under `build-recipe/`;
`build.outputs` has 1–64 unique, non-nested entries, none already present in
the package (the judge builds them; pre-built outputs are refused); every
`entry.*` lies in `build.outputs`. `sdk/arena-cli`'s `check-local` calls
this crate, so the SDK and the judge cannot disagree.

Tests: hostile fixtures generated in-test (raw ustar headers bypass the tar
crate's own checks), a real zstd bomb, PAX traversal, lying size headers,
truncated streams; property tests for roundtrip (tar/zstd → ingest →
`tree_from_dir` → `pack_tree` → ingest), path normalization, and random
garbage / random header corruption never writing outside the destination.

## sandbox

```rust
pub trait Sandbox: Send + Sync {
    fn name(&self) -> &str;
    fn tier_cap(&self) -> Option<Tier>;      // Some(Demo) for dev backends
    fn layout(&self) -> GuestLayout;          // guest paths differ per backend
    fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, InfraError>;
}
```

`SandboxSpec { rootfs, ro_mounts, rw_scratch_mb, copy_in, scratch_dirs, argv,
cwd, env (allowlist), cpu_set, mem_bytes, pids, wall_timeout, network: None,
collect, out_dir, max_output_bytes, output_trunc_bytes }`.
`SandboxOutcome { exit: Exited(code)|Signaled(sig)|TimedOut|OomKilled|ExecFailed,
wall_ns, cpu_ns, peak_rss_bytes, max_process_rss_bytes, stdout/stderr (truncated
+ totals), outputs [(path, Digest)], outputs_tree, output_error,
pids_limit_hit, limits, isolation, tier_cap, entry_wall_ns, diagnostics }`.

### bwrap-dev (DEMO-only)

Refused unless `ARENA_DEV_UNSAFE=1` (checked at construction **and** on every
run); every outcome is stamped `isolation = "bwrap-dev (DEMO-only)"`,
`tier_cap = Some(Demo)`, and the worker adds `DEMO_ONLY` to every gate that
ran candidate code through it.

```
supervisor
 └─ systemd-run --user --scope -p Delegate=yes --unit arena-sbx-*   (if delegation works)
     └─ arena-sandbox-helper shim   host: child cgroup <scope>/sandbox with memory.max,
         │                          memory.swap.max=0, memory.oom.group=1, pids.max,
         │                          cpu.max (= |cpu_set| × 100%); affinity; wall timeout
         │                          (cgroup.kill + SIGKILL); wall clock, wait4 rusage,
         │                          memory.peak, cpu.stat, memory.events, pids.events
         └─ bwrap --unshare-all --unshare-user --disable-userns --die-with-parent
             │    --new-session --as-pid-1 --clearenv, ro /usr (+merged-usr links,
             │    ld.so files), --proc, --dev (remounted ro), 16 MiB /dev/shm,
             │    sized tmpfs /scratch (/tmp → /scratch/tmp), ro input mounts,
             │    / remounted ro, uid/gid 1000, hostname arena-sandbox
             └─ /.arena/helper init    PID 1, non-dumpable: copy-in, mkdirs, starts the
                 │                     entry point (setsid, RLIMIT_CORE=0, FSIZE, NOFILE,
                 │                     + AS/NPROC in rlimit-fallback mode), reaps; when
                 │                     the entry point exits, kill(-1, SIGKILL) and reap
                 │                     everything, then streams `collect` paths as tar
                 └─ entry point
```

The host re-ingests the output tar with `arena-archive` (symlinks, fifos,
oversize → `output_error`, outputs empty). Without user cgroup delegation the
backend falls back to rlimits (`limits = Rlimit`): memory via `RLIMIT_AS`
(OOM then shows up as a failed exit, not `OomKilled`), processes via
`RLIMIT_NPROC` counted in the sandbox's user namespace.

Tests (`runners/sandbox/tests/bwrap.rs`, `refuse.rs`): refusal without the
env var; network denied (only `lo`, no TCP to the internet or to host
services, no DNS); `$HOME`, `/home`, `/data`, `/root`, `/etc/passwd`,
`/run`, `/var`, cgroupfs and a host temp file are invisible; writes outside
scratch fail (`/`, `/usr`, `/etc`, ro mounts, `/.arena`, `/proc`, `/dev`);
scratch and `/dev/shm` are size-limited; fork bomb contained (cgroup and
rlimit modes; `pids_limit_hit`); memory limit → `OomKilled` with
`peak ≤ limit` (cgroup) / failure (rlimit); timeout kills setsid'ed
grandchildren (checked with `pgrep` on the host); background daemons die with
the entry point; exact env (`HOME LANG PATH PWD TMPDIR TZ`, a supervisor
canary does not leak, `DATABASE_URL`/`LD_PRELOAD` refused); outputs collected
and digested; hostile outputs rejected; stdout truncation; copy-in; init
cannot be killed/inspected from inside.

### firecracker (runners-vm lane)

`FirecrackerSandbox` implements the trait with `tier_cap = None` and layout
`/arena/scratch` + `/arena/in`. It does not support `copy_in`,
`scratch_dirs`, a non-scratch `cwd`, or collecting paths outside `out/`
(`GuestLayout::flexible_scratch = false`); outputs come back as `out/<path>`.
`InfraError::GuestProtocol` (forged guest report) becomes a
`SANDBOX_VIOLATION` FAIL in the worker.

## measure

`score.rs` implements docs/BENCHMARK_SPEC.md §8 exactly and passes every
integer output of `benchmarks/testvectors/score.json` (SplitMix64, median/MAD,
`derive_seed`, score incl. all error codes, bootstrap, schedule, outliers,
drift) — `runners/measure/tests/testvectors.rs` reads the file directly.

`run_session(plan, runner)` builds the seeded schedule (cold → warmup →
measured → fresh-confirm rounds, per-round Fisher–Yates order), runs each
batch through a `BatchRunner`, takes times **only** from
`SandboxOutcome::wall_ns` (`BatchSample` can only be filled from outcomes),
flags outliers (never drops), applies the caching tripwire, and computes the
point score + bootstrap half-width. One failed run fails the session (no
partial credit).

## worker

`arena-worker` (also the sandbox helper via `arena-worker
__arena-sandbox-helper`, so one binary is deployed).

* Config: env or `ARENA_WORKER_CONFIG` TOML — `ARENA_SERVER_URL`,
  `ARENA_WORKER_TOKEN`/`_FILE`, `ARENA_WORKER_ID`, `ARENA_WORK_DIR`,
  `ARENA_SANDBOX_BACKEND` (`bwrap-dev` | `firecracker`), `ARENA_WORKER_KINDS`,
  `ARENA_BUILD_MOUNTS` (`host:/opt/...`), `ARENA_BUILD_PATH`,
  `ARENA_BUILD_ENV`, `ARENA_IMAGES_DIR`, `ARENA_BENCH_CPUS`. The worker
  **refuses to start** if `DATABASE_URL`, `PG*`, or any postgres URL /
  `database` key is visible to it.
  `ARENA_FIXTURES_DIRS` (public fixtures, matched to challenges by
  TreeDigest), `ARENA_CONFORMANCE_SAMPLES` (default 8),
  `ARENA_FORMAL_CONFIG` (JSON: trusted Lean packages + expected-statement
  template per `relation_decl`; without it the worker does not lease
  FORMAL_CHECK), `ARENA_DEV_BENCH_BATCH_CAP` (DEV ONLY, recorded in
  `measured_by`), `ARENA_LEASE_SECONDS`.
* Types and transport: `server/arena-jobs` is the single source (`JobSpec`,
  `JobResult`, `BuildOutputs`, wire types, `WorkerClient`). Endpoints:
  `POST /internal/v1/jobs/lease`, `POST /internal/v1/jobs/{id}/heartbeat|complete|fail`
  (fenced by `lease_id`), `GET|PUT /internal/v1/artifacts/{digest}`.
  Heartbeat `cancelled` or a 409/410 cancels the job (never completed).
  Infra errors → `fail{retryable: true}`; tier above the sandbox cap,
  unknown protocol or a sandbox violation → `retryable: false`.
* Each job reports **only the gates its kind owns** (`JobKind::owned_gates`);
  every reported artifact is uploaded before `complete`.
* Oracles (`oracle.rs`) are selected by `claim_encoding.format`; built in:
  `demo-toy-arith-v1`. Unknown formats leave the conformance / adversarial /
  benchmark gates `UNKNOWN`. Sampled workloads use public
  `derive_seed("workload", class, challenge, package)` seeds (the
  season-secret HMAC of BENCHMARK_SPEC §11.1 is not wired yet).

| job | gates | notes |
|---|---|---|
| VALIDATE | `PKG_WELLFORMED` | archive + layout + manifest; challenge id, security profile, GPU request; runs no candidate code (no `DEMO_ONLY`) |
| BUILD | `BUILD_REPRODUCIBLE` | recipe offline twice in fresh scratch; output trees compared (differing paths listed); judge-run `prepare` twice (nondeterministic → `BUILD_NOT_REPRODUCIBLE`); `BuildOutputs` = entry digests, bundle/public TreeDigests + uploaded archives (`bundle_archive`, `public_archive`), `formal_tree`, toolchain digest |
| FORMAL_CHECK | `FORMAL_*`, `AXIOM_AUDIT` (+ `ARTIFACT_BINDING` UNKNOWN: not implemented) | `runners/formal-checker` through the shared sandbox (`SandboxRunner`); formal tree re-bound to the verified surface; recheckers from `toolchain_policy` |
| CONFORMANCE | `CONFORMANCE_DIFFERENTIAL`, `PROVER_RELIABILITY`, `RESOURCE_LIMITS` | bundle + public dir fetched by archive digest and re-bound by TreeDigest; public fixtures + sampled cases; `prove` with witness, claim bytes vs judge oracle; `verify` in a **separate** sandbox (public dir, claim, proof only); fail-fast; non-public case ids never in summaries |
| ADVERSARIAL | `ADVERSARIAL_PROOFS` | 3 honest proofs produced and verified twice (rejected → `UNKNOWN`, flip → `VERIFIER_NONDETERMINISTIC`); generic mutators + the adversarial lane's `adv:*` (≤ 240 inputs, deterministic subsample); any acceptance → `HOSTILE_PROOF_ACCEPTED` |
| BENCHMARK | `BENCHMARK` | classes/weights/batch sizes/procedure from the challenge, batches sampled by the oracle; every proof claim-checked and verified (failure → `BENCHMARK` FAIL with its reason); `prepare` timed; VMM wall cross-check; excessive outliers → whole session re-measured (≤ 3) then infra; `CACHING_SUSPECTED` → `UNKNOWN`; no frozen baselines → measured, unscored (the server recomputes scores anyway) |

## End-to-end (`make e2e`)

`tests/e2e/run.sh [--keep] [--hostile] [--hostile-only a,b]`: builds
`arena-server`, `arena-worker` and the `arena` CLI; recreates its own
database (`arena_e2e_*`) on the shared Postgres; starts the server (dev,
ports 18471/18472) with the signed demo challenge and the dev governance
key; starts a real `arena-worker` (bwrap-dev); submits
`tests/e2e/toy-candidate` (C reference candidate for `demo-toy-arithmetic`)
with `arena submit`; asserts DECIDED, every required gate PASS from real
judge work, DEMO tier, `rank: null`. `--hostile` then runs
`adversarial/e2e/run.sh` against the same server (per-case JSON report in
the work dir).

## Known gaps

* Builds and formal checks need `copy_in` / read-write dirs (bwrap-dev only).
  The runners-vm lane's in-flight firecracker protocol v2 adds copy-in/cwd;
  the shared host's fc-runner image was already rebuilt for v2, so the
  firecracker tests on this branch fail with `shim: bad job` until that
  lands (layout handling here is backend-generic via `GuestLayout`).
* Sandbox *escape attempts* (reading host paths, clock tampering, ptrace)
  are contained but not detected/reported as `SANDBOX_VIOLATION`; only a
  forged guest report is.
* Host-dev toolchain is identified by a digest of its description, not a
  pinned image; pinned images are supported (`toolchain_image` +
  `ARENA_IMAGES_DIR`) but none is built yet.
* No calibration binary / drift check (bench-spec §6) and no page-cache drop
  for cold runs: cold = first runs of the session.
* bwrap-dev has no seccomp filter and shares the host kernel; that is why it
  is DEMO-only.
* `prepare --out` is pre-created on bwrap-dev but not on firecracker:
  candidates should `mkdir -p` it.
