# NEAR Proof Arena — Benchmark specification (`bench-spec-v1`)

Status: normative for every challenge whose `measurement.aggregation == "median"`
(the only value in contracts v1). Owner: bench lane (`benchmarks/`).
The measurement *mechanism* (sandbox timing, supervisor, Rust score function)
lives in `runners/measure` (runners-core lane) and must implement this
document. The reference implementation of every formula below is the
stdlib-only Python package `benchmarks/arena_bench`; its cross-language test
vectors are `benchmarks/testvectors/score.json`.

Key words MUST / MUST NOT / SHOULD are used in the RFC 2119 sense.

What the arena claims about a result: **"best measured on this challenge, on
this hardware profile, for this workload-suite revision"**. Never "provably
fastest", never a statement about other hardware, other inputs, or other
scopes.

---

## 1. What is measured: useful proving

The quantity is the **end-to-end wall time for the judge to obtain, from the
candidate's `prove` entry point, a proof that the judge's `verify` run
accepts for the oracle's expected claim**, for each request of a prescribed
batch. A run that does not end in an accepted proof of the correct claim is
not a slow run; it is a failure (§9).

### 1.1 Charged to the candidate (inside the timed region)

Everything `prove` does between `execve` and process-tree exit, including but
not limited to:

| work | notes |
|---|---|
| process start, dynamic loading, reading `public_dir` | page cache is warm in steady state, cold in cold runs (§4) |
| **witness generation** | anything derived from `request.bin` + `witness.bin` |
| **state preparation beyond the supplied canonical inputs** | e.g. building tries/Merkle paths, re-hashing state, decoding/re-encoding, sorting, indexing. The judge supplies only the canonical `request.bin` / `witness.bin` defined by `claim_encoding`; any other representation the prover wants is its cost |
| **execution** | NEAR semantics execution / re-execution inside or outside the proof system |
| **trace construction** | AIR/R1CS/PLONKish trace, memory/lookup tables |
| **commitments** | polynomial / vector / Merkle commitments, FFT/NTT, MSM |
| **proof construction** | IOP rounds, openings, Fiat-Shamir |
| **recursion / compression / aggregation / wrapping** | everything needed to reach the bytes the challenge's `verify` accepts |
| **serialization** | writing `claim.bin` and `proof.bin` to the scratch dir |
| GPU work | host↔device transfers, kernels, synchronization (§3.3) |

### 1.2 Not charged to the candidate

* Judge-side work: workload sampling, oracle `expected_claim`, writing input
  files, sandbox/VM boot, scratch wipe, output digesting, verification.
* `verify` time — measured, reported per class (`verify_median_ns`) and hard
  capped by `resource_limits.max_verify_ms` (§9), but not part of the
  **speed** score. On challenges with `scoring.kind = cost_v1` it is part of
  the separate **cost** score (§14), together with proof size.
* Public preprocessing (`prepare`) — measured and reported separately (§2).
* Build time — capped by `max_build_ms`, reported, not scored.

---

## 2. Allowed public preprocessing (`prepare`)

* `prepare --params <approved_params.bin> --out <public_dir>` is **run by the
  judge, once per (challenge, candidate verified surface)**, in the same
  sandbox type and hardware profile as benchmark runs, with no network and no
  access to any workload input, witness, seed or schedule.
* It is measured (`BenchmarkResult.prepare_ns`) with the same timer as §3 and
  its output size is recorded (`public_artifact_bytes`). Hard caps:
  `resource_limits.max_prepare_ms` and `max_public_artifact_bytes`; exceeding
  either fails `RESOURCE_LIMITS` with `RESOURCE_LIMIT`.
* The output is frozen by `TreeDigest`, becomes part of `VerifiedSurface.
  public_artifacts`, and is mounted **read-only** into every `prove` and
  `verify`. It is reused across `PROVER_ONLY` children only if the digests are
  identical (contract §7).
* **Amortization policy (fixed for bench-spec-v1, hence for every v1
  challenge): `prepare` is never amortized into the score.** It is reported
  next to the score (absolute ns and bytes) on every board row. A future
  challenge that wants an amortized term (e.g. `prepare_ns / N_proofs`) needs an
  additive contract field (`measurement.prepare_amortization`, see §15) and a
  new spec version; the policy can never change inside a published challenge.
* Because `prepare` sees no workload data and runs before sampling (§11), it
  cannot precompute anything input-specific; anything it precomputes is
  legitimately public (proving keys, tables, twiddles).

---

## 3. The timed region and its boundaries

### 3.1 Clock ownership

* Times are measured **only by the judge supervisor** (`SandboxOutcome.wall_ns`),
  a process outside the candidate's PID namespace / VM, using
  `CLOCK_MONOTONIC`. Anything the candidate prints (stdout/stderr, files,
  "timings.json") is ignored for measurement and only stored as truncated
  untrusted diagnostics.
* Under `firecracker`, the in-guest judge agent (part of the judge rootfs,
  not the candidate bundle) takes the authoritative timestamps, and the host
  supervisor independently timestamps the same start/stop events over vsock.
  If guest and host durations differ by more than 1% + 5 ms the run is an
  infra error (`INFRA_ERROR`, re-run), and a repeated mismatch for one
  candidate is escalated as `SANDBOX_VIOLATION`.
* The candidate has no `CAP_SYS_TIME`, no access to the host clock, no
  network, no way to observe the schedule.

### 3.2 Start and stop

* **Start**: immediately before the supervisor `execve`s the entry point
  (inputs already written and closed; scratch empty).
* **Stop**: when the entry process has exited **and** every process in its
  sandbox (cgroup / PID namespace) is gone. The supervisor kills the PID
  namespace when the entry process exits; daemons, forked children and
  detached helpers do not survive the run.
* **Durable outputs**: after stop, the supervisor reads `claim.bin` and
  `proof.bin` as regular files from scratch. Only bytes present at stop count.
  A missing/partial file is a failed run (`PROVER_FAILED`), never a "fast" run.
  No output may be produced or completed after the process exits.

### 3.3 GPU synchronization

Because the stop event is process-tree exit, and the driver destroys the
process's device contexts at exit, there is no window in which asynchronous
GPU work can finish "after the clock". Kernels still in flight at exit are
aborted; their results cannot reach `proof.bin`. In addition, before each GPU
run the supervisor checks that no other compute contexts exist on the device
(MPS disabled, no persistent daemons in the candidate image), and after each
run that none remain.

---

## 4. Hardware, isolation, cold vs steady state

### 4.1 Governed benchmark hosts

Official numbers come only from **governed hosts** whose host profile
(`arena-host-profile-v1`, collected by `python -m arena_bench host-profile
--governed`) satisfies:

* exact `HardwareProfile` match with the challenge (`cpu_model`, `vcpus`,
  `ram_bytes`, `gpu`), fixed microcode, BIOS settings recorded;
* `scaling_governor = performance` on all benchmark cores, turbo/boost
  **disabled** (or fixed and recorded), SMT disabled or siblings of
  benchmark cores isolated and idle;
* benchmark cores listed in `isolcpus=` / `nohz_full=` with IRQs steered away
  (`irqaffinity=`), all on one NUMA node with node-local memory;
* THP `madvise` or `never`; no swap use during sessions;
* no other workloads during a session (concurrency = 1, §5).

The collector records CPU model, microcode, governor, turbo/boost (incl.
`amd-pstate` EPP), SMT, kernel, cmdline isolation, memory/hugepages, NUMA,
isolated CPUs, mitigations and GPUs without privileges, and emits
`warnings` for each policy deviation. `benchmarks/hardware/dev-host.json` is a
**development** host (shared box, SMT on, powersave, no isolation); numbers
measured there are never official and are labelled as such in reports.

Document format:

```json
{
  "schema": "arena-host-profile-v1",
  "governed": false,
  "hardware_profile": {"id": "...", "cpu_model": "...", "vcpus": 32,
                       "ram_bytes": 134653128704, "gpu": null},
  "details": {"cpu": {...}, "kernel": {...}, "memory": {...}, "numa": [...], "gpus": [...]},
  "warnings": ["SMT_ACTIVE", "..."],
  "note": "free text",
  "collected_at": "RFC 3339 UTC"
}
```

`hardware_profile` is exactly `arena_types::HardwareProfile`
(`deny_unknown_fields`); only it is compared with the challenge.

### 4.2 Cold run

A **cold** run executes the class's batch on a **freshly booted microVM**
from the frozen rootfs + bundle, after the judge drops host page caches for
the bundle/public artifacts (`echo 3 > /proc/sys/vm/drop_caches`, judge
privilege). VM boot is outside the timed region. Cold medians are reported as
`ClassMeasurement.cold_ns` and are subject to every hard cap (`max_prove_ms`
applies to every single invocation, cold or warm). Cold time is **not** in
the v1 score.

### 4.3 Steady-state run

A **steady-state** run executes the batch in the same VM after warm-up
rounds: page cache and CPU caches may be warm, but **no candidate state
persists**: scratch (the only writable filesystem, incl. `/tmp`, `/dev/shm`)
is wiped and recreated per invocation, `public_dir` is read-only, the PID
namespace is torn down after every invocation, GPU contexts are destroyed at
exit. The score uses steady-state medians.

---

### 4.4 Invocation isolation modes (bench-spec-v1.1)

`measurement.invocation_mode` (additive, contracts v1.4; absent ⇒
`vm_per_invocation`) selects how steady-state runs are isolated:

* `vm_per_invocation` (bench-spec-v1): every `prove` and `verify` gets its own
  freshly booted sandbox instance. On the Firecracker backend the timed region
  then includes process start in a guest with a **cold page cache**. The
  2026-10-03 dev-host baseline of the reference candidate
  (`benchmarks/results/baseline-near-transfer-receipt-v1-r1-devhost-20261003`)
  showed ~25 ms per request against 3–200 µs of in-process proving. The score
  therefore mostly measures sandbox start-up.
* `vm_per_batch` (bench-spec-v1.1): every warm-up, measured and fresh-confirm
  batch runs in **one** fresh sandbox instance, which removes boot and
  cold-cache overhead from the timed region:
  * Every request is still a fresh `prove` process with a wiped scratch
    (`/scratch`, `/tmp`, `/dev/shm`), sees only its own `request.bin` and
    `witness.bin` (bound read-only for that invocation only), and runs in a
    fresh cgroup and IPC namespace with non-root key creation disabled. The
    whole cgroup is killed when the invocation ends. No state is carried
    between requests, and there is still no network.
  * One **untimed warm-up invocation** on the batch's first request precedes
    the timed ones. It must also produce a valid proof.
  * `T_run` is the sum of the timed invocations' host-clock times (STEP
    console markers). Verifies are batched the same way and are still all
    checked.
  * **Cold runs (§4.2) stay one instance per invocation**, so the cold-start
    cost is still measured and reported (`cold_ns`).
  * Implementation: `Sandbox::run_steps` (runners/sandbox), Firecracker steps
    mode (runners/firecracker; requires rootfs and fc-runner images rebuilt
    from this checkout), and worker `run_prove_batch`/`run_verify_batch`.
    Isolation tests: `runners/firecracker/tests/vm.rs`
    `steps_share_one_vm_but_no_state`.

  Residual shared state within one batch VM: the guest page cache and CPU
  caches (allowed warm state, §4.3) and kernel memory side channels. None of
  these carries candidate-chosen data, because process trees, files, IPC
  objects and keys do not survive an invocation. The fresh-confirm tripwire
  (§7.4) applies unchanged.

  **Status.** `near-transfer-receipt-v1-2`
  (`chl_3be93793610370275ae40f36a475f01f`) is the first challenge with
  `vm_per_batch`. Its baseline was measured through Firecracker on a quiet
  CPU set (4 physical cores, both SMT threads) of the dev host, with the
  calibration checks passing: batch-1 6.83 ms, batch-16 7.23 ms and batch-256
  10.20 ms per 8-request batch. Cold starts are ~0.22–0.27 s.
  (`benchmarks/results/baseline-near-transfer-receipt-v1-2-vmperbatch-devhost-20261003/`).
  Earlier sessions that failed calibration were never pinned. Steps mode
  needs the rootfs and fc-runner images built from this tree
  (`/data/illia/nearproof-deps/firecracker-rc` on the dev host).

## 5. Session layout, concurrency, run order

* **Concurrency = 1**: exactly one candidate process tree is being measured
  on a host at any time; it may use all of the profile's dedicated pinned
  cores (`SandboxSpec.cpu_set`) and memory (`mem_bytes`). Judge housekeeping
  runs on non-benchmark cores.
* A **session** is one uninterrupted sequence on one host:

  ```
  calibration_pre   x calibration_runs (5)
  cold              cold_runs rounds
  warmup            warmup_runs rounds        (unscored, but must be valid)
  measured          measured_runs rounds      (scored)
  fresh_confirm     1 round on an unseen batch (caching tripwire, §7.4)
  calibration_post  x calibration_runs (5)
  ```
  Each round is one run of every class's batch. The paired baseline control
  (§6.2) is scheduled as an extra pseudo-class `__baseline__/<class>` inside
  the same rounds.
* **Run order randomization**: within each round, classes are ordered by an
  independent Fisher-Yates permutation drawn from one `SplitMix64(seed)`
  stream (`arena_bench.schedule.build_schedule`), with
  `seed = derive_seed("schedule", challenge_id, submission_id, attempt)`
  (§8.4). Seed and full schedule are recorded in the report so the order is
  reproducible and auditable; it is public after the session but unknown to
  the candidate during it (the candidate sees no seed, no schedule, no
  round counter, no class name — only its input files).

---

## 6. Calibration and drift

### 6.1 Calibration workload

A fixed judge calibration binary (digest pinned per hardware profile; CPU:
a fixed deterministic hash/NTT/MSM mix pinned to the benchmark cores; GPU
profiles add a fixed kernel suite) runs `calibration_runs` times before and
after every session. The governed host profile stores a **reference
calibration median** established at host admission.

`arena_bench.calibration.check_drift` (all integer, ppm, rounded up):

| check | threshold (v1) | on failure |
|---|---|---|
| session drift `|post-pre|/pre` | 20 000 ppm (2%) | `SESSION_DRIFT` |
| `|pre-ref|/ref`, `|post-ref|/ref` | 50 000 ppm (5%) | `REFERENCE_DRIFT_PRE/POST` |
| calibration noise `MAD/median` (pre or post) | 20 000 ppm | `CALIBRATION_NOISY` |

Any failure ⇒ the whole session is discarded as an **infra** event (never
charged to the candidate, never a `FAIL`), and re-run, bounded by the
contract's 3 infra retries (then `INFRA_ERROR`). Repeated reference drift
takes the host out of the governed pool until re-admitted.

### 6.2 Paired baseline control

In every session the challenge's baseline submission is run on the **same
sampled batches** as the candidate. If the control median deviates from the
frozen `workload_suite.baseline_ns` by more than 30 000 ppm, the session is
infra-invalid (input variance or host drift detected). The score still uses
the frozen `baseline_ns` (contract §7) so scores are comparable across
sessions; the control only gates validity and is reported.

---

## 7. Statistics

All statistics are on integer nanoseconds, computed by the judge from
`SandboxOutcome.wall_ns`.

### 7.1 Per-run value and batch semantics

A **run** of class `j` is the class's batch of `batch_size` requests, proved
by `batch_size` sequential `prove` invocations (each a fresh process, §4.3),
each followed (outside the timed region) by claim check and `verify`.
`T_run = Σ wall_ns` of the `batch_size` prove invocations. Batch members are
distinct requests from the class generator. A request may itself be a
multi-receipt transition (that is the challenge's `granularity`); the batch
is a statistical unit of several such requests, not an aggregation the prover
may exploit across requests (it cannot: each invocation sees one request, and
no state persists between invocations).

### 7.2 Aggregation

* `median_ns = median_u64(runs_ns)` over the `measured_runs` steady-state runs;
  for even counts the floor of the midpoint (`lo + (hi-lo)//2`).
  `measured_runs` SHOULD be odd.
* `mad_ns = median_u64(|x - median_ns|)` (unscaled).
* Warm-up and fresh-confirm runs are never in the median; cold runs give
  `cold_ns = median(cold runs)`.

### 7.3 Outliers: flag, never silently drop

Run `i` is flagged iff `|x_i - median| > k * MAD` with
`k = measurement.outlier_mad_k` (integer, strict). Flagged runs **stay in**
the median, MAD and bootstrap, and are listed in the report. If more than
200 000 ppm (20%) of a class's runs are flagged, the class's runs are
re-measured in a new session (infra; noisy host) — not discarded piecemeal.
`MAD == 0` is reported (`MAD_ZERO`), not special-cased.

### 7.4 Fresh-input caching tripwire

The `fresh_confirm` round uses a batch from the same generator that the
candidate has not seen in the session. If its median exceeds the steady-state
median by more than **both** `k * MAD` and 50 000 ppm, the result is flagged
`CACHING_SUSPECTED`: the submission is not ranked until a re-run with fresh
batches only (every round a new batch) confirms the number; the confirming
re-run's number is the one published.

---

## 8. Score

### 8.1 Formula

```
score = 100 * exp( Σ_j w_j * ln(T_base_j / T_cand_j) ),   w_j = weight_ppm_j / 1e6
```

the weighted geometric mean of per-class speedups vs the baseline, so the
baseline scores exactly 100, uniformly 2× faster scores 200, and classes
trade off multiplicatively. `T_cand_j` = steady-state `median_ns`;
`T_base_j` = frozen `workload_suite.baseline_ns` for class `j`.
Weights are integer ppm summing to exactly 1 000 000 (`WEIGHT_SUM` otherwise);
a weight-0 class is measured, gated and reported but does not move the score.

### 8.2 Exact evaluation (normative, cross-language)

```
validate: non-empty; class ids unique; weight_ppm u32; baseline_ns, median_ns u64 > 0;
          Σ weight_ppm == 1_000_000
order:    classes sorted by class_id, ascending by UTF-8 bytes
acc = 0.0                                    (IEEE-754 binary64)
for c in order:
    r   = f64(c.baseline_ns) / f64(c.median_ns)      (u64→f64 round-to-nearest-even)
    acc = acc + f64(c.weight_ppm) * ln(r)
s = 100.0 * exp(acc / 1_000_000.0)
score_milli = floor(s * 1000.0 + 0.5)        (as u64)
error SCORE_OVERFLOW if s*1000+0.5 is not finite or ≥ 2^63
```

Error codes: `EMPTY_SUITE`, `BAD_CLASS_ID`, `DUPLICATE_CLASS`, `BAD_WEIGHT`,
`ZERO_OR_BAD_TIME`, `WEIGHT_SUM`, `SCORE_OVERFLOW`, `NO_RUNS`.
`BenchmarkResult.score_milli` is `score_milli`; JSON objects carry no floats.
Implementations MUST use the platform `ln`/`exp` of binary64 (glibc on judge
hosts, for both Rust `f64::ln/exp` and Python `math.log/exp`). Test vectors
are chosen ≥ ~4500 ulp away from any rounding boundary so a few-ulp libm
difference cannot change an integer output.

### 8.3 Bootstrap 95% CI (seeded)

Percentile bootstrap over measured runs, resampling each class's runs
independently with replacement:

```
rng = SplitMix64(seed)
for b in 0..B:                               B = 10_000 in v1
  for c in classes sorted by class_id bytes:
    n = len(c.runs_ns)
    resample = [c.runs_ns[rng.next_u64() % n] for _ in 0..n]
    med_c = median_u64(resample)
  x_b = score(classes with median_ns = med_c).score_milli
sort x ascending
lo = x[((B-1)*25) // 1000];   hi = x[((B-1)*975 + 999) // 1000]
score_ci_milli = (hi - lo + 1) // 2           (half-width, rounded up)
```

The point estimate is the score of the actual medians, not the bootstrap
mean. `seed = derive_seed("bootstrap", submission_id, result_digest)`.
The CI reflects run-to-run noise on this host for these inputs only; it does
not cover input variance or cross-host variance (§13 re-runs do).

`SplitMix64`: `state += 0x9E3779B97F4A7C15; z = state; z = (z ^ z>>30) *
0xBF58476D1CE4E5B9; z = (z ^ z>>27) * 0x94D049BB133111EB; return z ^ z>>31`
(mod 2^64). Indices use `next_u64() % n` (bias < n/2^64, accepted for
portability). Fisher-Yates: `for i in n-1 down to 1: j = next_u64() % (i+1);
swap(i, j)`.

### 8.4 Public seeds

`derive_seed(purpose, parts…)` = first 8 bytes, big-endian, of
`sha256("near-arena-seed-v1|" + purpose + "|" + part1 + "|" + … )`
(parts: printable ASCII, no `|`, no space). Used for schedule and bootstrap;
these seeds are recomputable by anyone and need not be secret because they
only randomize order/resampling, not inputs.

### 8.5 Test vectors

`benchmarks/testvectors/score.json` (`arena-bench-testvectors-v1`) contains
SplitMix64 streams, median/MAD, `derive_seed`, score (incl. every error code),
bootstrap, schedule, outlier and drift-ppm vectors. All u64 values are JSON
integers; f64 values are strings (shortest round-trip) and are informative
(rel. tolerance 1e-12); **every integer output MUST match exactly**.
Regenerate with `python -m arena_bench gen-testvectors` (run from
`benchmarks/`); `--check` verifies freshness. **Not yet wired into CI**: no
workflow job or Makefile target runs `gen-testvectors --check` or
`pytest benchmarks/tests` (both pass locally). `runners/measure` passes the same
file (`runners/measure/tests/testvectors.rs`, run by `make test-rust`).

---

## 9. Hard gates (not score components)

A submission gets a score only if **all** of these hold; any violation fails
the named gate and the decision follows `decide()` (contract §7):

| condition | gate | reason code |
|---|---|---|
| every required case (conformance suite, held-out correctness set, every benchmark batch member incl. warm-up, cold, fresh-confirm and baseline-paired runs) yields `claim.bin == expected_claim(request)` | `CONFORMANCE_DIFFERENTIAL` | `CLAIM_MISMATCH` |
| … and a proof the judge's `verify` accepts | `PROVER_RELIABILITY` | `PROVER_FAILED` |
| any prove invocation exceeds `max_prove_ms` or `per_run_timeout_ms` | `PROVER_RELIABILITY` | `TIMEOUT` |
| `proof.bin` > `max_proof_bytes` (any proof) | `RESOURCE_LIMITS` | `RESOURCE_LIMIT` |
| any `verify` > `max_verify_ms` | `RESOURCE_LIMITS` | `RESOURCE_LIMIT` |
| peak RSS > `max_ram_bytes`, VRAM > `max_vram_bytes` (OOM-kill counts) | `RESOURCE_LIMITS` | `RESOURCE_LIMIT` |
| `prepare` > `max_prepare_ms`, public dir > `max_public_artifact_bytes` | `RESOURCE_LIMITS` | `RESOURCE_LIMIT` |
| score function error (e.g. `NO_RUNS`) | `BENCHMARK` | `INFRA_ERROR` if judge-side, else `PROVER_FAILED` |

Every proof produced during benchmarking is verified — not a sample. There is
no partial credit: one failed case means no score.

---

## 10. Repetitions (v1 defaults)

Challenge fields (`MeasurementProcedure`) and spec constants:

| parameter | source | v1 default |
|---|---|---|
| `warmup_runs` | challenge | 2 |
| `measured_runs` | challenge | 9 (odd) |
| `cold_runs` | challenge | 3 |
| `outlier_mad_k` | challenge | 5 |
| `concurrency` | challenge | MUST be 1 |
| `aggregation` | challenge | MUST be `median` |
| `per_run_timeout_ms` | challenge | ≤ `max_prove_ms` |
| calibration runs | spec | 5 pre + 5 post |
| session / reference / noise drift | spec | 20 000 / 50 000 / 20 000 ppm |
| excessive-outlier share | spec | 200 000 ppm |
| fresh-confirm rounds; tripwire floor | spec | 1; 50 000 ppm |
| baseline control tolerance | spec | 30 000 ppm |
| bootstrap iterations | spec | 10 000 |

---

## 11. Workloads: sampling after freeze, held-out sets, leakage, seasons

### 11.1 Sampling after artifact freeze

Benchmark inputs are sampled **after** the package digest is fixed (upload
accepted) and the build is frozen; nothing the candidate controls can depend
on them. Per class:

```
sampling_seed_j = first 8 bytes BE of HMAC-SHA256(key = season_secret,
    "near-arena-workload-sample-v1|" + challenge_id + "|" + package_digest + "|" + class_id)
```

which drives the class generator (`WorkloadClass.generator` digest) to
produce the batch(es). Re-runs that need different batches (fresh-confirm,
leader re-run) append a tag to `class_id` (`<class>#fresh`, `<class>#rerun2`).
Same package digest ⇒ same inputs (dedup: re-submitting an identical package
returns the cached result, it does not re-roll noise).

**Worker implementation** (`runners/worker/src/oracle.rs`, `SeedCtx`): the
season secret is read from the judge-only file `ARENA_SEASON_SECRET_FILE` (hex,
≥ 32 bytes, must not be group/other accessible); it is never passed to a
sandbox or placed in paths, arguments or messages (only the derived per-class
seed reaches the judge's own `near-arena-oracle gen --seed`), and `Debug`
prints only its commitment. The class component is
`class_id`, replaced by a re-run tag that already starts with `<class_id>#`
(`batch-1#fresh`, `batch-1#confirm-<phase>-<round>`) and extended by `#heldout`
for the held-out subset selection; the result is bit-identical to
`arena_bench.seeds.derive_sampling_seed` (test `judge_secret_sampling_seeds`).
Conformance, adversarial controls and benchmark batches all draw from it. If a
worker has no secret configured it falls back to the public
`derive_seed("workload", class_id, challenge_id, package_digest, tags…)` and
says so in the `CONFORMANCE_DIFFERENTIAL` and `BENCHMARK` summaries ("PUBLIC
sampling seeds"); such runs are reproducible by anyone, including the
submitter, and must not be presented as secret-sampled.

### 11.2 Commit-reveal of the season secret

* Before a season opens governance publishes
  `commit = sha256("near-arena-secret-commit-v1\0" || season_secret)`
  (secret ≥ 32 random bytes) in the season manifest.
* The secret lives only in the judge's sampling service (the worker reads
  it from `ARENA_SEASON_SECRET_FILE`; with `ARENA_SEASON_SECRET_COMMIT` set to
  the published commitment, a worker whose secret does not match refuses to
  start). Every gate summary that used it names the commitment, so the
  reveal can be matched to the runs.
* At season end the secret is revealed; anyone can verify the commitment
  (`arena_bench.seeds.verify_reveal`), recompute every submission's sampling
  seeds and regenerate its inputs, proving the judge did not cherry-pick
  inputs per candidate.

### 11.3 Held-out sets

`workload_suite.heldout_commitment` commits to a held-out correctness/timing
set (tree digest) revealed at season end. During the season held-out cases
are used for correctness gating only, with **bucketed feedback** (§11.4). At
season end, the top entries are re-measured on held-out timing batches and the
season standings report both numbers.

**Worker implementation:** held-out sets live in judge-only directories
(`ARENA_HELDOUT_DIRS`, never mounted into a sandbox) laid out per class
(`<class>/…` in the claim encoding's fixture layout) and are matched to
`heldout_commitment` by TreeDigest, re-hashed on every use. Once a worker has
any held-out dir configured, a committed set that is missing or whose digest
differs is an infrastructure error (fail closed). CONFORMANCE uses a
seed-selected subset of each class (as many as the sampled cases per class);
held-out cases are non-public: their ids, proof sizes, timings and failure
details never reach summaries or public evidence (RT-04), and the summary
reports only the count and the commitment. A worker without held-out dirs
reports "held-out set … NOT exercised" in the CONFORMANCE summary instead of
silently skipping it.

**Coverage floor (fail closed):** a challenge that pins `public_fixtures` must
be run against exactly that set (a worker without it fails the job as
infrastructure, naming the pin), the set must contain an in-domain case, and
every workload class must contribute at least `max(1, ceil(samples /
classes))` judge-sampled cases; benchmark batches must have their full size.
Empirical coverage is evidence, not a soundness argument: it never substitutes
for the formal gates.

### 11.4 Adaptive-leakage limits

* Feedback granularity: score in milli units, per-class medians, CI,
  pass/fail per gate. Held-out feedback is only `PASS` or
  `FAIL (n of m failed, n bucketed to {1, 2–5, >5})` — never which case.
* Benchmark sampled inputs of a submission are not returned to the submitter
  during the season (they are re-derivable after the reveal).
* Rate limit: benchmarked submissions per agent per challenge per UTC day are
  capped (v1: 20); cancelled/failed submissions count.
* Near-duplicate re-rolls (packages differing only in irrelevant bytes) gain
  nothing: leaders are re-run (§13) and the conservative number is ranked.

### 11.5 Season rotation

Each season rotates generator parameters, held-out set and secret; the board
is per challenge and seasons are not mixed. Baselines are re-measured per
suite revision.

---

## 12. Anti-gaming: attack → gate

| attack | description | caught by |
|---|---|---|
| **Verifier transfer** | move work from `prove` into `verify` (e.g. "proof" that `verify` re-executes) | `max_verify_ms` hard cap (`RESOURCE_LIMITS`); verify median reported per class; verifier artifact is part of `VerifiedSurface` so any change reopens formal gates (`VERIFIER_OR_PROTOCOL`) |
| **Witness-as-proof** | ship the witness (or most of it) as the proof | `max_proof_bytes` + `max_verify_ms` caps; `FORMAL_ZK` for zero-knowledge profiles; `FORMAL_CRYPTO_SOUNDNESS` bound must still hold |
| **Easy-case proving** | fast on easy inputs, fail/slow on hard ones | every required case must produce a valid proof (§9, `PROVER_RELIABILITY`, no partial credit); inputs sampled after freeze from generators covering the scope (§11.1); per-class weights; held-out set (§11.3); `max_prove_ms` on every invocation |
| **Setup-cost omission** | hide expensive work in setup, build or "one-time" init | `prepare` judge-run, input-blind, measured, capped and reported (§2); build capped (`max_build_ms`) and reproducible (`BUILD_REPRODUCIBLE`); bundle/package size limits; per-invocation init is inside the timed region; cold runs reported |
| **Caching across runs** | persist results/precomputation between invocations | fresh scratch per invocation, read-only `public_dir`, PID-ns teardown, GPU context teardown (§4.3); fresh-confirm tripwire `CACHING_SUSPECTED` (§7.4); paired baseline control (§6.2); inputs unknown before freeze (§11.1) |
| **Unsynchronized GPU work** | return before GPU work finishes, finish "after the clock" | stop = process-tree exit, outputs must be durable at stop (§3.2–3.3); context teardown; device idle check before/after; every proof verified |
| **Timing forgery** | report own timings, tamper with clocks | judge-only clocks outside the candidate's namespace/VM; candidate output ignored; guest/host timestamp cross-check (§3.1, `SANDBOX_VIOLATION`); no `CAP_SYS_TIME` |
| **Benchmark-only shortcuts** | detect the benchmark (env, names, timing, order) and behave differently, e.g. skip work and emit invalid/unrelated proofs | identical sandbox spec, env allowlist and file layout for conformance and benchmark runs; no class names/seeds/round counters visible; randomized order; claim check + verify on **every** proof (`CLAIM_MISMATCH`, `PROVER_FAILED`); valid-but-overfit specialization is bounded by held-out timing and season rotation |
| **Noise fishing** | resubmit until a lucky run | identical digests dedup; rate limits; CI shown; leader re-run on a second host with the conservative number ranked (§13) |
| **Verify / proof-size games on cost_v1** | tiny proofs with huge verify, parallel verify, verify tuned to the judge's box | §14.9 |
| **Host interference** | exploit a noisy or mis-configured host | governed host profile, calibration before/after, drift ⇒ infra rerun (§6), outlier share ⇒ re-run |

---

## 13. Reporting, ranking, independent re-runs

* Every row shows **absolute numbers** (per-class median, MAD, cold, verify
  median, max proof bytes, peak RSS, prepare ns, public artifact bytes) **and**
  the speedup vs baseline and the score with its CI. Reports are rendered by
  `arena_bench.report.render` (all candidate-originating strings escaped).
* Ranking is by `score_milli` within one (challenge, hardware profile,
  suite revision). Entries whose 95% CIs overlap are displayed as a tie band;
  the order inside a band is by score but labelled "within noise".
* **Independent re-run of leaders**: any submission that would enter the
  top 3 is re-measured, before its rank is published, on a **second governed
  host** of the same hardware profile, with re-run batches (§11.1). If the two
  scores differ by more than `max(ci₁ + ci₂, 30 000 ppm of the lower)`, the
  entry is marked `UNCONFIRMED` and both are shown. The **lower** of the two
  scores is the ranked score; both are published.
* Experimental/demo tiers and non-governed hosts are labelled as such and
  never ranked on the official board.
* Wording: "best measured on this challenge" — never "provably fastest".

---

## 14. Cost-normalized board (`cost_v1`, bench-spec-v1.3)

### 14.1 Status and scope

Proof size and verification cost are first-class only through this section.
A challenge opts in with the additive `ChallengeDefinition.scoring` section
(contracts v1.5, §14.6). Without it a challenge is scored by speed alone
(§8), exactly as before; its id does not change, because an absent section is
not serialized. A `cost_v1` challenge has **two boards**:

* the **speed board** (§8, unchanged; `score_milli`);
* the **cost board**: the same rankable runs, ranked by `cost.score_milli`.

The two kinds of score are never compared, merged or averaged. A cost result
counts on a board only if it was computed under that challenge's own price
model (digest match). The server drops any cost result a worker sends for a
speed-only challenge.

Versions: bench-spec-v1.2 introduced `cost_v1` with a draft price model.
**bench-spec-v1.3** (2026-10-06) adds the verify drift control (§14.4), the
pinning rule for `cost_baseline` (§14.5), the governed price model
`pm-near-mainnet-2026q4@v2` (§14.7) and the documented multi-shard extension
(§14.11, future, not scored). The cost formula (§14.3) and its test vectors are
unchanged.
**bench-spec-v1.4** (2026-10-06) adds the verify statistic
`scoring.verify_statistic` (contracts v1.6, additive): `lower_quartile` aggregates
the per-run verify totals by their lower quartile instead of their median
(§14.3, rationale in §14.4.1). Absent means `median`, so every v1.2/v1.3 result
and vector is unchanged.

### 14.2 Model: per-chunk system cost

NEAR stateless validation proves each chunk once and verifies it many
times. The chunk producer applies the chunk and distributes the state witness
(in the arena: the proof). Every chunk validator assigned to that shard at
that height then receives the witness, validates it and endorses it. The
statement is **per shard**: one proof covers one shard's chunk, and only that
shard's committee verifies it. Cost per proved request (one `prove`
invocation is one chunk-like unit):

```
C = c_cpu·v_p·T_prove                       prover (chunk producer), once
  + c_cpu·v_p·T_prepare·/A                  amortized public preprocessing (A = 0: not charged)
  + N_v · ( c_cpu·v_v·T_verify               each of N_v validators verifies
          + (c_bw + c_store)·proof_bytes )   and receives/forwards (and keeps) the proof
```

| symbol | meaning | source |
|---|---|---|
| `T_prove`, `T_verify` | judge wall times (supervisor clock, §3) | measured |
| `proof_bytes` | size of `proof.bin` | measured |
| `v_p` | prover vCPUs = `hardware_profile.vcpus` | challenge |
| `v_v` | reference validator vCPUs; `verify` is **pinned** to this many of the benchmark CPUs | price model |
| `N_v` | validators that verify each chunk: the chunk-validator committee of **one shard** (stateless-validation fan-out); 50 in the governed model | price model |
| `c_cpu` | price of one vCPU-second | price model |
| `c_bw`, `c_store` | per-validator network and retention cost per proof byte | price model |

Design choices, and why:

* **Allocated vCPUs × wall time, not CPU time.** The only trusted clock is
  the supervisor wall clock (§3.1); guest CPU accounting is not. Charging what
  a run reserves also neutralizes parallelism games. A verifier that spreads
  over 8 cores pays for 8 cores; a single-threaded one on 8 reserved cores
  pays for the idle 7, which is also true of a real validator node sized for
  the job.
* **`verify` on a reference validator profile.** The validator's hardware,
  not the prover's, bounds verification. The worker pins every `verify` (warm,
  batched, measured) to the first `verifier_vcpus` benchmark CPUs and fails
  the job closed if it cannot. A weaker validator profile is therefore
  measured, not extrapolated.
* **Bytes are charged per validator.** In nearcore's partial-witness
  distribution every validator forwards a Reed-Solomon part to every other
  validator (§14.7), so bandwidth scales with `N_v`. The chunk producer's own
  upload (≈ 1.7 × size, once) is about 2% of the `N_v` term and is not modelled.
* **Latency is not a cost term.** It stays governed by `max_prove_ms`,
  `max_verify_ms` and the speed board. A cost-optimal but slow prover is
  visible as such on the speed board.

`score = 100·exp(Σ_j w_j·ln(C_base,j / C_cand,j))`, with the challenge's class
weights. `C_base,j` is the cost of the challenge's reference candidate,
measured under the same procedure. 100 means "as cheap as the reference", and
200 means "half the system cost".

### 14.3 Exact evaluation (normative, cross-language)

One run of class `j` is one batch of `batch_size` requests (§7.1). Per run
the judge records `T_run` (Σ prove wall), `V_run` (Σ verify wall of the same
proofs) and `S_run` (Σ proof bytes of the same proofs). Untimed warm-up proofs
count toward `max_proof_bytes` only.

```
P = median_u64(prove runs)  S = median_u64(byte runs)
V = median_u64(verify runs)              scoring.verify_statistic absent or "median" (v1.2/v1.3)
V = lower_quartile_u64(verify runs)      scoring.verify_statistic = "lower_quartile" (v1.4)
    lower_quartile_u64(xs) = sorted(xs)[⌊(n−1)/4⌋]   (order statistic, no interpolation)
all integers; u128 intermediates, every product checked (COST_OVERFLOW)
prove_fusd     = ceil(P · v_p · c_cpu / 1e9)
prepare_fusd   = A == 0 ? 0 : ceil(prepare_ns · v_p · c_cpu · batch_size / (1e9 · A))
verify_fusd    = N_v · ceil(V · v_v · c_cpu / 1e9)
bandwidth_fusd = N_v · S · c_bw
storage_fusd   = N_v · S · c_store
total_fusd     = Σ of the five, as u64 (COST_OVERFLOW otherwise)
cost score     = §8.2 score with baseline_ns := baseline total_fusd, median_ns := candidate total_fusd
```

Prices are integer **femto-USD** (1e-15 USD). The baseline total uses the same
formula on `scoring.cost_baseline` (and `cost_baseline_prepare_ns`). Component
medians, rather than the median of per-run totals, make the reference score
exactly 100 against itself and make the displayed components sum to the
ranked total. Error codes: `BAD_PRICES`, `ZERO_OR_BAD_TIME` (`P` or `V` = 0),
`ZERO_COST`, `COST_OVERFLOW`, `RUN_LENGTH_MISMATCH`, plus every §8.2 code.

**Bootstrap (95% CI).** The procedure is as in §8.3, with the same seed and
`B`. One `next_u64() % n` draw per element resamples the run **triple**
`(T, V, S)` jointly, which keeps the correlation between prove and verify noise
inside a run. Each iteration recomputes the three statistics (V with the
challenge's verify statistic) and the cost.

Reference: `benchmarks/arena_bench/cost.py`. Rust: `runners/measure/src/cost.rs`.
Vectors: `benchmarks/testvectors/cost.json` (`arena-bench-cost-testvectors-v1`;
every output is an integer and must match exactly). Generate them with
`gen-testvectors`, which writes `score.json` and `cost.json`. The Rust check is
`runners/measure/tests/cost_testvectors.rs`.

### 14.4 Measurement (judge)

The benchmark stage already verifies every proof under the same controls as
`prove`. In `vm_per_batch`, verifies are batched into one fresh sandbox per
batch, on the benchmark CPUs, and only measured-phase verifies are reported.
`cost_v1` adds:

* `BatchSample.proof_bytes_total` (timed proofs only);
* `ClassSession.measured_verify_runs_ns` / `measured_proof_bytes_runs`, i.e.
  per-run totals in the same order as `measured_runs_ns`;
* `ClassMeasurement.verify_runs_ns` / `proof_bytes_runs` (additive; empty in
  older results);
* `verify` pinned to `verifier_vcpus` CPUs (`verify_cpu_set`, worker
  `stages/benchmark.rs`).

The worker computes `BenchmarkResult.cost` (point score and CI). The server
recomputes the point score from the per-run vectors and the challenge, keeps
the worker's CI half-width, and drops the result if the vectors are missing or
inconsistent.

**Verify drift control (bench-spec-v1.3, normative).** Under `cost_v1` the
validator term `N_v·c_cpu·v_v·V` dominates the cost of every re-execution
reference (§14.8), so a drifted reference verify median would move every
cost score of the challenge. The control extends §6.2 from prove time to
verify time, with the same tolerance:

```
verify_control(pinned V_j, control runs of class j, statistic):
  V_ctl,j  = statistic(per-run Σ verify ns of the control session, class j)   (the challenge's §14.3 V)
  drift_j  = ceil(|V_ctl,j − V_j| · 1e6 / V_j)                 (ppm, §6.1 drift_ppm)
  ok       = ∀j: drift_j ≤ 30 000                                (VERIFY_CONTROL_TOLERANCE_PPM)
  else  VERIFY_DRIFT  → the control session is infra-invalid
```

The classes of the pinned and the control set must be identical
(`MISSING_BASELINE`), a control class needs ≥ 1 run (`NO_RUNS`) and a pinned
median must be > 0 (`ZERO_OR_BAD_TIME`). Reference:
`arena_bench.cost.verify_control`; Rust: `arena_measure::cost::verify_control`;
vectors: `cost.json` → `verify_control`. Where it applies:

1. **Pinning a cost baseline (§14.5).** The reference is measured on the
   challenge's benchmark CPUs with `run_baseline.py --control-sessions N`
   (N ≥ 1): N more sessions of the same bundle, the same sampled batches and the
   same CPUs right after the first. Each control is checked against the first
   session. A control session that is itself infra-invalid does not count
   either way: its own §6.1 calibration failed, it is flagged, or (v1.4) its
   calibration median (pre ∪ post) differs from the pinned session's by more
   than 20 000 ppm. In the last case the host changed state between the
   sessions, and the control would measure the host, not the reference. On
   2026-10-06 this happened on the shared host: one d0-2 control was 8% faster
   in calibration and 5% faster in every verify class. `pin_baseline.py
   --price-model` refuses to write `scoring` unless the pinned session is valid,
   at least one control is valid, and every valid control passes. A failed
   control is an infra event: re-measure (bounded by the 3 infra retries), and
   never widen the tolerance in place.
2. **Season re-check and re-scoring.** A re-measurement of a pinned reference
   is compared with the pinned `verify_ns`. A failure means the host or the
   reference changed. The board is then labelled and the baseline is re-pinned
   as a new challenge version (§14.5); a published board is never re-priced in
   place.
3. **In-session paired control (§6.2).** When the worker runs the challenge's
   baseline submission on the same batches as the candidate, it applies this
   check to the control's verify medians next to the prove check. The live
   worker does not run the paired baseline yet, neither for prove nor for
   verify. Until it does, 1 and 2 are the enforced controls, and the candidate's
   own verify noise is in its bootstrap CI (§14.3).

#### 14.4.1 Verify statistic (bench-spec-v1.4): why the lower quartile

The v1-6 reference failed the median-based control on batch-16 in both
attempts of 2026-10-06 (§14.8): 41 000–161 000 ppm between sessions on
identical batches. Within a run the per-request timings show why. The slow
runs are slow almost entirely in the **first** `verify` of the batch VM (20 ms
in the fast mode, 40–64 ms in the slow mode), with an occasional spike in a
later request. That is a sandbox artifact (a cold guest-side load of the
verifier in a fresh `vm_per_batch` VM, §4.4), not a property of the proof.
Its share of slow runs changes from session to session (6 to 13 of 15), and
the median of the per-run totals jumps with it. Timing noise is also
one-sided: contention and cold caches only add time.

Candidates on the same sessions (6 v1-6 sessions and 3 v3 D0 sessions; the
spread is the drift of each control against its pinned session, valid sessions
only):

| statistic of the per-run totals | worst drift, v1-6 | worst drift, v3 D0 | passes 3% in every valid control |
|---|---|---|---|
| median (v1.3) | 160 774 ppm | 19 673 ppm | no |
| **lower quartile** | 22 374 ppm | 8 464 ppm | **yes** |
| 20th percentile | 26 560 ppm | 9 758 ppm | yes (less margin) |
| minimum | 59 735 ppm (batch-1) | 9 061 ppm | no |
| Σ over requests of the per-request lower quartile | 52 871 ppm | 11 019 ppm | no |

The lower quartile is chosen because:

* it is the most stable estimator that passes every valid control with margin;
* it still describes the population. With 15 runs it is the 4th smallest and
  with 25 runs the 7th, so one lucky run cannot set it, unlike the minimum.
  The minimum is dominated by sampling noise on short classes (batch-1, 5 ms
  per proof);
* it measures the warm, uncontended cost of verification, which is what a
  long-running validator pays per chunk. A validator does not start a fresh
  VM per chunk;
* it is applied identically to the reference, the control and every
  candidate. A candidate's verify is charged by the same rule that pins the
  baseline, so the rule favours no one. A candidate cannot move its lower
  quartile without being fast in at least 75% of its runs;
* the tolerance stays at 30 000 ppm.

More repetitions: successor challenges measure **25** runs per class instead
of 15 (`measurement.measured_runs`), which tightens every statistic of the
session, the speed median included. Pooling sessions was rejected: a
candidate has one session, and the statistic must be the same for the
reference and the candidates. Prove (`P`) and bytes (`S`) keep the median: prove
is the speed board's quantity, and bytes are deterministic per batch.

### 14.5 Price model (`arena-price-model-v1`) and governance

```json
{
 "schema": "arena-price-model-v1", "id": "pm-…", "version": 1,
 "status": "draft" | "governed", "effective_from": "YYYY-MM-DD",
 "currency": "USD", "unit": "femto_usd",
 "validators_per_chunk": N_v, "verifier_vcpus": v_v,
 "cpu_fusd_per_vcpu_second": c_cpu, "bandwidth_fusd_per_byte": c_bw,
 "storage_fusd_per_byte": c_store, "prepare_amortization_requests": A,
 "rationale": [{"param", "basis": "protocol|published|estimate", "note", "sources": [...]}]
}
```

* Integers only, JCS-hashed, `deny_unknown_fields`. The rationale is inside
  the hashed object, so justifications cannot change silently. Files live in
  `challenges/price-models/`. Drafts are `*.draft.json` and are never signed.
* A challenge embeds the model inline **and** its digest
  (`scoring.price_model_digest`, checked). Changing any price is a new
  model version and therefore a new challenge. A published board is never
  re-priced. The price-model digest is shown on every cost-board row.
* **Versioning.** `id` names the series (e.g. the season) and `version` is
  bumped on any change to any field, rationale included. A governed file is
  `challenges/price-models/<id>.v<version>.json`, and its JCS digest is pinned
  by a test (`arena-types` `scoring::tests`). It is never edited: a change is
  a new file with `version + 1`. A model is content-addressed by its digest
  and is signed only through the challenge that embeds it (`arena-admin
  sign`/`supersede`).
* **Pinning `cost_baseline`.** `prove_ns` comes from the same session as
  `workload_suite.baseline_ns`. `verify_ns` and `proof_bytes` are that session's
  medians of the per-run totals (§14.3), measured on the benchmark CPUs
  (`verify` pinned to `verifier_vcpus`) and confirmed by the verify drift
  control (§14.4). Tooling: `run_baseline.py --control-sessions N`, then
  `pin_baseline.py --price-model <governed model>`.
* `formal` challenges MUST pin a `governed` model. The check is enforced by
  `ChallengeDefinition::check_scoring` in `arena-admin verify` and in
  server-side registration.
* **Parameters are re-checked each season.** `N_v` tracks mainnet stake
  distribution and shard count. Prices track public price lists.

This supersedes the sketch that §14 used to contain (a per-profile hourly
price on prove time only). That sketch was never published.

### 14.6 Contract (`ChallengeDefinition.scoring`, contracts v1.5)

```json
"scoring": {
  "kind": "speed" | "cost_v1",
  "price_model": { …arena-price-model-v1… },
  "price_model_digest": "sha256:…",
  "cost_baseline": [{"class_id", "prove_ns", "verify_ns", "proof_bytes"}],
  "cost_baseline_prepare_ns": 123
}
```

Validation rules:

* `cost_baseline` lists every class exactly once.
* Each class's `prove_ns` equals `workload_suite.baseline_ns`: one reference
  session supplies both baselines.
* `verifier_vcpus` must not exceed `hardware_profile.vcpus`.
* `kind = speed` takes no price fields.

Results and API:

* Results: `BenchmarkResult.cost: CostResult` holds the kind, the price-model
  id and digest, `N_v`, `v_v`, the score, the CI and per-class `CostClass`
  rows (component medians and each `*_fusd` term).
* `LeaderboardEntry` gains `board`, `cost_score_milli`,
  `cost_score_ci_milli` and `cost`.
* `GET /v1/leaderboards/{id}?board=cost_v1` returns the cost board. It
  answers 404 for a challenge that has none. The web UI shows the cost board
  under the speed board, with a per-class breakdown table: prove, N_v ×
  verify, N_v × bytes, total, ratio to the reference, verify time and proof
  size per batch.

### 14.7 Price model `pm-near-mainnet-2026q4`

#### v2 — GOVERNED (2026-10-06)

`challenges/price-models/pm-near-mainnet-2026q4.v2.json`, digest
`sha256:292f094206162f78ee3ad982a8082c11b49fc379ad04956275693d9ef4d5ca6a`
(pinned by `arena-types` `scoring::tests::governed_price_model_v2_is_pinned`).
It is the v1 draft below with these changes: `N_v` = 50 per shard, status
`governed`, `effective_from` 2026-10-06, and the rationale updated. Every price
is kept.

| param | value | basis | justification |
|---|---|---|---|
| `validators_per_chunk` | **50** | governance decision | **Per shard.** The per-chunk statement is one shard's chunk at one height, and that shard's committee verifies it, so `N_v` counts one shard's validators. 50 is the governed committee size. The v1 observation (84.0–84.1 distinct endorsers per shard, 105 mandate seats) is kept as a sensitivity column. Only the validator terms scale with `N_v`, both linearly. |
| `verifier_vcpus` | **8** | published | NEAR chunk-validator spec ("≥ 8 physical cores"). Measured pinned to live CPUs 0–7 (CCD0, SMT siblings idle). |
| `cpu_fusd_per_vcpu_second` | **7.61e9** (USD 7.61e-6) | ESTIMATE | Unchanged: USD 160/month for 8 vCPU (m5a.2xlarge CPU part) ÷ (730 h × 8 × 3600 s). |
| `bandwidth_fusd_per_byte` | **82 000** (USD 8.2e-11) | ESTIMATE | Unchanged: egress USD 0.05/GB × upload amplification. The amplification is `(N−2)/⌊0.6 N⌋`: 1.64 at N = 84 and 1.60 at N = 50 (48/30). The v1 constant is kept by decision. The N = 50 derivation gives 8.0e-11 (−2.4%), well inside the egress-price uncertainty. |
| `storage_fusd_per_byte` | **0** | estimate | Unchanged. |
| `prepare_amortization_requests` | **0** | estimate | Unchanged. |

The measurement does not change the constants. In the re-measured references
(§14.8), verify is 63–77% of the reference cost on v1-6 and 93–96% on v3 D0;
bandwidth is the rest, and prove is < 0.2%. No measured quantity is an input
to a price, so the measurement cannot contradict `c_cpu` or `c_bw`. What it
does show is that the verify median itself is the quantity to control (§14.4).

#### v1 — DRAFT (2026-10-05, superseded by v2, never signed)

`challenges/price-models/pm-near-mainnet-2026q4.draft.json`, digest
`sha256:38c281cfe256d2cfcdef920eb267254df16fbe947a76e03637ad704016b84dac`.

| param | value | basis | justification |
|---|---|---|---|
| `validators_per_chunk` | **84** | protocol, observed | Mainnet RPC `validators` (epoch 4835, 2026-10-05): 415 validators and 10 shards. Expected endorsements ÷ expected chunks = 84.0–84.1 on every shard. The nearcore 2.13.4 mandate model (`target_validator_mandates_per_shard = 105`, `epoch_configs/mainnet/85.json:7`; round-robin mandate dealing, `validator_mandates/mod.rs:134-200`) on the same stakes predicts 84.1. Several mandates held by one account verify once, so N_v < 105. |
| `verifier_vcpus` | **8** | published | NEAR chunk-validator spec: "x86_64 with at least 8 physical cores". The v1-6 benchmark CPUs 0–7 are 8 physical cores with SMT siblings idle, so existing measurements are already on this profile. |
| `cpu_fusd_per_vcpu_second` | **7.61e9** (USD 7.61e-6) | ESTIMATE | USD 160/month CPU for 8 vCPU (AWS m5a.2xlarge, NEAR's own chunk-validator cost estimate) ÷ (730 h × 8 × 3600 s). The same price applies to the prover. |
| `bandwidth_fusd_per_byte` | **82 000** (USD 8.2e-11) | ESTIMATE | Egress USD 0.05/GB (AWS high-volume tier) × upload amplification 1.64. Partial-witness Reed-Solomon uses `WITNESS_RATIO_DATA_PARTS = 0.6` (`partial_witness/encoding.rs:6`); with N = 84 there are 50 data parts, and each validator forwards its part to 82 others (`partial_witness_actor.rs:442-477`). Ingress is free. |
| `storage_fusd_per_byte` | **0** | estimate | Validators drop the witness after endorsing. Only the endorsement signature reaches the block (`chunk_endorsement.rs:98-134`). |
| `prepare_amortization_requests` | **0** (not charged) | estimate | `prepare` runs once per release, against millions of chunks per release (43 200 heights per epoch × 10 shards), so its amortized share is noise. It stays capped and reported (§2). |

Context facts that the model does not use directly, from nearcore 2.13.4:

* uncompressed witness ≤ 64 MiB (`state_witness.rs:19`), with a design
  target of ≈ 17 MiB worst case (`docs/misc/state_witness_size_limits.md`);
* compressed witness ≤ 48 MiB (`partial_witness.rs:18`), zstd level 1;
* `main_storage_proof_size_soft_limit` = 4 MB (`72.yaml:1`);
* mainnet block time ≥ 600 ms (`nearcore/src/config.rs:76`).

### 14.8 Offline re-scoring of the admitted entries

#### Under the governed model v2, with re-measured references (2026-10-06)

**Reference re-measurement.** For each challenge, the pinned
`baseline_submission` package was re-packed from git and checked to be
byte-identical to the pin: v1-6 `sha256:329c763a…` from `6b4ae2f`, v3 D0-1
`sha256:63618259…` from `e50d17d`. It was then measured on the live benchmark
CPUs 0–7 through the worker's own BENCHMARK stage (`run_baseline.py` →
`bench_session`, Firecracker `firecracker-rc`, `vm_per_batch`, judge-secret
sampling under the live season commitment `sha256:b860eb74…`, sampled for the
live challenge id). Live `w1` was stopped for the windows (07:45–08:06 and
08:06–08:15 UTC) with no job queued or leased. Each run was 1 + 2 control sessions on the
same batches (§14.4).

| challenge | session | prove ms/batch (frozen) | verify ms/batch (per-run median) | proof KiB/batch | verify control |
|---|---|---|---|---|---|
| v3 D0-1 | `costbase-near-chunk-validation-d0-1-secret-cpus0-7-20261006` | quiet 6.77 (7.00), transfers 7.14 (6.96), missing 7.23 (7.13) | quiet **813.6**, transfers **923.8**, missing **632.1** | 15.7 / 27.7 / 33.1 | **PASS** (control 2: 5 342 / 19 673 / 4 041 ppm; control 1 infra-invalid, SESSION_DRIFT) |
| v1-6 attempt 1 | `…-v1-6-…-20261006-attempt1-verify-drift` | batch-1 6.97, batch-16 7.40, batch-256 10.03 | 39.1 / **164.2** / 1509.8 | 6.1 / 47.0 / 507.3 | **FAIL** VERIFY_DRIFT: batch-16 43 293 and 41 464 ppm (both controls valid, both ≈ 171 ms); batch-1 ≤ 5 312, batch-256 ≤ 17 416 |
| v1-6 attempt 2 | `…-v1-6-…-20261006-attempt2-verify-drift` | 6.82 / 7.81 / 10.41 (frozen 6.21 / 6.88 / 10.21) | 38.9 / **157.2** / 1524.0 | 6.1 / 47.0 / 507.3 | **FAIL** VERIFY_DRIFT: batch-16 160 774 ppm (valid control at 182.5 ms); batch-1 21 948, batch-256 19 546 |

On v3 D0 the reference verify reproduces within 3%, and the cost baseline is
confirmed. On v1-6 the **batch-16 reference verify is bimodal**: the per-run
totals of one session cluster near 150 ms and near 185–215 ms, so the median
of 15 runs moves by 4–21% between sessions on identical batches. The control
caught exactly the failure it was added for. Per §14.4 the v1-6 cost baseline
is **not confirmed**, and a governed v1-6 cost challenge cannot be pinned from
these sessions. The fix is a measurement change, not a wider tolerance: more
measured runs for verify, or a verify median over pooled sessions, as a
bench-spec change. Batch-1 and batch-256 pass in every valid control.

The per-run verify totals of v3 D0 are 1.6–4.2× (8 × the per-proof median).
Verify time is heavy-tailed in the input: in every d0-quiet batch, two of the
eight sampled chunks verify in ≈ 320–350 ms and the other six in 12–68 ms.
The cost formula charges the batch total, which is the right quantity (the
median per proof would hide the expensive chunks). It does so for the
reference and every candidate alike.

**Scores.** `python -m arena_bench cost-rescore --cost-baseline …` (inputs
copied from the live object store; runs untouched). The reference prove is
the frozen `baseline_ns`. Reference verify and bytes come from the re-measured
session. "ref as in control" re-scores against the valid control session's
medians and shows how far the choice of session moves the score.

v3 D0-1 (`benchmarks/results/cost-rescore-v3-d0-1-pm-v2-20261006/`, exact
per-run bytes, reference **confirmed**):

| candidate | speed (live) | **cost_v1 (v2)** | ref as in control | N_v=1 | N_v=84 | c_bw=0 | verify priced at 2 vCPUs |
|---|---|---|---|---|---|---|---|
| reexec-v3-d0-fast (`sub_2b51fbde…`) | 104.566 | **78.766 ± 1.535** | 79.513 | 78.931 | 78.764 | 77.734 | 81.422 |
| reexec-v3-d0 normal form (`sub_0826bb9b…`) | 4.504 | **74.600 ± 3.662** | 75.308 | 66.229 | 74.679 | 73.515 | 76.855 |

v1-6 (`benchmarks/results/cost-rescore-v1-6-pm-v2-20261006/`, bytes upper
bound because five sessions predate per-run byte totals; reference
**UNCONFIRMED**, so the scores are indicative):

| candidate | speed (live) | v1 draft (N_v=84, 2026-10-05) | **cost_v1 (v2)** | ref as in control | N_v=1 | N_v=84 | c_bw=0 | verify priced at 2 vCPUs |
|---|---|---|---|---|---|---|---|---|
| reexec-npai (`sub_7ef24373…`) | 97.324 | 207.592 | **222.554 ± 0.641** | 231.354 | 213.516 | 222.643 | 2187.299 | 118.352 |
| reexec-witness (`sub_c67dd93b…`) | 98.376 | 93.492 | **100.270 ± 2.225** | 104.235 | 100.144 | 100.271 | 104.549 | 96.469 |
| reexec-witness-fast (`sub_314aa809…`) | 110.007 | 91.318 | **97.942 ± 1.073** | 101.815 | 98.263 | 97.939 | 100.688 | 95.311 |
| np-udr-stark-fast2 (`sub_ec1fdc22…`) | 0.070 | — | **1.632 ± 0.003** | 1.696 | 1.087 | 1.640 | 6.725 | 0.909 |
| np-udr-stark (`sub_19cc9c90…`) | 0.052 | 1.528 | **1.628 ± 0.001** | 1.692 | 0.991 | 1.639 | 6.656 | 0.906 |
| np-udr-stark-fast (`sub_56bb976b…`) | 0.048 | 1.496 | **1.596 ± 0.002** | 1.659 | 1.016 | 1.604 | 6.672 | 0.887 |

What moved, and why:

* **N_v 84 → 50 hardly moves any score** (compare the N_v=84 column). For the
  reexec family the cost is almost all validator-side, and that side scales with
  `N_v` for the reference and the candidate alike. Only the STARKs (≈ 1–2%
  prover share) and the v3 Lean prover (`sub_0826bb9b…`, prove 124–196 ms per
  batch) gain anything from a smaller committee. The latter is still 74.6 at
  N_v = 50 against 66.2 at N_v = 1.
* **The v1-6 changes against the draft re-scoring come from the re-measured
  reference** (verify 1365 → 1524 ms on batch-256, 128 → 157 ms on batch-16),
  not from N_v. The reference package now scores ≈ 100 against its own
  re-measurement (`sub_c67dd93b…` 100.27; that is the re-vendored build of
  the same verifier source).
* **v3 D0: both admitted entries cost more than the reference** (74.6 and
  78.8), the reverse of the speed board (fast child 104.6). Their normal-form
  verifier (`normalW`) does more work per proof than the canonical-only
  reference it is measured against: 923–1148 ms against 632–924 ms per batch.
  The speed board does not see this, because it measures prove time only. It
  is the price of rejecting the `v3-witness-freedoms` malleability (§5e of
  LIVE.md), and it is now visible.

#### Cost-scored successors (bench-spec-v1.4, 2026-10-06)

The references were measured on unsigned measure drafts: the predecessor with
25 measured runs, `baseline` null and the new name. Each run used
`run_baseline.py --verify-statistic lower_quartile --control-sessions 2
--before-session "arena-live stop worker@w1"`, so the CPU window covers only
the sessions, not the build.

| successor | reference | result | verify (lower quartile, ms/batch) | control |
|---|---|---|---|---|
| `near-transfer-receipt-v1-7` | `examples/reexec-witness` @ HEAD (`sha256:233924e8…`) | **pinned, signed** | batch-1 37.5, batch-16 127.8, batch-256 1498.7 | valid control 2: 25 536 / 12 561 / 8 688 ppm; control 1 infra-invalid (SESSION_DRIFT), and it would also have passed |
| `near-chunk-validation-d0-2` | `examples/reexec-v3-d0-fast` @ HEAD (`sha256:f02389d7…`) | **not pinned** | quiet 882–927, transfers 1516–1574, missing 1114–1147 | 4 attempts, **no valid pinned session with a valid passing control**: attempt 4 (16:55 UTC, quieter host) pinned session SESSION_DRIFT, while its valid control was within 20 356 ppm; attempt 1 pinned session itself failed calibration (SESSION_DRIFT, CALIBRATION_NOISY); attempt 2 the only valid-by-own-calibration control ran 8% faster in calibration than the pinned session (host state changed) and 5% faster in every verify class; attempt 3 both controls failed their own calibration (one would have passed at ≤ 1.3%) |

The v1-6 batch-16 instability is gone under the lower quartile, on new batches
(2.6% worst class). Live v1-7 board, cost rank (speed): reexec-npai 264.522 (98.880),
reexec-witness 96.121 (91.433), reexec-witness-fast 93.609 (103.405), np-udr-stark-fast2
1.489 (0.065), np-udr-stark 1.476 (0.046), np-udr-stark-fast 1.475 (0.047); see LIVE.md §5f.
d0-2 is limited by the host, not by the statistic. Its
sessions are the longest (≈ 6 min, ≈ 1–1.6 s of verify per batch) on a shared
host whose calibration moved by up to 8% between sessions. The infra-retry
bound was exhausted, and a fourth attempt in a quieter window also failed. d0-2 is re-measured when the host is quiet. Its unsigned
measure draft is `challenges/drafts/near-chunk-validation-d0-2.measure.json`.
v3 D0-1 stays speed-scored until then.

#### Under the v1 draft (2026-10-05, superseded)

`python -m arena_bench cost-rescore` takes the judge's "benchmark session"
artifacts of the five ranked v1-6 submissions. It re-scores them against the
frozen v1-6 reference session
(`benchmarks/results/baseline-near-transfer-receipt-v1-6-secret-cpus0-7-20261005`)
and writes `benchmarks/results/cost-rescore-v1-6-draft-20261005/` (inputs
included, so the result is reproducible).

* Verify per run is exact: the flat measured-phase verify timings, chunked by
  `batch_size`.
* These sessions predate per-run byte totals, so proof bytes per run =
  `batch_size × proof_bytes_max`. This is an upper bound, applied identically
  to baseline and candidates.

| candidate | speed (live) | **cost_v1** | N_v=1 | N_v=30 | N_v=105 | c_bw=0 | c_bw×1.8 | verify priced at 2 vCPUs |
|---|---|---|---|---|---|---|---|---|
| reexec-npai (npai-v1) | 97.324 | **207.592 ± 0.599** | 199.5 | 207.4 | 207.6 | 1942.2 | 155.0 | 115.9 |
| reexec-witness (native-lean; = reference package) | 98.376 | **93.492 ± 2.074** | 93.6 | 93.5 | 93.5 | 92.4 | 93.9 | 94.5 |
| reexec-witness-fast (speed #1) | 110.007 | **91.318 ± 1.001** | 91.8 | 91.3 | 91.3 | 89.0 | 92.2 | 93.3 |
| np-udr-stark | 0.052 | **1.528 ± 0.001** | 0.93 | 1.50 | 1.53 | 6.12 | 1.18 | 0.89 |
| np-udr-stark-fast | 0.048 | **1.496 ± 0.002** | 0.95 | 1.48 | 1.50 | 6.10 | 1.15 | 0.87 |

What the cost board shows that the speed board hides:

* **Proving is about 0% of system cost for the reexec family** (≤ 0.4% in
  every class). For reexec-witness and its fast variant, validator verify is
  59–76% of cost and validator bandwidth 24–41%. The speed leader,
  reexec-witness-fast (a faster *prover*), falls below the reference: its
  verify measured 1555 ms per batch-256 batch, against 1365 ms in the
  reference session. That gap is within cross-session verify noise; the
  reference package itself re-measured at 1511 ms (§14.4).
* **reexec-npai halves the system cost and ranks first.** Its judge-run npai
  verifier is ≈ 30–35× faster here than the native-lean verifier (5.4 ms vs
  165–189 ms per batch-256 proof). Bandwidth is now 74–96% of its cost.
* **np-udr-stark moves up 30× (0.052 → 1.53) but remains 65× more expensive
  than re-execution.** Bandwidth is 83–86% of its cost: 1.9–3.1 MB proofs,
  against an ≈ 80 KB reexec proof (= witness) on batch-256, sent to 84
  validators. Verify is 14–16% (0.43–0.78 s per proof). Prove is ≤ 2%.
* **Break-even.** On these small-witness transfer workloads, a succinct proof
  reaches 100 at about **40 KiB and 5 ms verify per request with a 10× faster
  prover** (99.0); at 35 KiB it scores 110.8. Scores for hypothetical
  np-udr-stark profiles under this model:

  | proof / verify per request | prove time | cost_v1 score |
  |---|---|---|
  | 200 KiB / 50 ms | as measured | 17.2 |
  | 100 KiB / 20 ms | as measured | 31.7 |
  | 50 KiB / 10 ms | ÷10 | 76.8 |
  | 40 KiB / 5 ms | ÷10 | 99.0 |
  | 20 KiB / 5 ms | ÷100 | 194.6 |

  Real chunk witnesses are far larger (up to the 4 MB storage-proof soft limit
  and the ≈ 17 MiB worst-case design target). There, a 100–300 KB proof is
  where succinctness pays, which is the D-ladder's target.

### 14.9 Gaming analysis

| attack | effect under cost_v1 | defence |
|---|---|---|
| **Tiny proof, huge verify** (e.g. "proof" = hash, verify recomputes) | Verify is charged N_v × v_v × wall. A 100× slower verify costs ≈ 50× more than a slower prover would. | Cost term itself; `max_verify_ms`; the verifier is part of `VerifiedSurface` (§12). |
| **Witness as proof** (re-execution) | This is the status quo, and it scores as the reference does. Bytes and verify are charged N_v times. | Intended: it is the baseline to beat. |
| **Verify fast only on the judge's big box** | Verify is measured pinned to `verifier_vcpus` CPUs of the reference validator profile, so multi-thread speedups beyond the profile are not available. | §14.2 pinning. The next model version can lower `verifier_vcpus` (sensitivity column "2 vCPUs" shows the effect) or add a memory cap for verify. |
| **Parallel verify to cut wall time** | Pays for every reserved vCPU (allocated × wall); no gain beyond the profile. | §14.2. |
| **Proof compression outside the timed region** | Impossible: bytes are measured at `proof.bin`, and decompression runs inside `verify`. | §3.2, §14.3. |
| **Push work into `prepare`** | Not charged at A = 0; `prepare` is input-blind (§2), so it cannot depend on inputs. | §2 caps; set A > 0 if a model needs it. |
| **Ignore latency to minimise cost** (very slow but cheap prover) | Prove is ≈ 0% of cost, so a slow prover hardly moves the cost score. | `max_prove_ms` hard cap. The speed board stays primary for latency. A future model may add a per-request latency gate tied to block time (600 ms). |
| **Price-model shopping** | Not possible: the model is pinned by digest in the signed challenge, and results under another digest are never ranked. | §14.5, server and web digest checks. |
| **Noisy verify luck** | Verify is bootstrapped jointly with prove (CI). A drifted *reference* verify would move every score. | Verify drift control (§14.4): the pinned reference verify must be reproduced within 30 000 ppm on the benchmark CPUs before it is pinned, and again at each season re-check. |

### 14.10 Decisions (resolved 2026-10-06)

1. `N_v` = **50 validators per shard** (not 84 or 105). One chunk proof is
   verified by its shard's committee only.
2. `c_cpu` = USD 7.61e-6 per vCPU-second and `c_bw` = USD 8.2e-11 per byte per
   validator are kept as estimates. The measurement did not contradict them
   (§14.7).
3. `verifier_vcpus` = 8 is kept.
4. The verify drift control is added (§14.4). It is a prerequisite for pinning
   a `cost_baseline`.
5. The references were re-measured on the live benchmark CPUs with per-run byte
   totals (§14.8). Under the median (v1.3), v3 D0-1 passed the verify control
   and v1-6 failed it (batch-16 bimodal verify). bench-spec-v1.4 (§14.4.1)
   fixed the statistic. **`near-transfer-receipt-v1-7`** is the first
   cost-scored challenge (governed model v2, lower quartile, 25 runs). The v3
   successor `near-chunk-validation-d0-2` is not pinned yet because no control
   was valid on the shared host (§14.8).

### 14.11 Forward plan: one proof for all shards (multi-shard term, FUTURE, not scored)

**Why ZK at all.** Under `cost_v1` a per-chunk succinct proof competes with
re-execution only through a smaller `N_v × (verify + bytes)`. With
small witnesses the break-even is hard (§14.8). The structural advantage of ZK
is elsewhere: **one proof can cover every shard**. Re-execution cannot do
that today. A validator that checks a whole block must re-execute S chunks,
which needs S × the per-shard CPU, memory and witness bandwidth. That is more
than the standard 8-core validator profile, and it is why validation is
sharded with one committee per shard. A succinct proof of the whole block
costs a roughly flat verify and size whatever S is, so *every* validator can
check *every* shard.

**Price model extension (documented now, versioned later).** The statement
becomes a whole block of S shards, and the same formula is applied to it:

```
C_block = c_cpu·v_p·T_prove_block                         prover(s), incl. aggregation
        + N_v,block · ( c_cpu·v_v·T_verify_block + c_bw·bytes_block )
N_v,block = N_v · S            (all validators: 50 × S; e.g. 500 for S = 10)

re-execution reference:
  T_verify_block ≈ Σ_s T_verify_s   (grows linearly with S)
  bytes_block    ≈ Σ_s bytes_s      (grows linearly with S)
  feasibility    : must fit the reference validator profile (v_v, memory,
                   bandwidth); for S above what one 8-vCPU validator can
                   re-execute within the block time, the reference is priced at
                   v_v,ref = ⌈S·v_v / 8⌉·8 vCPUs and flagged EXCEEDS_PROFILE
succinct candidate:
  T_verify_block ≈ const, bytes_block ≈ const   (independent of S, up to log factors)
```

The baseline cost therefore grows ≈ S² (S × more validators, each doing
S × more work), while a succinct candidate's validator term grows only ≈ S
(more validators, same work each). That is the regime where ZK wins. The
per-chunk model above is the S = 1, N_v = 50 slice of it.

**How it lands (governance, not now).**

* A new price-model version (`arena-price-model-v2`, a schema change) adds
  `shards_per_statement` (S) and `validators_per_shard` (50). `N_v` is then
  derived as `validators_per_shard × S`. The reference's validator profile
  can be scaled with an `EXCEEDS_PROFILE` label. `arena-price-model-v1` and
  every `cost_v1` result stay as they are.
* A new **workload class / challenge**: a *cross-shard aggregate statement*
  whose relation is the conjunction, over the S chunks of one block, of the
  per-shard `validate_chunk_state_witness` relation that today's D0 challenge
  checks (same per-shard semantics, plus the block binding: the chunk headers
  of one block and its shard layout). A new scoring kind, say `cost_v2`, is
  pinned to it. That is a new statement, so it is a new challenge.
* **The current per-chunk challenges do not change.** The v1-6 and v3 D0
  statements, their fixtures, baselines and boards are untouched, and they
  remain the S = 1 calibration points of the extended model.

---

## 15. Contract notes for the integrator

bench-spec-v1 fits contracts v1 without changes. `scoring` (cost_v1, §14) is
the first such additive field (contracts v1.5). Constants that a future
version may still want per challenge are `measurement.spec_version`,
bootstrap iterations and drift thresholds. Adding any of them is a governed,
additive contract change (`docs/CHANGELOG-contracts.md`).

## 16. Tooling

```
cd benchmarks
python -m arena_bench score --input classes.json
python -m arena_bench bootstrap --input runs.json --seed N [--iterations B]
python -m arena_bench outliers --input runs.json --k 5
python -m arena_bench drift --pre a,b,c --post d,e,f [--reference-ns N]
python -m arena_bench schedule --classes a,b --seed N --cold 3 --warmup 2 --measured 9
python -m arena_bench seed --purpose schedule chl_... sub_... 1
python -m arena_bench report --input bundle.json --out report.md
python -m arena_bench host-profile --id <id> [--governed] [--note ...] --out host.json
python -m arena_bench gen-testvectors [--check]        # score.json + cost.json
python -m arena_bench cost-rescore --challenge chl.json --price-model pm.json \
    --baseline-session baseline/session.json [--cost-baseline costbase/summary.json [--allow-unconfirmed]] \
    --out DIR VIEW.json:SESSION.json...
python -m pytest benchmarks -q
```
