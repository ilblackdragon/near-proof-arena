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
  capped by `resource_limits.max_verify_ms` (§9), but not part of the score.
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

  **Open item.** No challenge uses `vm_per_batch` yet. A mode change alters
  scores, so it needs a new superseding challenge with a re-measured
  baseline, and a signed challenge is never edited. Three dev-host sessions
  (`benchmarks/results/baseline-near-transfer-receipt-v1-r1-vmperbatch-devhost-20261003/`)
  gave 8–18 ms per 8-request batch, against ~210 ms under
  `vm_per_invocation`. All three failed the calibration drift checks, so
  nothing was pinned. Next steps: re-measure on a quiet or governed host,
  pin `near-transfer-receipt-v1-2`, and deploy the rebuilt images.

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

### 11.2 Commit-reveal of the season secret

* Before a season opens governance publishes
  `commit = sha256("near-arena-secret-commit-v1\0" || season_secret)`
  (secret ≥ 32 random bytes) in the season manifest.
* The secret lives only in the judge's sampling service.
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

## 14. Cost-normalized board

A cost board is shown **only** when governance publishes a versioned price
model; it never replaces the time board. Format (`arena-price-model-v1`,
JCS-hashed, integers only, stored under `benchmarks/price-models/`):

```json
{
  "schema": "arena-price-model-v1",
  "id": "pm-2026q4",
  "version": 1,
  "effective_from": "2026-10-01",
  "currency": "USD",
  "unit": "micro_usd_per_hour",
  "source": "public on-demand list prices, region X, retrieved 2026-09-30",
  "profiles": [
    {"hardware_profile": "cpu-epyc-32", "micro_usd_per_hour": 1536000},
    {"hardware_profile": "gpu-h100-1",  "micro_usd_per_hour": 2990000}
  ]
}
```

`cost_j = ceil(T_cand_j_ns * micro_usd_per_hour / 3_600_000)` (integer,
pico-USD); the cost score uses the §8 formula with costs instead of times
and the baseline's cost on its own profile. The price-model digest is shown
on every cost-board row; changing prices is a new version, never an edit.

---

## 15. Contract notes for the integrator

bench-spec-v1 fits contracts v1 without changes. Constants that a future
version may want per challenge (none required now): `measurement.spec_version`,
`measurement.prepare_amortization`, bootstrap iterations / drift thresholds,
`scoring.price_model` digest. Adding any of them is a governed, additive
contract change (`docs/CHANGELOG-contracts.md`).

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
python -m arena_bench gen-testvectors [--check]
python -m pytest benchmarks -q
```
