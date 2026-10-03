# SP1 zkVM candidate through the real arena pipeline

Date: 2026-10-03, shared dev host (AMD Ryzen 9 9950X3D, 32 threads, 125 GB, no GPU).
Generated with `tests/e2e/sp1-pipeline.sh` and `tests/e2e/sp1-pipeline-summary.py`.
Raw data: `sp1-pipeline/run1/` and `sp1-pipeline/run2-head/`. Each holds submission views
(`*.submission.json`), signed reports (`*.report.json`), leaderboards, the worker and server logs,
and `progress.log` (host load every 30 s).

## Verdict

| | challenge | SP1 decision | why (judge output) |
|---|---|---|---|
| **A**, current head | `chl_3be93793…` v1.2 (formal, signed, production checker pin) | **REJECTED** | FORMAL_CHECK: every formal gate and ARTIFACT_BINDING are `FAIL ARTIFACT_BINDING_FAILED` ("candidate-built native verifier: no route binds a candidate binary to the statement"). Fail-fast, so conformance never ran. |
| A, superseded | `chl_f7eb2d91…` v1.1, `chl_5ef2bc7d…` v1 | **refused at submit** | `HTTP 409 challenge_closed` (superseded) |
| A, v1 (run 1, before the merge) | `chl_5ef2bc7d…` (signed, as is) | **REJECTED** | formal gates `UNKNOWN` (this worker's checker identity ≠ v1's pin). `PROVER_RELIABILITY FAIL PROVER_FAILED` and `RESOURCE_LIMITS FAIL RESOURCE_LIMIT`: "case fixture/example-tierA: prove OOM-killed" under v1's 16 GiB cap. |
| A, v1 re-pinned (run 1) | `chl_dc78da24…` (e2e-local, = milestone-d re-pin) | **REJECTED** | same as the head: `ARTIFACT_BINDING_FAILED` on all formal gates |
| **B**, experimental | `chl_b03314c3…` (local key, experimental) | **REJECTED** | `AXIOM_AUDIT` and `ARTIFACT_BINDING` `FAIL ARTIFACT_BINDING_FAILED`. Fail-fast, nothing measured. |
| B′, demo measurement-only | `chl_b2e2046f…` (local key, demo) | **ADMITTED (demo, rank null)** | all 7 required gates PASS; judge-measured numbers below |
| reference `reexec-witness` on B | `chl_b03314c3…` | **ADMITTED (experimental, rank null)** | all 9 gates PASS; judge-measured numbers below |

SP1 was never ADMITTED on a formal or experimental challenge, and it was never ranked anywhere.

The judge did **not** report `CERTIFICATE_MISSING`, although SP1's `formal/` has no `Candidate.certificate`.
The formal checker tests the verifier route before it looks for the certificate. SP1 ships its own native
`verify` (no `verify_route`), and no route binds a candidate-built binary to the statement. So the checker
stops at `ARTIFACT_BINDING_FAILED` (`runners/formal-checker/src/pipeline.rs`). The verdict is right; the
reason code is less specific than it could be (see Findings).

`RESOURCE_LIMIT` appears only on v1 (run 1). There the formal gates were `UNKNOWN`, so the pipeline went
on to conformance, and the 16 GiB VM OOM-killed the first 2-receipt proof. On the v1.2 head the run is
decided at FORMAL_CHECK, before any `prove` runs.

### Why there is a demo twin (B′)

`arena-admin` policy requires every experimental challenge to include `ARTIFACT_BINDING`
(`tools/arena-admin/src/policy.rs`, `EXPERIMENTAL_MIN`). The judge fails that gate for any
candidate-built native verifier, and fail-fast decides the run before conformance. So **no experimental
challenge can measure SP1 as packaged.** I did not weaken that policy or the gate. Instead I signed a
**demo**-tier twin of B: same semantics, limits, procedure and hardware, but without the FORMAL_CHECK
gates. Demo is never ranked.

`reexec-witness` cannot run on B′. Its `native-lean` verifier is built by FORMAL_CHECK, which B′ does not
run. So the side-by-side compares **SP1 on B′** with **reexec on B**: same worker, same Firecracker
config, same CPUs, same limits, same procedure. The challenges differ only in tier and required gates.

## Judge-measured: SP1 (B′) vs reexec-witness (B)

Firecracker microVM with 8 vCPUs pinned to host CPUs 8–15 and 48 GiB guest RAM cap. `batch_size` = 1
per class (one request of 1 / 16 / 256 receipts). Procedure: cold 1, warmup 1, measured 3, plus 1
fresh-confirm round. Times are the judge's sandbox wall clock for one `prove` process, in ms. The memory
column is the **peak guest memory** of the VM (kernel + page cache + process), not the process RSS. That
is why reexec shows about 1 GiB, although its process RSS is a few MB.

| class | SP1 prove median (runs) | reexec prove median (runs) | SP1 verify | reexec verify | SP1 proof | reexec proof | SP1 peak guest mem | reexec peak guest mem |
|---|---|---|---|---|---|---|---|---|
| batch-1 | **80,710 ms** (78,768 / 80,710 / 83,719), cold 83,990 | **25.8 ms** (41.5 / 25.8 / 20.3) | 60.3 ms | 32.3 ms | 1,272,573 B | 794 B | 18.62 GiB | 1.01 GiB |
| batch-16 | **89,745 ms** (86,249 / 89,745 / 95,562), cold 94,352 | **29.8 ms** (29.8 / 51.2 / 21.1) | 54.8 ms | 38.9 ms | 1,272,573 B | 6,741 B | 19.06 GiB | 1.01 GiB |
| batch-256 | **139,718 ms** (135,971 / 150,002 / 139,718), cold 142,549 | **35.3 ms** (35.3 / 30.4 / 39.6) | 57.2 ms | 191 ms | 1,272,573 B | 65,704 B | 35.17 GiB | 1.01 GiB |

| | SP1 (B′) | reexec (B) |
|---|---|---|
| prepare (judge-run) | 10.9 s; `public.bin` 172 B | 9.3 ms; 110 B |
| conformance | 23/23 claims byte-equal to the oracle (20 public fixtures + 3 judge-sampled) | 23/23 |
| prover reliability | 23/23 honest proofs produced and accepted | 23/23 |
| resource limits (conformance) | max proof 1,272,573 B, max verify 88 ms, **peak 36,280 MiB** | max proof 66,512 B, max verify 186 ms, peak 1,038 MiB |
| adversarial | 155 hostile inputs (generic mutators + 15 `adv:*` families), **0 accepted** | 146 hostile inputs, 0 accepted |
| build | 2 builds in Firecracker, identical trees `sha256:16dd3534…`; **guest ELF rebuilt from source** in the build VM and equal to the pin `fdfeb40a…` | identical trees `sha256:29551ea1…` (same digest as milestone-d) |
| decision | ADMITTED (demo, not ranked) | ADMITTED (experimental, not ranked) |
| score | null (no baselines in these challenges) | null |

SP1's benchmark gate is PASS. Getting there took 5 sessions, all recorded in the gate summary. Sessions 1
and 2 were discarded for `EXCESSIVE_OUTLIERS`. Session 3 raised `CACHING_SUSPECTED`, so the judge
re-measured on fresh batches only. In the fresh-only phase, sessions 1 and 2 were again discarded for
outliers, and session 3 was published. The job took about 3 h (98 proofs). The cause is my procedure
choice, not SP1. With `measured_runs = 3`, one run outside 5·MAD is a 33 % outlier share, above the
spec's 20 % limit. On a shared host that happens often. A rerun should use `measured_runs >= 5`.

Compared with the candidate's own local numbers (README: 46–83 s prove on a quiet host, 16–38 GB): the
judge's prove times are 80–140 s at 8 vCPUs instead of 32 cores. The peak memory matches (19 / 19 /
35 GiB guest, 36 GiB worst case in conformance). Proof size is the same constant 1,272,573 B. Verify is
55–60 ms against 30–110 ms locally.

## Setup

* Worktree `lane/sp1-pipeline` (= `lane/runners-core` + main). Run 1 used the pre-merge code (HEAD
  `e0fe512`). Run 2 used the code after merging main (`fc95f36`; superseding closes challenges, NEAR v1.2
  head).
* Server: `arena-server serve --dev` on 127.0.0.1:18581 (worker API 18582), with its own database
  `arena_sp1` on the shared Postgres 127.0.0.1:55471. Governance keys: dev + local operator.
* Worker: one `arena-worker`, backend `firecracker`, tier cap formal. Pinned toolchain image (below);
  Lean toolchain from lean-checker image `d85133a1…` mounted at `/opt/lean`; FORMAL_CHECK in that image
  (checker identity `sha256:b6391b38…`); NEAR oracle (run 1: `runners-core` build; run 2: main build);
  `ARENA_CONFORMANCE_SAMPLES=3`; **`ARENA_RUN_CPUS=8-15`, `ARENA_BENCH_CPUS=8-15`**; no DEV batch cap.
  Only one candidate VM ran at a time.
* Host load (1-min load average, sampled every 30 s during run 1): median 7.9, range 1.8–40.5. Other
  lanes (milestone-d, builds, agents) ran at the same time, unpinned. Absolute times are therefore noisy.
* Packaging: `examples/zkvm-sp1/build-recipe/vendor.sh` (vendor digests equal
  `dependency-locks/vendor-digests.txt`), then `arena submit` (tar.zst, 32.8 MB upload, 21,170 files,
  231 MB expanded).

### Toolchain image with the SP1 `succinct` toolchain (guest rebuilt, covered by BUILD_REPRODUCIBLE)

`deploy/images/toolchain-sp1/build.sh` takes the pinned base build image `sha256:57a89fc6…`, re-checks
its TreeDigest, and adds the `succinct-1.96.0-64bit-v2` toolchain as the rustup custom toolchain
`/usr/local/rustup/toolchains/succinct`. The toolchain comes from its GitHub release tarball, sha256
`ff3afc3a…fb94b` (the asset `cargo prove install-toolchain` v6.8.1 installs). The image env adds
`RUSTUP_HOME`. `--check` assembles the image twice: both give `sha256:70d2b28003f8117601772dedb7f42393e928ccfcca7356a49d675ec3f878a8a1`.

With this image, `build.sh` rebuilds the guest ELF from source in the offline build VM. The build log
shows the guest `cargo build` (8 s) before the host build (4 min 14 s), and no `GUEST-NOT-REBUILT`. The
recipe exits non-zero unless the rebuilt ELF equals the pinned `fdfeb40a…`, so `BUILD_REPRODUCIBLE`
**covers the guest program**. All 5 SP1 submissions produced the same bundle tree `sha256:16dd3534…`.
Each pair of builds took about 9 min on 8 vCPUs. The image's TreeDigest is recorded in every
submission's `build.toolchain_image`.

### Challenges (local ones signed with `/data/illia/nearproof-deps/keys/governance-local.key`; all pass `arena-admin verify`)

All local challenges are derived from `chl_5ef2…` and stored in `sp1-pipeline/run1/challenges/`, not in
`challenges/`.

| label | id | tier | differs from `chl_5ef2…` in |
|---|---|---|---|
| A1 | `chl_5ef2bc7d2068219635426e47ca46bfbb` | formal | — (signed original) |
| A2 | `chl_dc78da24004f3efe07b97f3ecb11fe29` | formal | `checker_image` → `b6391b38…` (the same re-pin milestone-d signs; the same value v1.2 later pinned) |
| B | `chl_b03314c363f0bc1300ba31f00d23739c` | **experimental** | A2 + `required_obligations` = experimental minimum + BENCHMARK; `max_ram_bytes` 48 GiB; `max_prove_ms` 600 000; hardware profile `nearproof-local-ryzen9-9950x3d-fc8-48g` (8 vCPU, 48 GiB); measurement cold 1 / warmup 1 / measured 3, `batch_size` 1; season `2026-s1-EXPERIMENTAL-sp1-measurement` |
| B′ (M) | `chl_b2e2046f9d0c59e08660ba535a54bdd1` | **demo** | B without ARTIFACT_BINDING (no FORMAL_CHECK gate required); season `…-DEMO-sp1-measurement-only` |
| head | `chl_3be93793610370275ae40f36a475f01f` | formal | (main's signed v1.2) |

Semantics, spec, claim encoding, workload generators, fixtures, held-out commitment, security profile and
`formal_params` are unchanged in every challenge. `max_proof_bytes` stays 8 MiB, not the 4 MiB suggested:
the reference certificate's statement is instantiated with `formal_params.max_proof_bytes`, and the formal
tier requires that value to equal `resource_limits.max_proof_bytes`. SP1's 1.27 MB proofs fit either way.

### Commands

```sh
cd /data/illia/nearproof-wt/sp1-pipeline
bash examples/zkvm-sp1/build-recipe/vendor.sh          # from examples/zkvm-sp1 (network)
deploy/images/toolchain-sp1/build.sh --check            # -> sha256:70d2b280…a8a1
# run 1 (A1, A2, B, B′; pre-merge code)
ARENA_NEAR_ORACLE=/data/illia/nearproof-deps/sp1-pipeline-oracle tests/e2e/sp1-pipeline.sh
# run 2 (after merging main: SP1 to every signed NEAR challenge)
ARENA_SP1_MODE=head ARENA_SP1_ONLY=none ARENA_SP1_RESULTS=$PWD/docs/e2e-results/sp1-pipeline/run2-head \
  ARENA_NEAR_ORACLE=/data/illia/nearproof-deps/sp1-pipeline-oracle-main tests/e2e/sp1-pipeline.sh
python3 tests/e2e/sp1-pipeline-summary.py docs/e2e-results/sp1-pipeline/run1
```

The script runs `arena submit` → `arena status` (polled) → `arena report -o` → `arena leaderboard`.
Work dir: `/data/illia/nearproof-deps/sp1-pipeline/work`.

## Judge-side changes made for this run (tests green: `ARENA_DEV_UNSAFE=1 cargo test -p arena-worker`)

1. **`ARENA_RUN_CPUS`** (`runners/worker`). On Firecracker a VM gets one vCPU per `cpu_set` entry.
   BUILD, CONFORMANCE and ADVERSARIAL passed no `cpu_set`, so every build and every
   conformance/adversarial `prove` ran on **1 vCPU**, whatever the challenge's `hardware_profile` said
   (v1: 8 vCPUs). A multi-threaded prover would then be measured single-core and would time out the
   600 s cap. The new variable pins those runs to a host CPU set; unset keeps the old behaviour. No gate
   changed.
2. **CPU lists accept ranges** (`8-15`). `deploy/hardened/.../20-bench.conf` sets
   `ARENA_BENCH_CPUS=2-15`, which failed to parse before this change.
3. `deploy/images/toolchain-sp1/` (new image, above).

No gate, policy or decision rule was changed.

## Findings / open items

* **Policy gap, not fixed:** an experimental challenge must require ARTIFACT_BINDING, which a
  candidate-built native verifier always fails, and fail-fast then skips measurement. So no
  non-certified, natively verified candidate (SP1 as packaged) can get judge measurements outside the
  demo tier. Options: let experimental challenges measure first and decide afterwards, or give zkVM
  candidates a judge-built verifier route (e.g. the judge builds `sp1-verifier` from pinned source).
  This is a governance question, not something this run should change.
* **Reason code:** a candidate with no certificate *and* a native verifier is reported only as
  `ARTIFACT_BINDING_FAILED`. `CERTIFICATE_MISSING` is never reached, because the route check stops the
  checker first.
* v1/v1.1 pin a host-tools checker identity, so on the production worker the formal gates are `UNKNOWN`
  (run 1, A1). v1.2 fixes this; v1 and v1.1 are now closed.
* Measurement procedure: `measured_runs = 3` makes `EXCESSIVE_OUTLIERS` likely on a shared host
  (5 sessions, about 3 h for SP1). Use ≥ 5.
* Transient: shared-Postgres pool timeouts for about 30 s at 07:45 (heartbeat 500s). The lease survived.

## Gate tables — run 1 (pre-merge code; A1, A2, B, B′)

### sp1-A1: `sub_7d14a2973bab4ca3a9108a08cf7e4e3f`

challenge `chl_5ef2bc7d2068219635426e47ca46bfbb` · stage **DECIDED** · decision **REJECTED** · accepted False · tier `formal` · score None · run reason codes PROVER_FAILED, RESOURCE_LIMIT, OBLIGATION_UNDISCHARGED

| gate | status | reasons | summary |
|---|---|---|---|
| PKG_WELLFORMED | PASS |  | package TreeDigest sha256:906ac6eba6cce5d208a2961b58a25a526748140ad2f164f3ba7758117e2ed5d8; 21170 files, 230870757 bytes; manifest ok |
| BUILD_REPRODUCIBLE | PASS |  | two independent builds produced identical trees sha256:16dd35347e4d4f909329bcc195bc96e17f98902fb8740350189e21bf55e5ecc4; prepare 10921 ms, public dir 172 bytes, TreeDigest sha256:8adccff1f08de496a74fdd72ee8b2079f87efbad2ab94d9fa5c7a9ae5c1dd6ca |
| ARTIFACT_BINDING | UNKNOWN |  | this worker's checker (lean-checker image sha256:d85133a1309157e27d0bac50b20d6d96a59db3ee6d55830389366f7248ccb7e1, identity sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e) is not the challenge's pinned checker sha256:2de5b68465258abb9573333bf675d9fbc381386c7730f3f683a2a48e40e6561e |
| FORMAL_SEMANTIC_SOUNDNESS | UNKNOWN |  | this worker's checker (lean-checker image sha256:d85133a1309157e27d0bac50b20d6d96a59db3ee6d55830389366f7248ccb7e1, identity sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e) is not the challenge's pinned checker sha256:2de5b68465258abb9573333bf675d9fbc381386c7730f3f683a2a48e40e6561e |
| FORMAL_SEMANTIC_COMPLETENESS | UNKNOWN |  | this worker's checker (lean-checker image sha256:d85133a1309157e27d0bac50b20d6d96a59db3ee6d55830389366f7248ccb7e1, identity sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e) is not the challenge's pinned checker sha256:2de5b68465258abb9573333bf675d9fbc381386c7730f3f683a2a48e40e6561e |
| FORMAL_CRYPTO_SOUNDNESS | UNKNOWN |  | this worker's checker (lean-checker image sha256:d85133a1309157e27d0bac50b20d6d96a59db3ee6d55830389366f7248ccb7e1, identity sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e) is not the challenge's pinned checker sha256:2de5b68465258abb9573333bf675d9fbc381386c7730f3f683a2a48e40e6561e |
| FORMAL_IMPL_CONNECTION | UNKNOWN |  | this worker's checker (lean-checker image sha256:d85133a1309157e27d0bac50b20d6d96a59db3ee6d55830389366f7248ccb7e1, identity sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e) is not the challenge's pinned checker sha256:2de5b68465258abb9573333bf675d9fbc381386c7730f3f683a2a48e40e6561e |
| AXIOM_AUDIT | UNKNOWN |  | this worker's checker (lean-checker image sha256:d85133a1309157e27d0bac50b20d6d96a59db3ee6d55830389366f7248ccb7e1, identity sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e) is not the challenge's pinned checker sha256:2de5b68465258abb9573333bf675d9fbc381386c7730f3f683a2a48e40e6561e |
| ADVERSARIAL_PROOFS | UNKNOWN |  | could not obtain an honest proof (prove OOM-killed); see the conformance gates |
| CONFORMANCE_DIFFERENTIAL | UNKNOWN |  | 0/23 cases conform (20 public fixtures, 3 judge-sampled) |
| PROVER_RELIABILITY | FAIL | PROVER_FAILED | case "fixture/example-tierA": prove OOM-killed; 0/23 honest proofs produced and accepted |
| RESOURCE_LIMITS | FAIL | RESOURCE_LIMIT | case "fixture/example-tierA": prove OOM-killed; public cases: max proof 0 bytes (cap 8388608), max verify 0 ms (cap 10000), peak memory 0 MiB |

### sp1-A2: `sub_95839e104fd4470d89f764d41161fc81`

challenge `chl_dc78da24004f3efe07b97f3ecb11fe29` · stage **DECIDED** · decision **REJECTED** · accepted False · tier `formal` · score None · run reason codes ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED

| gate | status | reasons | summary |
|---|---|---|---|
| PKG_WELLFORMED | PASS |  | package TreeDigest sha256:814a299a8c9c5136a92a1caef112cf0d5094b21f6ac3ab1262b0704a9b36fbca; 21170 files, 230870757 bytes; manifest ok |
| BUILD_REPRODUCIBLE | PASS |  | two independent builds produced identical trees sha256:16dd35347e4d4f909329bcc195bc96e17f98902fb8740350189e21bf55e5ecc4; prepare 10892 ms, public dir 172 bytes, TreeDigest sha256:8adccff1f08de496a74fdd72ee8b2079f87efbad2ab94d9fa5c7a9ae5c1dd6ca |
| FORMAL_SEMANTIC_SOUNDNESS | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| FORMAL_SEMANTIC_COMPLETENESS | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| FORMAL_CRYPTO_SOUNDNESS | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| FORMAL_IMPL_CONNECTION | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| AXIOM_AUDIT | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| ARTIFACT_BINDING | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |

### sp1-B: `sub_36cd12e5721743a0ac0edfc271e78323`

challenge `chl_b03314c363f0bc1300ba31f00d23739c` · stage **DECIDED** · decision **REJECTED** · accepted False · tier `experimental` · score None · run reason codes ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED

| gate | status | reasons | summary |
|---|---|---|---|
| PKG_WELLFORMED | PASS |  | package TreeDigest sha256:64ea7adcb63781f13315c27febc6041ddd033bb6f0629145c4206988a580f9b5; 21170 files, 230870757 bytes; manifest ok |
| BUILD_REPRODUCIBLE | PASS |  | two independent builds produced identical trees sha256:16dd35347e4d4f909329bcc195bc96e17f98902fb8740350189e21bf55e5ecc4; prepare 11069 ms, public dir 172 bytes, TreeDigest sha256:8adccff1f08de496a74fdd72ee8b2079f87efbad2ab94d9fa5c7a9ae5c1dd6ca |
| AXIOM_AUDIT | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| ARTIFACT_BINDING | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |

### reexec-B: `sub_986a4d988a58433e9785b7ab8d1a2e1d`

challenge `chl_b03314c363f0bc1300ba31f00d23739c` · stage **DECIDED** · decision **ADMITTED** · accepted True · tier `experimental` · score None · run reason codes —

| gate | status | reasons | summary |
|---|---|---|---|
| PKG_WELLFORMED | PASS |  | package TreeDigest sha256:1f192ddf18c09c716252a59f3396896e0332b9ee76453d67975356f8c97a3a7f; 682 files, 6595205 bytes; manifest ok |
| BUILD_REPRODUCIBLE | PASS |  | two independent builds produced identical trees sha256:29551ea16cf95ec71752ca2b5b693629e221213fce56d6d85c99a5a949544a98; prepare 7 ms, public dir 110 bytes, TreeDigest sha256:b7fa448e64a4e0a012bc8e05bf591ecc257861addbed2bac49e4db70db0e39e8 |
| AXIOM_AUDIT | PASS |  | certified closure uses only allowlisted axioms; no sorry/native shortcuts |
| ARTIFACT_BINDING | PASS |  | verifier executable is the judge's build of the certified Lean model; its digest is pinned in the statement (binary↔model edge: trusted Lean compiler/runtime) |
| CONFORMANCE_DIFFERENTIAL | PASS |  | 23/23 cases conform (20 public fixtures, 3 judge-sampled) |
| PROVER_RELIABILITY | PASS |  | 23/23 honest proofs produced and accepted |
| RESOURCE_LIMITS | PASS |  | public cases: max proof 66512 bytes (cap 8388608), max verify 186 ms (cap 10000), peak memory 1038 MiB |
| ADVERSARIAL_PROOFS | PASS |  | 146 hostile inputs from [truncate,bitflip,empty,oversize,swap,append,adv:empty,adv:truncate,adv:extend-trailing,adv:bitflip,adv:malformed-length,adv:noncanonical,adv:altered-commitment,adv:truncated-merkle-path,adv:swapped-siblings,adv:duplicated-node,adv:node-type-confusion,adv:transcript-tamper,adv:domain-separation,adv:mismatched-context,adv:recursive-substitution]: 146 rejected, 0 errored (not accepted), 0 timed out (not accepted), 0 accepted |
| BENCHMARK | PASS |  | challenge has no frozen baseline for every class: measured, not scored; batch-1: median 25835 us, MAD 5559 us, verify median 32253 us, max proof 794 B; batch-16: median 29757 us, MAD 8629 us, verify median 38893 us, max proof 6741 B; batch-256: median 35346 us, MAD 4287 us, verify median 190534 us, max proof 65704 B |

### sp1-M: `sub_d2b7cc86c4c24c63b4abdae2e6cb7ab2`

challenge `chl_b2e2046f9d0c59e08660ba535a54bdd1` · stage **DECIDED** · decision **ADMITTED** · accepted True · tier `demo` · score None · run reason codes DEMO_ONLY

| gate | status | reasons | summary |
|---|---|---|---|
| PKG_WELLFORMED | PASS | DEMO_ONLY | package TreeDigest sha256:e051705566478272a640845d53f3502cd2331cce1efad4635dfa690d47e9a5d3; 21170 files, 230870757 bytes; manifest ok |
| BUILD_REPRODUCIBLE | PASS | DEMO_ONLY | two independent builds produced identical trees sha256:16dd35347e4d4f909329bcc195bc96e17f98902fb8740350189e21bf55e5ecc4; prepare 11903 ms, public dir 172 bytes, TreeDigest sha256:8adccff1f08de496a74fdd72ee8b2079f87efbad2ab94d9fa5c7a9ae5c1dd6ca |
| CONFORMANCE_DIFFERENTIAL | PASS | DEMO_ONLY | 23/23 cases conform (20 public fixtures, 3 judge-sampled) |
| PROVER_RELIABILITY | PASS | DEMO_ONLY | 23/23 honest proofs produced and accepted |
| RESOURCE_LIMITS | PASS | DEMO_ONLY | public cases: max proof 1272573 bytes (cap 8388608), max verify 88 ms (cap 10000), peak memory 36280 MiB |
| ADVERSARIAL_PROOFS | PASS | DEMO_ONLY | 155 hostile inputs from [truncate,bitflip,empty,oversize,swap,append,adv:empty,adv:truncate,adv:extend-trailing,adv:bitflip,adv:malformed-length,adv:noncanonical,adv:altered-commitment,adv:truncated-merkle-path,adv:swapped-siblings,adv:duplicated-node,adv:node-type-confusion,adv:transcript-tamper,adv:domain-separation,adv:mismatched-context,adv:recursive-substitution]: 155 rejected, 0 errored (not accepted), 0 timed out (not accepted), 0 accepted |
| BENCHMARK | PASS | DEMO_ONLY | session 1 discarded (EXCESSIVE_OUTLIERS:batch-1); re-measured; session 2 discarded (EXCESSIVE_OUTLIERS:batch-256); re-measured; session 3: CACHING_SUSPECTED; re-measured on fresh batches only; session 1 discarded (EXCESSIVE_OUTLIERS:batch-256); re-measured; session 2 discarded (EXCESSIVE_OUTLIERS:batch-1); re-measured; challenge has no frozen baseline for every class: measured, not scored; batch-1: median 80709712 us, MAD 1941618 us, verify median 60316 us, max proof 1272573 B; batch-16: median 89745104 us, MAD 3496339 us, verify median 54830 us, max proof 1272573 B; batch-256: median 13971839 |

### Benchmark table (generated)

| class | candidate (challenge) | prove median ms (runs) | MAD ms | cold ms | verify median ms | max proof bytes | peak guest mem |
|---|---|---|---|---|---|---|---|
| batch-1 | sp1-M (`chl_b2e2046f…`) | 80,710 (78,768, 80,710, 83,719) | 1,942 | 83,990 | 60.3 | 1,272,573 | 18.62 GiB |
| batch-1 | reexec-B (`chl_b03314c3…`) | 25.8 (41.5, 25.8, 20.3) | 5.6 | 39.8 | 32.3 | 794 | 1.01 GiB |
| batch-16 | sp1-M (`chl_b2e2046f…`) | 89,745 (86,249, 89,745, 95,562) | 3,496 | 94,352 | 54.8 | 1,272,573 | 19.06 GiB |
| batch-16 | reexec-B (`chl_b03314c3…`) | 29.8 (29.8, 51.2, 21.1) | 8.6 | 15.1 | 38.9 | 6,741 | 1.01 GiB |
| batch-256 | sp1-M (`chl_b2e2046f…`) | 139,718 (135,971, 150,002, 139,718) | 3,748 | 142,549 | 57.2 | 1,272,573 | 35.17 GiB |
| batch-256 | reexec-B (`chl_b03314c3…`) | 35.3 (35.3, 30.4, 39.6) | 4.3 | 34.2 | 191 | 65,704 | 1.01 GiB |

* sp1-M: prepare 10,913 ms, public artifacts 172 bytes, measured_by `arena-worker sp1-fc-worker`, score None
* reexec-B: prepare 9.3 ms, public artifacts 110 bytes, measured_by `arena-worker sp1-fc-worker`, score None


## Gate tables — run 2 (merged main; signed head)

    sp1-chl_3be93793610370275ae40f36a475f01f -> sub_e4c0b5a8b3814a24bc2b053d1d4b8406 (challenge chl_3be93793610370275ae40f36a475f01f)
    sp1-chl_f7eb2d91bf7b363eee134b6ad9d3e011 -> REFUSED by the server (challenge chl_f7eb2d91bf7b363eee134b6ad9d3e011): uploading 32806048 bytes (sha256:ae772aedb3d318d242aa0992ce51b3e4552bfaf8b3457271e316a3d8e6067305) arena: error: HTTP 409: {"error":{"code":"challenge_closed","message":"challenge is superseded by chl_3be93793610370275ae40f36a475f01f and closed for new submissions; submit against chl_3be93793610370275ae40f36a475f01f"}} 
    sp1-chl_5ef2bc7d2068219635426e47ca46bfbb -> REFUSED by the server (challenge chl_5ef2bc7d2068219635426e47ca46bfbb): uploading 32806049 bytes (sha256:63e52ed6c44f6726fceb8084fdd863c6e46472f7ed897f625bf1abbf332bcb72) arena: error: HTTP 409: {"error":{"code":"challenge_closed","message":"challenge is superseded by chl_f7eb2d91bf7b363eee134b6ad9d3e011 and closed for new submissions; submit against chl_f7eb2d91bf7b363eee134b6ad9d3e011"}} 

### sp1-chl_3be93793610370275ae40f36a475f01f: `sub_e4c0b5a8b3814a24bc2b053d1d4b8406`

challenge `chl_3be93793610370275ae40f36a475f01f` · stage **DECIDED** · decision **REJECTED** · accepted False · tier `formal` · score None · run reason codes ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED

| gate | status | reasons | summary |
|---|---|---|---|
| PKG_WELLFORMED | PASS |  | package TreeDigest sha256:de81913866cf61d7ed0414f61387c94c154a87c972aa03cb4fe108d86cf5290a; 21170 files, 230870757 bytes; manifest ok |
| BUILD_REPRODUCIBLE | PASS |  | two independent builds produced identical trees sha256:16dd35347e4d4f909329bcc195bc96e17f98902fb8740350189e21bf55e5ecc4; prepare 11327 ms, public dir 172 bytes, TreeDigest sha256:8adccff1f08de496a74fdd72ee8b2079f87efbad2ab94d9fa5c7a9ae5c1dd6ca |
| FORMAL_SEMANTIC_SOUNDNESS | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| FORMAL_SEMANTIC_COMPLETENESS | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| FORMAL_CRYPTO_SOUNDNESS | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| FORMAL_IMPL_CONNECTION | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| AXIOM_AUDIT | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |
| ARTIFACT_BINDING | FAIL | ARTIFACT_BINDING_FAILED | candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = "native-lean" so the judge builds it from the model) |

