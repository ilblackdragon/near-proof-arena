# Evidence coverage

This document lists, for every link between pinned nearcore and the exact
artifacts the arena executes, what kind of evidence supports that link today.
It covers `main` at the time of writing. Columns marked **in progress** are
backends that other lanes are still building; they will be refreshed when
those lanes merge.

## Status vocabulary

| status | meaning |
|---|---|
| **CHECKED** | Proved, and the proof accepted by a kernel: the Lean kernel through `leanchecker`, plus `nanoda`, plus `lean4lean` where it says so. A digest-equality check counts only where it says "(digest)". |
| **TRUSTED** | Assumed correct. The entry names the TCB row in `docs/TCB.md` (`TCB#n`). |
| **TESTED** | Differential, fuzz, or fixture testing. The entry gives the case count and says whether it was re-run for this document (**re-run**) or is only a committed or README result (**reported**). |
| **MISSING** | No evidence on `main`. |
| **N/A** | Not applicable to this backend or profile. |

"Pipeline" means the arena itself producing the evidence through
`arena-server`, leased jobs and workers. "Manual" means someone ran a
component directly, outside the pipeline. **Today no formal evidence is
produced by the pipeline**, for the reasons in `docs/ARCHITECTURE.md` §9. All
CHECKED entries below come from manual runs of the real checker in the
`bwrap-dev` sandbox, so they are tier-capped at `demo`.

Backends (columns):

* **RW**: `examples/reexec-witness` (and its prover-only child
  `reexec-witness-fast`). Route `verify_route = "native-lean"`. Merged.
* **RN**: re-execution via NPAI bytecode, route `npai-v1`. **In progress:
  `lane/npai-near`**. On `main` there is only `examples/npai-ir`.
* **SP1**: zkVM (SP1). **In progress: `lane/backend-zkvm`**. No code on `main`.
* **P3**: STARK (Plonky3). **In progress: `lane/backend-plonky3`**. No code on
  `main`.

## Reproduced for this document (2026-10-03, worktree at `10e7139`)

| what | command | result |
|---|---|---|
| RW certificate through the real checker | `formal-check --formal examples/reexec-witness/formal --certificate ReexecWitness.certificate --challenge challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json --challenge-config runners/formal-checker/challenges/near-transfer-receipt-v1.json --repo-root <clean git export> --public-digest 38c230e8… --native-model ReexecWitness.Model.verifier@ReexecWitness.Model --candidate-native-binary out/verify` (`ARENA_DEV_UNSAFE=1`) | All 6 gates PASS: `FORMAL_SEMANTIC_SOUNDNESS`, `FORMAL_SEMANTIC_COMPLETENESS`, `FORMAL_CRYPTO_SOUNDNESS`, `FORMAL_IMPL_CONNECTION`, `AXIOM_AUDIT`, `ARTIFACT_BINDING`. leanchecker, nanoda and lean4lean accepted. Closure is 2767 declarations; axioms ⊆ {propext, Classical.choice, Quot.sound}. Judge-built verify is `sha256:3931ac6f…0ac94`. Runner bwrap-dev, tier cap demo, 29 s. |
| RW build reproducibility | `bash build-recipe/build.sh` on a fresh copy | `out/verify` = `sha256:3931ac6f…`, identical to the digest in the README and the judge's native-lean build |
| RW claims vs oracle fixtures | `out/prove` on `oracle/fixtures/public/cases/*` | 20/20 claims byte-identical to `expected_claim.bin`; 20/20 honest proofs accepted by `out/verify` |
| RW hostile proofs | `run-mutants --verify out/verify --seed 1` on those 20 cases | 792 mutants across 9 mutators (packaging, semantic, binding); **0 accepted** |
| NPAI interpreter vs Lean reference | `npai-difftest --cases 200000 --seed 42` | 200,001 cases, **0 disagreements** |
| Checker negative suite | `cargo test -p arena-formal-checker --test formal_core --test near_spec --test native_route` with `ARENA_DEV_UNSAFE=1 FC_NEAR_SPEC=1 FC_FORMAL_CORE_DIR=formal-core` | Toy certificate PASS. All 11 `formal-core/negative` attacks rejected with the expected codes. NEAR expected-statement reference build OK. Native-route attacks rejected. |
| Lean projects | `make lean` | `formal-core` and `spec/lean` build, with no `sorry`/`axiom` in sources |

---

## 1. The chain

```
pinned nearcore + RuntimeConfig ──(1)──► NearSpec (formal NEAR semantics) ──(2)──► claim encoding
        │                                     │
        │                                     └──(3)──► backend semantics B ──(4)──► security theorem
        │                                                                              (AdmissionStatement)
        │                                                       ┌──(5)── assumptions (CR / ROM)
        ▼                                                       ▼
   oracle (expected_claim) ──(9)──► conformance      production verifier / parser / params ──(6)──► formal verifier
                                                               │
                                                               └──(7)──► exact built artifacts ──(8)──► executed by the arena
```

| # | edge | RW (native-lean) | RN (npai-v1) — in progress `lane/npai-near` | SP1 — in progress `lane/backend-zkvm` | P3 — in progress `lane/backend-plonky3` |
|---|---|---|---|---|---|
| 0 | nearcore pin → challenge | **TRUSTED** (TCB#11, TCB#16): signed `nearcore.commit = 44f7ae6c…` (2.13.4), `protocol_version` 86, `runtime_config_digest sha256:ae2d1af8…`. `oracle/scripts/link-nearcore.sh` refuses a checkout whose HEAD differs. | same (shared) | same | same |
| 1 | nearcore → NearSpec (`spec/lean`) | **TESTED, reported**: 3-way difftest (nearcore `Runtime::apply` oracle vs Lean `nearspec-check` vs Python `spec_check.py`), **1712 cases** (1502 in-domain, 210 out-of-domain), 0 disagreements, seed 4242 (`spec/difftest-report.json`). Synthetic state only; Transfer-only, PV86. Not re-run here (needs a nearcore build) and not in CI. **Not CHECKED**: `spec/near-transfer-receipt-v1.md` §6 says faithfulness is tested, not proved. | same (shared) | same | same |
| 1a | NearSpec scope vs real chain | **MISSING** for the 23 `semantic_scope.excludes` (e.g. `onchain_post_state_root`, `failure_paths_and_rollback`, `function_calls_and_wasm`). The post root is a slice projection, not the on-chain root. Historical mainnet data: **in progress `lane/historical`**. Wider scope: **in progress `lane/spec-v2`, `lane/challenge-v2`**. | same | same | same |
| 2 | NearSpec ↔ claim bytes (`spec/claim-v1.md`) | **CHECKED**: `decodeClaim_encode`, `Claim.encode_injective`, `WfClaim.decode_encode` (`spec/lean/NearSpec/ClaimCodec.lean`). The prose spec ↔ Lean codec link is **TRUSTED** (TCB#5). | same | same | same |
| 3 | NearSpec → backend semantics (`SemSound`, `SemComplete`) | **CHECKED** (re-run): `B := NearRelation`, `Aux := Witness` (`examples/reexec-witness/formal/.../Obligations.lean`) | **MISSING** on main | **MISSING** | **MISSING** |
| 4 | backend → security theorem (`CryptoSound`, `VerifierComplete`) | **CHECKED** (re-run): `cryptoSound := DeterministicSound` (ε = 0, no assumption); completeness from `Roundtrip.lean` + `Size.lean` for `maxProofBytes ≥ 3,088,869` | **MISSING** | **MISSING** | **MISSING** |
| 4a | `AdmissionStatement` expresses what we mean | **TRUSTED** (TCB#4, `formal-core`). Partially **CHECKED** by the anti-vacuity lemmas in `formal-core/ArenaCore/Sanity.lean` (accept-all is not sound; reject-all is not complete) | same | same | same |
| 5 | CR / ROM assumptions → Lean definitions | **N/A** (deterministic branch, no assumption) | **N/A** if deterministic | **TRUSTED** (TCB#6) if used. Caveat: the Lean `Sha256CollisionResistant` / `RomSound` take arbitrary `num/den`; the birthday / q_H bounds in `security/assumptions/*.json` are not in Lean | same as SP1 |
| 6 | production verifier ↔ formal verifier (`FORMAL_IMPL_CONNECTION`) | **TRUSTED** (TCB#9: Lean compiler `lean -c`/`leanc`, Lean runtime, C toolchain). The statement quantifies over the binary digest; the evidence graph marks `implements` as `trusted`. The gate reports PASS: it is a policy-accepted trusted edge, not a proof. | Statement about the exact bytecode: **CHECKED** (design; the only certificate on main is the non-NEAR `Toy`). `npai-verify` ↔ `interpVerify`: **TESTED**, 200,001 cases re-run + 1,000,000 reported + 45 vectors, 0 disagreements; fuzz targets `decode`/`exec`. Not CHECKED (TCB#8). IR→NPAI compiler: **CHECKED** (`examples/npai-ir`, `NpaiIR.exec_placed`). NEAR verifier ↔ `check`: **MISSING** (in progress). | **MISSING**: verifier ↔ Lean / FRI / Fiat–Shamir soundness has no checked route (see `docs/research/formal-ecosystem.md`) | **MISSING** (same) |
| 6a | claim/proof parser inside the verifier | Inside the Lean model, so it inherits #6 (**TRUSTED** compile) and #4 (**CHECKED** semantics) | inside the bytecode (#6) | **MISSING** | **MISSING** |
| 6b | approved params / public dir → statement | **CHECKED** (digest): the statement binds `sha256 pub = publicDigest`. Manual run used `public.bin` = `oracle/fixtures/public/params.bin` (`sha256:38c230e8…`). In the pipeline, who supplies `--public-digest` from the judge-run `prepare` is **MISSING** (no worker runs FORMAL_CHECK). | same design | **MISSING** | **MISSING** |
| 7 | built artifact = certified artifact (`ARTIFACT_BINDING`) | **CHECKED (digest)**, re-run: the candidate `out/verify` equals the judge's native-lean build `3931ac6f…`; `BUILD_REPRODUCIBLE` holds (re-run rebuild matched) | design: the image digest is spliced into the statement | **MISSING** | **MISSING** |
| 8 | executed artifact = certified artifact | **MISSING**: `runners/worker` runs `entry.verify` and does not check that its digest equals the judge-built verifier, and never runs the judge-built binary (`runners/worker/src/stages/common.rs`). For RW the bytes happen to be identical. | **MISSING**: the worker has no `npai-verify` path | **MISSING** | **MISSING** |
| 9 | oracle → expected claims in conformance | **TESTED, re-run** (manual): 20/20 public fixtures byte-identical. **Reported**: +600 generated in-domain, 140 out-of-domain + 14 rejection fixtures refused. Pipeline: **MISSING** (the server's `ConformanceJob` carries no oracle cases) | **MISSING** | **MISSING** | **MISSING** |
| 10 | sandbox isolation of executed code | **TESTED**: bwrap-dev 20 tests (`runners/sandbox/tests/bwrap.rs`, in `make test-rust`; demo only). Firecracker 19 VM tests + 2 worker tests, **gated** (`ARENA_FC_TESTS=1`), not in CI. **TRUSTED** (TCB#10). | same | same (GPU route: **MISSING**) | same |
| 11 | measurement → score | **TESTED**: `runners/measure` + `benchmarks/arena_bench` share `benchmarks/testvectors/score.json` (8 Rust tests; 42 Python tests re-run, not in CI). **MISSING**: governed hardware profile (only `benchmarks/hardware/dev-host.json`, `governed: false`) and baselines (`baseline_ns: []`), so no score can be computed | same | same | same |

### Every MISSING edge, listed

1. NearSpec scope versus the real chain, for the 23 excluded properties and the on-chain post-state root (#1a).
2. Backend semantics and security theorem for RN, SP1 and P3 (#3, #4); all are in progress.
3. NEAR verifier bytecode ↔ `check` for RN (#6; `lane/npai-near`).
4. Verifier ↔ formal proof-system soundness for SP1 and P3: STARK, FRI and Fiat–Shamir layers (#6).
5. The claim/proof parser for SP1 and P3 (#6a).
6. Pipeline supply of the judge-run `prepare` public digest to the formal check (#6b).
7. ARTIFACT_BINDING for SP1 and P3 (#7).
8. Executed artifact = certified artifact, for every backend: the worker runs `entry.verify`, never the judge-built or interpreted verifier (#8).
9. Oracle cases in pipeline conformance jobs, and held-out cases (#9).
10. Governed hardware profile and baselines (#11).
11. GPU isolation route (#10).
12. Evidence-graph producers for the `nearcore_source`, `test_suite` and `measurement` nodes. Edges #0, #1, #9, #10 and #11 therefore never appear in a signed report (`docs/ARCHITECTURE.md` §2.4).
13. `FORMAL_ZK`: there is no Lean ZK definition (only relevant to `zk-classical-128`).
14. Production governance key, and M-of-N signing (TCB#16).

---

## 2. Obligations (`docs/CONTRACTS.md` §6)

The "implemented in" column names the code that computes the gate. The RW
column says what evidence exists for the reference backend.

| obligation | implemented in | in pipeline today | RW evidence | RN / SP1 / P3 |
|---|---|---|---|---|
| `PKG_WELLFORMED` | `runners/worker/src/stages/validate.rs`, `runners/archive` | real worker not joined to server (ARCHITECTURE §9); fake worker in server tests | **TESTED**: archive 30 tests; hostile `archive-*` and `ui-injection-manifest` packaged (dry run) | MISSING (in progress) |
| `BUILD_REPRODUCIBLE` | `runners/worker/src/stages/build.rs` (two builds, bit-identical) | as above | **TESTED** (re-run rebuild: identical `out/verify`); `runners/worker/tests/pipeline.rs` | MISSING |
| `ARTIFACT_BINDING` | `runners/formal-checker` (`pipeline.rs`, `native.rs`) | **MISSING** (no worker runs FORMAL_CHECK) | **CHECKED (digest)**, manual re-run | MISSING |
| `FORMAL_SEMANTIC_SOUNDNESS` | formal-checker; all `FORMAL_*` gates pass or fail together on "type = expected statement ∧ rechecks accept" (`report.rs`) | **MISSING** | **CHECKED**, manual re-run | MISSING |
| `FORMAL_SEMANTIC_COMPLETENESS` | same | **MISSING** | **CHECKED**, manual re-run | MISSING |
| `FORMAL_CRYPTO_SOUNDNESS` | same; bound evaluated by the kernel (no `native_decide`) | **MISSING** | **CHECKED** (deterministic, ε = 0) | MISSING |
| `FORMAL_IMPL_CONNECTION` | same | **MISSING** | gate PASS; edge **TRUSTED** (TCB#9) | RN: CHECKED statement + TESTED interpreter (design); SP1/P3: MISSING |
| `FORMAL_ZK` | policy only (`tools/arena-admin/src/policy.rs`) | — | **N/A** (`validity_only`; listed in `not_applicable_gates`) | **MISSING** (no Lean definition) |
| `AXIOM_AUDIT` | `runners/formal-checker/src/audit.rs` + `ArenaAudit` | **MISSING** | **CHECKED**, manual re-run: axioms {propext, Classical.choice, Quot.sound} | MISSING |
| `CONFORMANCE_DIFFERENTIAL` | `runners/worker/src/stages/conformance.rs` | **MISSING** (no oracle cases in jobs) | **TESTED**: 20/20 re-run; 600 + 140 + 14 reported | MISSING |
| `ADVERSARIAL_PROOFS` | `runners/worker/src/stages/adversarial.rs` + `adversarial/proof-mutators` | real worker not joined | **TESTED**: 792 mutants, 0 accepted (re-run) | MISSING |
| `PROVER_RELIABILITY` | `conformance.rs`, `benchmark.rs` | real worker not joined | **TESTED**: 20/20 honest proofs accepted (re-run) | MISSING |
| `RESOURCE_LIMITS` | `conformance.rs`, `benchmark.rs`; sandbox limits | real worker not joined | proof-size bound **CHECKED** in the certificate (`maxProofBytes ≥ 3,088,869` ≤ 8 MiB); runtime limits **TESTED** at sandbox level only | MISSING |
| `BENCHMARK` | `runners/worker/src/stages/benchmark.rs`, `runners/measure`; server recomputes score | real worker not joined | **MISSING**: no baseline, no governed host; local timings only (`examples/bench/measure_provers.py`) | MISSING |

---

## 3. Hostile suite (`adversarial/hostile-submissions`, 35 cases, 15 families)

Every case expects `REJECTED`. The "dry run" column is what CI runs today:
`make e2e-hostile` with no `ARENA_SERVER` packages every case and validates
`expect.json`. It does not submit anything. "Component" is evidence that the
responsible component rejects this class of attack in its own tests. "Live"
means the case was submitted through the pipeline.

| family (cases) | expected gate → reason | dry run (CI) | component evidence | live pipeline |
|---|---|---|---|---|
| archive-attack (5) | `PKG_WELLFORMED` → `ARCHIVE_UNSAFE` | packaged | **TESTED**: `runners/archive` 26 tests (zip-slip, symlink, hardlink, device, bomb) | **MISSING** |
| ui-log-injection (2) | `PKG_WELLFORMED` / `ADVERSARIAL_PROOFS` | packaged | manifest regex in `CandidateManifest::validate`; web escaping in `web/tests/security.test.tsx` (part of 47 vitest tests, `make web`) | **MISSING** |
| build-integrity (3) | `BUILD_REPRODUCIBLE` / `ARTIFACT_BINDING` | packaged | **TESTED**: `runners/worker/tests/pipeline.rs::nonreproducible_and_failing_builds`; no-network enforced by the sandbox (`network_is_denied`) | **MISSING** |
| artifact-binding (4, incl. `near-reexec-malicious-executable`) | `ARTIFACT_BINDING` → `ARTIFACT_BINDING_FAILED` | packaged | **TESTED**: `tests/native_route.rs` (candidate-native, shadow, macro hijack rejected; re-run) | **MISSING** |
| axiom-audit (4) | `AXIOM_AUDIT` → `SORRY_FOUND` / `FORBIDDEN_AXIOM` / `NATIVE_EVAL_FOUND` / `SHADOWED_DEFINITION` | packaged | **TESTED**: checker corpus 30 cases (26 negative) + `formal-core/negative` 11 attacks (re-run) | **MISSING** |
| theorem-type-mismatch (3, incl. `near-reexec-skip-refund`) | `FORMAL_SEMANTIC_SOUNDNESS` → `THEOREM_TYPE_MISMATCH` | packaged | **TESTED**: `05_false_premise_proved`, `07_wrong_theorem_type`, `08_wrong_params`, `11_wrong_route_native` (re-run) | **MISSING** |
| formal-missing (1) | `CERTIFICATE_MISSING` | packaged | **TESTED**: `09_stale_digest` → `CERTIFICATE_MISSING` | **MISSING** |
| crypto-soundness (1) | `SECURITY_BOUND_INSUFFICIENT` | packaged | statement-level only (wrong params → type mismatch); no case exercises a too-weak but well-typed bound | **MISSING** |
| forged-output (1) | `CERTIFICATE_MISSING` | packaged | checker ignores candidate stdout/files (staging takes only `.lean`) | **MISSING** |
| verifier-soundness (1) | `ADVERSARIAL_PROOFS` → `HOSTILE_PROOF_ACCEPTED` | packaged | **TESTED**: `runners/worker/tests/pipeline.rs::lenient_verifier_fails_adversarial`, `proof-mutators` 7 tests | **MISSING** |
| public-input-binding (1) | `ADVERSARIAL_PROOFS` / `CLAIM_MISMATCH` | packaged | binding mutators (`mismatched-context`, `recursive-substitution`) | **MISSING** |
| prover-reliability (1) | `PROVER_RELIABILITY` → `PROVER_FAILED` | packaged | **TESTED**: `pipeline.rs::verifier_rejecting_honest_proof_and_prover_timeout` | **MISSING** |
| async-cheat (1) | `PROVER_FAILED` | packaged | **TESTED**: `background_processes_do_not_outlive_entry` (bwrap) + VM test (gated) | **MISSING** |
| sandbox-escape (4) | `SANDBOX_VIOLATION` / `RESOURCE_LIMIT` | packaged | **TESTED**: bwrap 20 tests (network denied, host FS hidden, fork bomb, ...); Firecracker 19 VM tests, gated, not CI | **MISSING** |
| benchmark-cheat (3) | `CLAIM_MISMATCH` / `SANDBOX_VIOLATION` | packaged | `caching_tripwire` (`runners/measure/src/stats.rs`); held-out cases not wired | **MISSING** |

Live hostile e2e is blocked by the worker↔server integration gaps
(`docs/ARCHITECTURE.md` §9) and is **in progress** (integration e2e lane).
Independent attack review: **in progress `lane/red-team`**.

---

## 4. Unresolved formal links

1. nearcore → NearSpec is **tested, not proved**. There is no extraction of
   nearcore (no Aeneas/hax path on main), and the difftest uses synthetic
   state.
2. NearSpec covers single-Transfer receipts on PV86 only, with 23 excluded
   properties. The post-state root is a projection.
3. On native-lean, the Lean compiler, runtime and C toolchain are trusted
   (TCB#9).
4. `npai-verify` ↔ `ArenaCore.Interp.interpVerify` is tested
   (1,200,001 + 45), not checked. Closing it needs extraction plus an
   equivalence proof (TCB#8).
5. No NEAR verifier exists as NPAI bytecode yet: `interpVerify code … ↔ check`
   is missing (`examples/npai-ir/README.md`). In progress on `lane/npai-near`.
6. STARK, FRI and Fiat–Shamir soundness for SP1 and Plonky3: no checked
   artifact exists in the ecosystem (`docs/research/formal-ecosystem.md`). In
   progress on `lane/backend-zkvm` and `lane/backend-plonky3`.
7. The CR and ROM assumption bounds in the JSON (birthday, q_H) are not
   expressed in the Lean definitions, which take arbitrary `num/den`.
8. `FORMAL_ZK` has no Lean definition.
9. The four `FORMAL_*` gates are one combined check. A per-obligation result
   only scopes findings; it is not an independent proof.
10. `toolchain_policy.checker_image` is pinned by digest, but the image is not
    reproducibly built or published with an SBOM (TCB#1, TCB#2).

## 5. Unavailable datasets

| dataset | status |
|---|---|
| Real mainnet / historical chunks for the NEAR slice | not in repo; **in progress `lane/historical`** |
| nearcore build for re-running the 1712-case difftest | external (`oracle/vendor/nearcore` → pinned checkout at `/data/illia/nearproof-deps/nearcore`); not in CI |
| Held-out conformance cases | only the commitment is in the repo (`spec/challenge-inputs/heldout-commitment.json`); the seed is off-repo; nothing loads them |
| Baseline timings (`scoring.baseline_ns`) | empty in both signed challenges |
| Governed hardware profile | none (`benchmarks/hardware/dev-host.json` is `governed: false`) |
| NPAI 1,000,000-case difftest report | numbers only in `runners/npai/README.md`; no committed artifact (the 200,001-case run was re-run here) |
| RW "600 generated + 140 OOD" conformance run | numbers only in `examples/reexec-witness/README.md` |
| Firecracker / KVM CI runner | none; VM tests are gated on `ARENA_FC_TESTS=1` and host assets |
