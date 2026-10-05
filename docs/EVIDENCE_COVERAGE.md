# Evidence coverage

This document lists, for every link between pinned nearcore and the exact
artifacts the arena executes, what kind of evidence supports that link. It
covers `main` as of 2026-10-03 (v1 close-out). It covers both the evidence the
**pipeline** produces (`arena-server` with leased jobs and Firecracker workers)
and the evidence produced by components run on their own.

## Status vocabulary

| status | meaning |
|---|---|
| **CHECKED** | Proved, and the proof accepted by a kernel: the Lean kernel through `leanchecker`, plus `nanoda`, plus `lean4lean`. A digest-equality check counts only where the entry says "(digest)". |
| **TRUSTED** | Assumed correct. The entry names the TCB row in `docs/TCB.md` (`TCB#n`). |
| **TESTED** | Differential, fuzz, or fixture testing, with the case count. |
| **MISSING** | No evidence on `main`. |
| **N/A** | Not applicable to this backend or profile. |

"Pipeline" means the arena produces the evidence itself: a submission goes
through `arena-server`, every stage runs on a Firecracker worker at formal
tier, and the result ends up in a signed report. "Manual" means a component was
run directly, outside the pipeline.

Backends (columns):

* **RW**: `examples/reexec-witness`, with its prover-only child
  `reexec-witness-fast`. Route `native-lean`. **Admitted at formal tier** in
  the pipeline: `docs/e2e-results/milestone-d-v1-2/`, plus the live instance
  (`docs/LIVE.md`).
* **RN**: `examples/reexec-npai`. Route `npai-v1`: the NEAR verifier is NPAI
  bytecode, run by the judge's interpreter. **Admitted at formal tier** in the
  pipeline: `docs/e2e-results/reexec-npai/`, plus the live instance.
* **SP1**: `examples/zkvm-sp1` (zkVM). It is **measured on the experimental
  tier only** and has no certificate.
* **P3**: `examples/stark-plonky3` (STARK). It is **measured on the
  experimental tier only** and has no certificate.

**Experimental tier.** On an experimental challenge, `ARTIFACT_BINDING`,
`FORMAL_*` and `AXIOM_AUDIT` are diagnostic: they are evaluated and reported,
but they never block a run, never feed the decision, and an experimental entry
is never ranked. Formal and demo tiers are unchanged. See
`docs/e2e-results/sp1-pipeline.md` for this policy.

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

| # | edge | RW (native-lean) | RN (npai-v1) | SP1 | P3 |
|---|---|---|---|---|---|
| 0 | nearcore pin → challenge | **TRUSTED** (TCB#11, TCB#16). The signed challenge pins `nearcore.commit = 44f7ae6c…` (2.13.4), protocol version 86 and the `runtime_config_digest`. Formal challenges are signed with the local operator key. | same | same | same |
| 1 | nearcore → NearSpec | **TESTED**: 3-way difftest, 1712 synthetic cases, 0 disagreements (`spec/difftest-report.json`). Also **4 authentic mainnet fixtures** (`oracle/fixtures/historical/`, class `historical-rebased-prestate`; `docs/HISTORICAL_REPLAY.md`), whose claims come from pinned `Runtime::apply` on real mainnet trie nodes and are confirmed by the Lean checker. This edge is **not CHECKED**: faithfulness is tested, not proved. | same (shared) | same | same |
| 1a | NearSpec scope vs real chain | **MISSING** for the 23 `semantic_scope.excludes`. The post root is a slice projection. Historical fixtures are rebased (pre-state = state-sync root), so they are not the chain's own transition. | same | same | same |
| 2 | NearSpec ↔ claim bytes | **CHECKED**: `decodeClaim_encode`, `Claim.encode_injective`, `WfClaim.decode_encode`. Prose spec ↔ Lean codec is **TRUSTED** (TCB#5). | same | same | same |
| 3 | NearSpec → backend semantics | **CHECKED, pipeline**: `FORMAL_SEMANTIC_SOUNDNESS` / `_COMPLETENESS` PASS (three kernels) | **CHECKED, pipeline** (`ReexecNpai.certificate`) | Only vacuous `B := Rel` lemmas. No certificate: **CERTIFICATE_MISSING** (diagnostic) | same as SP1 |
| 4 | backend → security theorem | **CHECKED, pipeline**: deterministic soundness, ε = 0, no assumption | **CHECKED, pipeline** (deterministic) | **MISSING** | **MISSING** |
| 4a | `AdmissionStatement` means what we intend | **TRUSTED** (TCB#4). Partly **CHECKED** by the anti-vacuity lemmas (`formal-core/ArenaCore/Sanity.lean`) | same | same | same |
| 5 | CR / ROM assumptions → Lean | **N/A** (deterministic) | **N/A** | **TRUSTED** (TCB#6) if used. The bounds in `security/assumptions/*.json` are not expressed in Lean. | same. Design only: `docs/zk-formal/DESIGN.md` + `zk-formal/` (ROM potential, bad-query and line-lemma PoCs, parameter budget checked with `decide +kernel`) |
| 6 | production verifier ↔ formal verifier (`FORMAL_IMPL_CONNECTION`) | **TRUSTED** (TCB#9: Lean compiler, runtime, C toolchain). The evidence edge `implements` is `trusted`. | **CHECKED, pipeline**: the statement is about the exact bytecode; the evidence edge `artifact:verifier_bytecode -implements-> statement` is **checked**. Remaining link `npai-verify` ↔ `interpVerify`: **TESTED** (200,001 + 1,000,000 cases + 45 vectors, 0 disagreements), shadowed per job by `arena-interp-ref`, but not CHECKED (TCB#8). | **MISSING**: no checked route for STARK/FRI/Fiat–Shamir soundness | **MISSING** (design only, see #5) |
| 6a | claim/proof parser inside the verifier | inside the Lean model: inherits #6 / #4 | inside the bytecode: **CHECKED** with #6 | **MISSING** | **MISSING** |
| 6b | approved params / public dir → statement | **CHECKED (digest), pipeline**: the statement pins `sha256(public.bin)` from the judge-run `prepare` | same | diagnostic only | diagnostic only |
| 7 | built artifact = certified artifact (`ARTIFACT_BINDING`) | **CHECKED (digest), pipeline**: the shipped `out/verify` must equal the judge's native-lean build of the certified model | **CHECKED (digest), pipeline**: bytecode digest is in the statement | **FAIL** (diagnostic): candidate-built native verifier, no binding route | same |
| 8 | executed artifact = certified artifact | **CHECKED (digest), pipeline**: conformance, adversarial and benchmark jobs run the judge-built native verifier | **CHECKED (digest), pipeline**: judge `npai-verify --expect-digest` on the judge-built bytecode | **MISSING** (runs its own `verify`) | **MISSING** |
| 9 | oracle → expected claims (conformance) | **TESTED, pipeline**: per run, 20 public fixtures + 3 judge-sampled cases, byte-identical claims; the adversarial stage adds 146–152 hostile proofs, 0 accepted | same | **TESTED, pipeline** (experimental): conformance and adversarial PASS | same |
| 10 | sandbox isolation | **TESTED**: every pipeline stage runs in Firecracker microVMs (no network device, read-only images, per-job VM). **Seccomp user-notification** escape detection reports `SANDBOX_VIOLATION` (`docs/e2e-results/hostile-seccomp/`). VM tests are gated (`ARENA_FC_TESTS=1`), not in CI. **TRUSTED** (TCB#10). | same | same (GPU route **MISSING**) | same |
| 11 | measurement → score | **TESTED, pipeline**: server-recomputed score against a pinned baseline. The live head v1-3 pins a baseline measured on the live benchmark worker's CPUs (`benchmarks/results/baseline-near-transfer-receipt-v1-2-live-w1-cpus24-31-20261003/`). **MISSING**: governed hardware. All numbers are dev-host, on a shared, non-isolated machine. | same | measured, never scored (experimental) | same |

### Every MISSING edge, listed

1. NearSpec scope versus the real chain: the 23 excluded properties, the on-chain post-state root, and an exact (non-rebased) historical replay (#1a).
2. Formal certificates for SP1 and P3 (#3, #4), and verifier ↔ proof-system soundness for STARK/FRI/Fiat–Shamir (#6). For P3-style backends there is a design only (`docs/zk-formal/DESIGN.md`).
3. ARTIFACT_BINDING and executed-artifact binding for SP1 and P3 (#7, #8).
4. `npai-verify` ↔ `interpVerify` as a proof rather than a test (TCB#8), and the Lean compiler for native-lean (TCB#9).
5. Governed hardware profile and benchmark host (#11).
6. GPU isolation route (#10).
7. Evidence-graph producers for `nearcore_source`, `test_suite` and `measurement` nodes. Edges #0, #1, #9, #10 and #11 therefore do not appear in signed reports.
8. Held-out conformance set: only its commitment is in the repo, and the pipeline samples fresh generator cases instead.
9. `FORMAL_ZK` Lean definition (only relevant to `zk-classical-128`).
10. Production governance key and M-of-N signing (TCB#16). The live instance runs in `dev` mode with the local operator key.

---

## 2. Obligations (`docs/CONTRACTS.md` §6)

| obligation | implemented in | pipeline today | RW / RN evidence | SP1 / P3 (experimental) |
|---|---|---|---|---|
| `PKG_WELLFORMED` | `runners/worker/src/stages/validate.rs`, `runners/archive` | yes | PASS; hostile `archive-*` and `ui-injection-manifest` rejected live | PASS |
| `BUILD_REPRODUCIBLE` | `stages/build.rs` (two bit-identical builds in the toolchain image) | yes | PASS | PASS |
| `ARTIFACT_BINDING` | `runners/formal-checker` + worker binding | yes | **CHECKED (digest)** | FAIL (diagnostic) |
| `FORMAL_SEMANTIC_SOUNDNESS` / `_COMPLETENESS` / `FORMAL_CRYPTO_SOUNDNESS` | formal-checker; the gates pass or fail together | yes (FORMAL_CHECK jobs in the lean-checker image) | **CHECKED** | FAIL `CERTIFICATE_MISSING` (diagnostic) |
| `FORMAL_IMPL_CONNECTION` | same | yes | RW: edge **TRUSTED** (TCB#9). RN: edge **CHECKED** | FAIL (diagnostic) |
| `FORMAL_ZK` | policy only | — | **N/A** (`validity_only`) | **N/A** |
| `AXIOM_AUDIT` | `formal-checker/src/audit.rs` + `ArenaAudit` | yes | **CHECKED**: {propext, Classical.choice, Quot.sound} | FAIL (diagnostic) |
| `CONFORMANCE_DIFFERENTIAL` | `stages/conformance.rs` + `near-arena-oracle` | yes | **TESTED**: 23/23 per run | PASS |
| `ADVERSARIAL_PROOFS` | `stages/adversarial.rs` + `proof-mutators` | yes | **TESTED**: 146–152 hostile inputs per run, 0 accepted | PASS |
| `PROVER_RELIABILITY` | conformance / benchmark | yes | PASS 23/23 | PASS |
| `RESOURCE_LIMITS` | conformance / benchmark + VM limits | yes | PASS | PASS |
| `BENCHMARK` | `stages/benchmark.rs` (`vm_per_batch`), server recompute | yes | scored against the pinned dev-host baseline | measured, never scored |

---

## 3. Hostile suite (`adversarial/hostile-submissions`, 35 cases)

All 35 cases have run live through the pipeline, and every one is REJECTED.
None was admitted, accepted or ranked.

| run | cases | result | evidence |
|---|---|---|---|
| demo challenge, bwrap-dev worker | 22 demo-targeted | 22/22 match `expect.json` | `docs/e2e-results/hostile-final/` |
| same, with seccomp detection | 22 | 22/22. `sandbox-escape-network`, `sandbox-ptrace-proc` and `forged-timing` now fail with **SANDBOX_VIOLATION** | `docs/e2e-results/hostile-seccomp/` |
| signed formal NEAR challenge, Firecracker, formal tier | 13 NEAR-formal-targeted | 13/13 match (axioms, `sorry`, `native_decide`, shadowing, type mismatch, stale/missing certificate, wrong VK, malicious executable, …) | `docs/e2e-results/hostile-near-formal/` |
| live instance | `near-reexec-skip-refund`, `near-reexec-malicious-executable` | REJECTED | `docs/LIVE.md` |

Known gap: `sandbox-escape-filesystem` (file opens only) is contained but not
detectable as a violation, so it fails with `PROVER_FAILED`. Its `notes` field
explains why.

---

## 4. Unresolved formal links

1. nearcore → NearSpec is tested, not proved. The historical fixtures are
   authentic but rebased.
2. NearSpec covers single-Transfer receipts on PV86 only, with 23 excluded
   properties.
3. native-lean trusts the Lean compiler, runtime and C toolchain (TCB#9).
   Choose `npai-v1` to avoid trusting them.
4. `npai-verify` ↔ `interpVerify` is tested, not checked (TCB#8).
5. STARK/FRI/Fiat–Shamir soundness for SP1 and P3: no checked artifact
   exists. There is a design plus PoC lemmas only (`docs/zk-formal/DESIGN.md`).
6. The CR/ROM bounds in the JSON are not in the Lean definitions.
7. `FORMAL_ZK` has no Lean definition.
8. The four `FORMAL_*` gates are one combined check.
9. The checker image is pinned by digest but not reproducibly built or
   published with an SBOM (TCB#1, TCB#2).

## 5. Datasets

| dataset | status |
|---|---|
| Mainnet replay fixtures | 4 rebased-prestate cases in `oracle/fixtures/historical/` (`docs/HISTORICAL_REPLAY.md`). An exact replay is not achievable with public data in the current epoch |
| nearcore build for the 1712-case difftest | external (`/data/illia/nearproof-deps/nearcore`); not in CI |
| Held-out conformance cases | commitment only; the seed is off-repo |
| Baselines | pinned in the signed v1-2 and v1-3 (dev host, `benchmarks/results/`) |
| Governed hardware profile | none (`benchmarks/hardware/dev-host.json`, `governed: false`) |
| Firecracker / KVM CI runner | none; VM tests are gated |
