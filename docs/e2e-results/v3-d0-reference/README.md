# v3 D0 reference (`examples/reexec-v3-d0`) on `near-chunk-validation-d0`

Challenge **`chl_640ed008467448706236fc727f759ecc`** `near-chunk-validation-d0`
(formal tier, signed with the local operator key `challenges/governance-local.pub`):
statement `near/pv86/chunk-validation/v0`, domain D0, relation `NearSpecV3.RelD0`
(`spec/near-chunk-validation-v0.md`, `spec/claim-v3.md`).

## What the challenge pins

| field | value |
|---|---|
| trusted tree (`formal_spec.tree_digest`) | `sha256:89903b98…` = `formal-core` + `spec/lean` at `9f20f82` (adds `spec/lean/judge/ExpectedV3D0*.template`; `spec/lean/v3` = NearSpecV3 as merged from lane/spec-v3) |
| `allowed_packages` | ArenaCore, NearSpec, NearSpecV3 @ `9f20f82` |
| checker identity | `sha256:66b014d4…` (unchanged lean-checker image `463fdcf4…`) |
| formal config | `runners/formal-checker/challenges/near-chunk-validation-d0.json` (trusted: ArenaCore, 11 NearSpec modules, 15 NearSpecV3 modules; no `Examples`) |
| claim encoding | `near-arena-claim-v3`; request = claim (the judge hands the claim to prove), params `near-arena-params-v3` with domain `D0` |
| `chain_id` | `arena-v3-local`: the chain the oracle's claims are about. nearcore asserts the real mainnet genesis hash when `chain_id = "mainnet"`, so a TestEnv chain cannot carry it; D0 never reads `chain_id` (T3); runtime parameters are mainnet's (`runtime_config_digest`) |
| public fixtures | `oracle/fixtures/v3/arena-public` `sha256:349fe0df…`: 78 positives (64 honest D0 chunks + 14 nearcore-accepted mutants), 121 rejection cases (59 honest out-of-D0 chunks, 62 nearcore-rejected mutants), `params.bin` |
| workload classes (batch 8) | `d0-quiet` 20 % (no incoming receipt, no implicit transition), `d0-transfers` 50 % (≥ 1 incoming cross-shard Transfer receipt), `d0-missing` 30 % (≥ 1 implicit transition; chains with 25 % chunk skips). Every class rotates the chain parameter set by the seed (4/5/6 shards × RS (2,8), (33,100), (5,16), (1,3)), ≤ 2 chunks per chain |
| generator digests | `spec/workloads/near-chunk-validation-d0/*.json` (`near-arena-oracle-v3 gen`, oracle source `sha256:4c362214…`… see the specs) |
| held-out commitment | `sha256:edac8e6f…` (`spec/challenge-inputs/heldout-commitment-v3-d0.json`; secret seed off-repo; 72 positives, 64 rejections; regenerated from the seed with the current oracle: identical digest) |
| baseline | reexec-v3-d0 package `sha256:fec6f7c9…` measured on the unsigned measurement draft `chl_35ed44c7…` (`challenges/drafts/near-chunk-validation-d0.measure.json`): Firecracker `firecracker-rc`, CPUs 0-7 (live `w1` stopped for the window 00:34–00:39 UTC 2026-10-06, no BENCHMARK leased), judge-secret HMAC sampling (season commitment `sha256:b860eb74…`), `vm_per_batch`, 3 warm-up + 15 measured. Calibration OK (drift 9 343 ppm), no flags, BENCHMARK PASS. Medians per 8-chunk batch: d0-quiet 6 830 957 ns, d0-transfers 6 959 158 ns, d0-missing 6 998 029 ns (verify medians 21.5 / 26.4 / 56.1 ms per batch). `benchmarks/results/baseline-near-chunk-validation-d0-secret-cpus0-7-20261006/` |
| scoring | speed (§8). `scoring-v2` (`cost_v1`, BENCHMARK_SPEC §14) has landed, but a formal challenge must pin a *governed* price model and only the draft `pm-near-mainnet-2026q4` exists (§14.10 decisions pending); a successor can add `scoring` once it is governed |

## Judge pipeline before going live (milestones 1–3)

* **Oracle ↔ nearcore.** Every case the judge issues is labelled by nearcore's own
  validator (`pre_validate_chunk_state_witness` + `validate_chunk_state_witness`) and the
  independent D0 classifier. Cross-check with the compiled Lean relation
  (`nearspec-v3-check`): arena-public 78/78 positives accepted, 0/121 rejections accepted;
  72 class samples (3 seeds × 3 classes × 8) 72/72; held-out 72/72 and 0/64.
* **Formal checker** (`formal-check-dev.report.json`, dev bwrap sandbox, clean export,
  config `near-chunk-validation-d0.json`): all 6 formal gates PASS; leanchecker, nanoda,
  lean4lean, arena-audit, NDJSON audit accept; judge-built `verify`
  `sha256:02527ce2…` = `build.sh` output.
* **`arena check-local`** on the public fixtures: PKG_WELLFORMED, BUILD_REPRODUCIBLE,
  CONFORMANCE_DIFFERENTIAL, PROVER_RELIABILITY, ADVERSARIAL_PROOFS, RESOURCE_LIMITS PASS
  (`check-local.txt`).
* **Worker pipeline** (`runners/worker/tests/near_v3.rs`, bwrap-dev, `worker-pipeline-bwrap.log`):
  VALIDATE, BUILD, FORMAL_CHECK (6 PASS), CONFORMANCE "84/84 cases conform (78 public
  fixtures, 3 judge-sampled, 3 held-out); … 127 rejection case(s) (121 public, 3
  judge-sampled, 3 held-out; nearcore rejects or out of domain): 0 refused by prove, 127
  proofs rejected by verify, 0 accepted", ADVERSARIAL 155/155 rejected, BENCHMARK PASS.
  The same pipeline with an accept-all verifier fails CONFORMANCE with
  `COUNTEREXAMPLE_FOUND` on the rejection cases.

## Live run

(recorded after the install from main; see docs/LIVE.md §5e)
