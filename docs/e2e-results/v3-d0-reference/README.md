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
| public fixtures | `oracle/fixtures/v3/arena-public` `sha256:45eb0203…`: 78 positives (64 honest D0 chunks + 14 nearcore-accepted mutants), 121 rejection cases (59 honest out-of-D0 chunks, 62 nearcore-rejected mutants), `params.bin` |
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

## Live run 1 (2026-10-06): REJECTED — proof malleability

Install from main `241dc41` (release binaries from main; `near-arena-oracle-v3` built from
source byte-identical to main's `oracle/v3`, because the main-checkout rebuild was starved by a
40 GB job of another lane in `zkbuild.slice`), `freeze-trusted 9f20f82` (`trusted-trees/89903b98…`),
challenge `chl_640ed008…` loaded and verified at server start. Worker log: v3 oracle, fixtures
`sha256:45eb0203…`, held-out set `sha256:edac8e6f…`.

`sub_7c6a67b0c3684852a8f755072744489a` (agent `reference`, package `sha256:d10dde14…`):

* PKG_WELLFORMED, BUILD_REPRODUCIBLE PASS;
* **all 6 formal gates PASS on the real judge** (Firecracker, lean-checker image, checker
  `66b014d4…`, frozen tree `89903b98…`);
* **ADVERSARIAL_PROOFS FAIL** (`HOSTILE_PROOF_ACCEPTED`): `bitflip/379.3` — 154/155 hostile
  inputs rejected, one accepted; CONFORMANCE was cancelled by the server after the failure.
  Decision REJECTED; status and signed report: `live-run1-status.json`, `live-run1-report.json`.

**Cause (a property of the statement, not a judge bug).** The proof is the raw witness, and
nearcore's validator — hence `RelD0`, faithfully — does not read three witness fields
(spec §10 finding 1): the chunk header's `height_included`, its signature, and every
`ChunkStateTransition.block_hash`. Flipping any bit there yields another valid witness of the same
true claim, so `verify` accepts it. Exhaustive single-bit map of fixture `00-h10004-s3`
(1 565 B): accepted offsets 365–372 (`height_included`) and 374–469 (signature + main transition
`block_hash`), nothing else. Soundness is unaffected (acceptance ⇒ `RelD0`, a true claim), but the
arena contract requires hostile proof *bytes* to be rejected (CONTRACTS: `ADVERSARIAL_PROOFS`), i.e.
a non-malleable proof encoding. The bwrap pipeline run passed only because its public-seed bitflip
positions missed these ~100 bytes.

**Fix (lead decision: option A, canonical proof encoding; adversarial semantics unchanged).**

* `examples/reexec-v3-d0` now proves with the **canonical witness**: `height_included` = 0, the
  ED25519 all-zero signature, every transition `block_hash` = 0; the verifier accepts only
  canonical bytes (`CanonDefs.lean`, `canonicalW`). Certificate: `relD0_canonical : RelD0 cb w →
  ∃ w', RelD0 cb w' ∧ canonicalW w' ∧ |w'| ≤ |w|`, proved in the candidate's `formal/` (the
  frozen trusted tree is untouched; no encoder was committed anywhere, so none is used): every
  trusted witness parser is context-free (`CF.lean`), the spliced canonical bytes re-parse to the
  same witness with zeroed block hashes (`Canon.lean`), and `checkD0` never reads a transition
  block hash (`Norm.lean`). Axioms: propext, Classical.choice, Quot.sound. Exhaustive single-bit
  flips of two canonical proofs (1 565 B, 5 214 B with an implicit transition): 0 accepted.
* Judge: a structure-aware generic mutator `v3-ignored-fields` (runners/worker/src/mutators.rs)
  flips one bit of each validator-ignored field of every `near-arena-witness-v3` proof, and the
  permanent hostile case `adversarial/hostile-submissions/near-v3-malleable-witness` (the
  pre-canonical reference) must be REJECTED with `HOSTILE_PROOF_ACCEPTED`; in the bwrap pipeline
  all four `v3-ignored-fields` mutants (height_included, signature, main and implicit block_hash)
  are accepted by it, the canonical reference rejects all 164 hostile inputs. Note filed in
  adversarial/README.md: random bit flips must be complemented by structure-aware mutations of
  known validator-ignored fields.
* Successor challenge **`chl_4b4316516128000f129cff9b3ced8b51` `near-chunk-validation-d0-1`**
  (supersedes `chl_640ed008…`): identical statement, trusted tree, workloads, fixtures, held-out
  set and checker; the baseline is re-measured from the canonical reference (package
  `sha256:63618259…`, measurement draft `chl_902d8b89…`, CPUs 0-7 with live `w1` stopped for the
  window 04:05–04:09 UTC, secret sampling, calibration OK drift 2 930 ppm, no flags; medians
  d0-quiet 6 996 987, d0-transfers 6 957 356, d0-missing 7 133 640 ns). An earlier attempt
  (03:52–04:03) failed calibration (drift 34 359 ppm, one 1.57 s pre-calibration outlier) and is
  kept as `benchmarks/results/…-attempt1-calibration-drift/`.

## Live run 2 (2026-10-06): ADMITTED

Install from main `84fa676` (judge with `v3-ignored-fields`; `near-arena-oracle-v3` unchanged,
its source is the pinned `oracle/v3`), successor `chl_4b4316516128000f129cff9b3ced8b51`
`near-chunk-validation-d0-1` registered (signature, policy and trusted tree `89903b98…` checked);
`chl_640ed008…` is closed, superseded.

**Reference `sub_9b0c50fcdf80450da79cced76b4f7aea`** (agent `reference`, package
`sha256:bc2e9428…`): **ADMITTED at formal tier, score 102.144 ± 3.214**, all 14 gates PASS.
Signed report `live-run2-reference-report.json` (ed25519, report key in docs/LIVE.md), status
`live-run2-reference-status.json`.

* all 6 formal gates PASS on the real judge (Firecracker, lean-checker image, checker
  `66b014d4…`, frozen tree `89903b98…`);
* CONFORMANCE: "84/84 cases conform (78 public fixtures, 3 judge-sampled, 3 held-out);
  judge-secret HMAC sampling …; held-out set sha256:edac8e6f… verified against the commitment and
  used (3 case(s); ids withheld); 127 rejection case(s) (121 public, 3 judge-sampled, 3 held-out;
  nearcore rejects or out of domain): 53 refused by prove, 74 proofs rejected by verify, 0 accepted";
* ADVERSARIAL: 165 hostile inputs (incl. `v3-ignored-fields`), 165 rejected;
* RESOURCE_LIMITS: max proof 118 295 B, max verify 599 ms, peak 432 MiB;
* BENCHMARK (CPUs 0-7, secret sampling): prove medians per 8-chunk batch d0-quiet 6.635 ms
  (baseline 6.997), d0-transfers 6.860 (6.957), d0-missing 7.050 (7.134); verify medians
  23.3 / 36.4 / 31.1 ms.

**Hostile `sub_23822a4bea894cc8bb781f208af7f830`** (agent `agent-1`, case
`near-v3-malleable-witness`, the pre-canonical reference): **REJECTED**, reasons
`HOSTILE_PROOF_ACCEPTED`, `OBLIGATION_UNDISCHARGED`. All formal gates PASS (its certificate is
genuine); ADVERSARIAL_PROOFS FAIL: "verify accepted hostile proofs:
v3-ignored-fields/block_hash.implicit0, v3-ignored-fields/block_hash.main,
v3-ignored-fields/height_included, v3-ignored-fields/signature" — every structure-aware mutant,
none of the random ones, i.e. deterministic. Report `live-hostile-malleable-report.json`.

## Live run 3 (2026-10-06): full normal form, ADMITTED; lenient hostile REJECTED

Install from main `b61b79f` (judge with `v3-witness-freedoms`). First install used stale
binaries from `~/.cache/nearproof-live-target` (built at `84fa676`, no new mutator): those first
runs (reference ADMITTED 4.430, hostile ADMITTED 95.774) are invalid; rebuilt into the live target
dir, re-installed, `rerun-submission` of both (docs/LIVE.md §5e).

**Reference `sub_0826bb9b8d1c46c0b0bc4b5e1a0df3de`** (agent `reference`, package
`sha256:9d8b9f71…`), run `run_9cfcf7bdfa7949abb7087b5babc77865`: **ADMITTED at formal tier, score
4.504 ± 0.370**, all 14 gates PASS. Signed report `live-run3-normal-reference-report.json`,
status `live-run3-normal-reference-status.json`.

* 6 formal gates PASS (judge-built verify = `build.sh` output, model closure CanonDefs, NormDefs,
  KeysD0, NormalDefs, NormBytesDefs, Model);
* CONFORMANCE: 84/84 conform (78 public, 3 judge-sampled, 3 held-out); 127 rejection cases: 87
  refused by prove, 40 rejected by verify, 0 accepted;
* ADVERSARIAL: 183 hostile inputs (incl. `v3-ignored-fields`, `v3-witness-freedoms`), 183 rejected;
* RESOURCE_LIMITS: max proof 118 295 B, max verify 1 459 ms, peak 445 MiB;
* BENCHMARK (CPUs 0-7, secret sampling): prove medians per 8-chunk batch d0-quiet 124.2 ms
  (baseline 7.0), d0-transfers 148.6 (7.0), d0-missing 196.3 (7.1); verify 59.4 / 65.6 / 83.4 ms.
  The Lean prover runs `keysD0` (the claim-segment walk up to the main trie build) + `normSW`.

**Hostile `sub_f9644f35093d44038518293b0d4f8675`** (agent `agent-1`, case
`near-v3-lenient-witness`, the canonical-only reference of run 2), run
`run_99a3f62247d048098e11f361251818b5`: **REJECTED**, reasons `HOSTILE_PROOF_ACCEPTED`,
`OBLIGATION_UNDISCHARGED`. Formal gates PASS; ADVERSARIAL_PROOFS FAIL: 18 of 183 accepted, all
`v3-witness-freedoms/entries…` and `v3-witness-freedoms/values…` (deterministic). Report
`live-hostile-lenient-report.json`.

**Re-judged `sub_9b0c50fcdf80450da79cced76b4f7aea`** (run 2's canonical-only reference, ADMITTED
at 102.144 before `v3-witness-freedoms` existed): `rerun-submission` on the current judge, run
`run_c8661f22951f415d962e0ad2e1338a40`: **REJECTED** (HOSTILE_PROOF_ACCEPTED,
`v3-witness-freedoms/entries…` and `…/values…`), the judge's own verdict, same as the hostile case.
Report `live-run2-reference-rerun-report.json`; the run-1 report above stays as history.

## Live run 4 (2026-10-06): fast PROVER_ONLY child, ADMITTED 104.566

**`sub_2b51fbdeb20c4ff0b5932607c8e8e7da`** (`examples/reexec-v3-d0-fast` from main `38329cf`,
package `sha256:d065d3cb…`, `--parent sub_0826bb9b…`), run `run_d034b34f43734081879682df72e87bd2`:
**ADMITTED, score 104.566 ± 3.033**, `change_class=PROVER_ONLY`, all 6 formal gates reused from
the parent. CONFORMANCE 84/84 + 127 rejection cases (61 refused by prove, 66 rejected by verify,
0 accepted); ADVERSARIAL 183/183 rejected (incl. `v3-witness-freedoms`); RESOURCE_LIMITS max proof
118 295 B, max verify 892 ms; BENCHMARK prove medians d0-quiet 6.616 ms, d0-transfers 6.622,
d0-missing 6.929 (baseline 6.997 / 6.957 / 7.134). The native normaliser's proofs are byte-identical
to the parent's Lean prover on all 78 public positives (gate test). Report
`live-run4-fast-child-report.json`, status `live-run4-fast-child-status.json`.
