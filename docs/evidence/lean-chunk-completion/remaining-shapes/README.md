# Remaining W05–W07 shapes (workplan item 10), 2026-10-29/30

Five shapes were open: curve hosts called from timed-out yield callbacks; the post-NEP-488
`version = 1` BLS path; an ML-DSA-65 `z` exactly at the norm bound; mismatched global-contract
distribution code identities; and a state init followed by a successful emit. Ground truth is
pinned nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV86), run cold. Lean computes;
no nearcore value is a Lean input.

| shape | how closed | nearcore-judged Lean comparisons (seeds) | disagreements | breakage control |
|---|---|---|---|---|
| curve hosts in timed-out yield callbacks | whole-chunk fixtures (`curve-yield-timeout`) | 1,500 (601–604) | 0 | C-Y |
| BLS `version = 1` (NEP-488) | source-backed unreachability at PV86, plus the existing version-0 fixtures | — | — | — |
| ML-DSA `z` at the norm bound | boundary signer + whole-chunk fixtures (`mldsa-bound`) + 40 crate/Lean vectors | 2,150 (1618, 2718, 31415, 6151) | 0 | C-M |
| mismatched distribution code identities | source-backed unreachability, plus identity mutants (`dist-identity`) | 1,027 (811–818) | 0 | C-D1, C-D2 |
| state init then a successful emit | whole-chunk fixtures (`state-init-emit`) | 1,595 (701–704) | 0 | C-S |

**No Lean/nearcore disagreement in 6,272 compared verdict rows, and no Lean change was needed.**
`MlDsa65.lean` and every successor source are unchanged; the only Lean addition is a test executable
(`MlDsaCheck.lean`, not a default target). The verdict tables, the 3,138-case census and the corpus
therefore have no before/after movement to report (the checker binary is byte-identical to the one
built from the base commit, sha256 `a1627ea3…`).

The generator changes are opt-in environment variables. Without them, the generator output is
byte-identical to the base commit's: seed 7, 2 chains, 40 blocks, `--mutate-every 10`, 8,547 files,
`diff -r` empty (`generation.json` `baseline_identity`). `make pin-check` passes; no signed source
changed.

## 1. Curve hosts in timed-out yield callbacks (`NEAR_XFAM_VARIANT=curve-yield-timeout`)

`xfam.rs` `curve_yield_timeout()`, run with `NEAR_SUCCESSOR_SCENARIO=curve-callbacks`. For each
curve-host input that `curve-callbacks` uses (first non-empty `pos`, first `neg`, first `edge`, and
the gas-exhaustion input with its own callback gas, from `curve_hosts::steps()`), `yslot` creates a
yield whose callback is the host method. No step resumes these yields. The runtime's timeout
(`resolve_promise_yield_timeouts`, 200 blocks after creation, `PromiseResult::Failed`) therefore
runs the callback. There are 135 steps per run: input from the yield arguments in memory (`H`) and
in a register (`H_reg`, `value_len = u64::MAX`), and from the failed promise result in memory
(`H_rm`) and in a register (`H_rr`). Every third step is signed from another shard.

nearcore outcomes, identical in all four runs (540 timeout callbacks, executed 201–205 blocks after
creation; `manifests/cy60*.json.gz`):

| callback input | outcomes |
|---|---|
| arguments in memory (40/run) | host returns 0 (19) or 1 (13); AltBn128 input errors (3); `Exceeded the prepaid gas` at the element charge (5) |
| arguments in a register (30/run) | BLS writers: `Integer overflow` at the per-element charge (22); alt_bn128 hosts and pairings return 0/1 or their input errors (8) |
| failed promise result in memory (35/run) | `Accessed invalid register id: 0`: a failed result writes no register, so the host is never reached |
| failed promise result in a register (30/run) | BLS writers: `Integer overflow` (22); others: `Accessed invalid register id: 0` (8) |

So the hosts themselves run in 70 timeout callbacks per run (the argument variants). The
failed-result variants pin what a contract sees when it reads the result of a timed-out yield.

Population per run: every honest chunk with scenario activity and every mutant of one
(`NEAR_XFAM_MUTATE_EVERY=3`): 174–189 honest chunks, 2,927–3,235 mutants. Curve chunks replay
slowly (BLS pairings), so the replay takes every honest chunk and every 16th mutant of the sorted
list: 363–392 cases per run, **1,500 rows, 0 disagreements** (`replay/cy60*-checker.json`).

## 2. BLS `version = 1` (NEP-488) is unreachable at PV86

* The version is selected from `bls12381_not_in_group_fix`
  (`runtime/near-vm-runner/src/logic/bls12381.rs:49-53`, `wasmtime_runner/logic.rs:62`). It is
  `false` in `core/parameters/res/runtime_configs/parameters.yaml:292` (`parameters.snap:289`),
  and only `155.yaml:1` flips it (`{ old: false, new: true }`).
* `RuntimeConfigStore` applies `155.yaml` at protocol version 155 (`config_store.rs:65`). That is
  `NIGHTLY_PROTOCOL_VERSION`; `STABLE_PROTOCOL_VERSION` is 86
  (`core/primitives-core/src/version.rs:628-631`). A PV86 chunk therefore runs `version = 0`.
* The only other setter is `Config::enable_all_features` (`core/parameters/src/vm.rs:274-283`).
  Its callers are the runtime-params estimator (`estimator_context.rs:155`, `gas_metering.rs:140`),
  not chunk application.
* Lean implements `version = 0` only. `bls12381Version := 0` (`BLS12381.lean:583`,
  `Wasm/CryptoHost.lean:164`) is passed to every BLS host. `parseG1` rejects the `(0, ±2)` point
  below version 1 (`BLS12381.lean:451-461`), and so does compressed decoding
  (`g1CompressedNotInGroup`, `:506`).
* Existing whole-chunk coverage of the version-0 corner: `curve-host-fixtures` steps
  `edge.corner_0_2` for `bls12381_p1_sum` and `bls12381_p1_decompress`
  (`oracle/v3-successor/src/curve_hosts.rs:392-449`; README "(0, ±2) point, which is rejected
  because `bls12381_not_in_group_fix = false`"). Every `edge` input also reaches the timed-out
  callbacks of section 1.

The post-NEP-488 path is a protocol upgrade, not a PV86 shape. A Lean `version = 1` would be one
constant plus the decompress branch, to be tested when the claim moves past PV86.

## 3. ML-DSA-65 `z` exactly at the norm bound

The earlier claim that such a signature "cannot be produced without forging"
(`mldsa-fixtures/README.md` §6) is wrong for the key holder. near_crypto derives an ML-DSA-65 key
from a 32-byte seed: the seed string padded with spaces (`core/crypto/src/test_utils.rs:37-61`,
`ml_dsa_65_from_seed`, aws-lc `PqdsaKeyPair::from_seed`), which is FIPS 204
`ML-DSA.KeyGen_internal(ξ)`. Verification does not and cannot check how the mask `y` was drawn.

`tools/d3/mldsa65_bound.py` implements FIPS 204 KeyGen, Sign_internal and Verify (pure ML-DSA,
empty context, the `0 ‖ 0` prefix nearcore uses). Its boundary signer draws `y` as Sign_internal
does, then moves one coefficient to `T − e`, where `e` is drawn near the expected `(c·s1)` value. It
keeps a candidate only when that `z` coefficient is exactly `±T` and every other `|z_i| < γ1 − β`,
and when the other Sign_internal checks pass (`‖r0‖∞ < γ2 − β`, `‖c·t0‖∞ < γ2`, at most ω hints).
With `T = γ1 − β = 524,092` the signature fails only the norm check. The signer's verifier with the
norm check disabled accepts it, so the challenge matches. With `T = γ1 − β − 1` the signature is
valid, and its largest coefficient is the largest allowed. A signature takes 60–440 attempts
(a few seconds in Python).

**Vectors** (`mldsa-bound-verdicts.json.gz`): two near_crypto seeds (`keys-main-s2kmldsa`,
`keys-main-s1kdeleg`), four messages each, five modes:

| mode | max ‖z‖∞ | near_crypto/aws-lc (`mldsa-vectors --check`) | Lean `MlDsa65.verify` | Lean control C-M |
|---|---|---|---|---|
| honest | < 524,092 | 8 accept | 8 accept | 8 accept |
| at bound, + / − | 524,092 | 16 reject | 16 reject | **16 accept** |
| bound − 1, + / − | 524,091 | 16 accept | 16 accept | 16 accept |

The Python key derivation reproduces near_crypto's public key for both seeds (40/40).

**Whole chunks** (`NEAR_MLDSA_BOUND_SIGNER`, `keys/mldsa.rs` steps 47–52, after the 47 existing
`mldsa` steps). The oracle asks the boundary signer to sign the transaction hash or the NEP-461
delegate hash with the account's key:

| step | nearcore (all 4 seeds) |
|---|---|
| 47 `mldsa-tx-z-at-bound`, 48 `…-at-neg-bound` (injected) | `InvalidSignature` (failure outcome, transaction dropped) |
| 49 `mldsa-tx-z-bound-minus-one`, 50 `…-neg-bound-minus-one` | success, transfer executed |
| 51 `deleg-mldsa-z-at-bound` | relayer transaction ok; delegate `DelegateActionInvalidSignature` |
| 52 `deleg-mldsa-z-neg-bound-minus-one` | delegate executed |

Every chunk carrying one of these steps gets the full mutant set, with drop-node mutants
(`scenarios.rs` `force_full_mutants`). Population: 147–156 honest chunks and 604–628 mutants per
run. Replayed: seed 1618 in full (783 rows); the others with every honest chunk and every second
mutant (452–460 rows). **2,150 rows, 0 disagreements.**

## 4. Mismatched distribution code identities

Lean refuses a distribution receipt whose `CodeHash` identifier is not sha256 of its code, with the
named exclusion `out of domain (w.shape): global_code_identity`
(`Successor/GlobalExecution.lean:90-95`). The question is whether a valid chunk can reach it. It
cannot:

* A distribution receipt is constructed in two places only. `initiate_distribution` sets
  `id = CodeHash(hash(code))` (or `AccountId`) from the deployed code itself
  (`runtime/runtime/src/global_contracts.rs:162-195`). `forward_distribution_next_shard` uses
  `GlobalContractDistributionReceipt::forward` (`:317-353`), which copies `id`, `code` and `nonce`
  and changes only the target and delivered shards (`core/primitives/src/receipt.rs:974-986`).
* A receipt reaches a chunk application from three places:
  * Incoming receipts are bound by the source receipt proofs to the source chunk's outgoing
    receipts root (`chunk_validation.rs:449-562`; Lean
    `verifyReceiptProofD2`, `Successor/RuntimeCore.lean:298,536`).
  * Delayed and buffered receipts are read from the state under the authenticated pre-state root.
  * Both of those were written by a runtime that emitted the receipt.
* At genesis, a postponed distribution receipt panics (`core/store/src/genesis/state_applier.rs:308-314`).
  A `StateRecord::DelayedReceipt` is stored verbatim (`:267-269`), so a malformed distribution in a
  custom genesis is not excluded by nearcore. Mainnet's genesis (PV29) predates the
  `GlobalContractDistribution` variant and has none. For any other genesis, Lean's named exclusion
  keeps such a chunk out of domain, never accepted.

By induction from such a genesis, every distribution receipt a valid chunk can apply has
`id = CodeHash(sha256(code))` or an `AccountId` id. The exclusion removes no valid chunk.

**Identity mutants** (`NEAR_DIST_MUTANTS=1`, `d3.rs` `dist_mutants`, no RNG use). These are global-cache
runs. Every incoming distribution receipt of every honest chunk is mutated:

* the code: a byte flipped in the middle, first or last position; the last byte dropped; or a byte
  appended;
* the identifier: a `CodeHash` bit flipped; `CodeHash` replaced by `AccountId(predecessor)`; or
  `AccountId` replaced by the consistent `CodeHash(sha256(code))`;
* the `code_flip` proof placed next to the honest one under the same chunk hash, first (`dup_last_good`,
  where the last entry wins) or last (`dup_last_bad`).

nearcore rejects every mutant except `dup_last_good` with `Receipt proof … has invalid merkle path`.
It accepts `dup_last_good`. Lean returns the same verdicts, rejecting with `receipt proof merkle path`
**before** the identity guard, so the exclusion is never reached. Controls C-D1 and C-D2 show the
layering. With proof verification removed, the applied-receipts hash still rejects every mutant.
With both removed, the `CodeHash` mutants reach the identity guard (out of domain) and the rest fail
on the post-state root. No layer removal makes Lean accept a mutant. Over 8 seeds: 110 honest
chunks + 917 mutants = **1,027 rows, 0 disagreements**.

## 5. State init followed by a successful emit (`NEAR_XFAM_VARIANT=state-init-emit`)

`xfam.rs` `state_init_emit()`, run with `NEAR_SUCCESSOR_SCENARIO=rollback-refund`. In the
`rollback-refund` composition the derived account held only its storage stake, so the emitted
1,000-yocto promises failed with `BalanceExceeded` and the init was rolled back. Here the account is
paid first, in one of three ways:

* the emitting call's own deposit, in the same receipt as the init;
* a `Transfer` between the init and the call;
* a later transaction from the signer or from another account.

Per round (4 per run) there are six emitting steps, by global code hash and by account id:

* cross-shard targets with a `promise_then` callback;
* a failing target, whose callback sees the failure;
* a self-call plus another shard, with 512 bytes of init data;
* the later deposit and transfer variants.

There are also an init-only step, an ordinary transfer, and the unfunded composition as a control.

nearcore: in every run, 23–24 emitting steps succeed and their emitted receipts execute. Callbacks
return `01` on success and `02` after the failing target. All 4 unfunded controls fail with
`Exceeded the account balance`. The single exception (se702, step 35) is a later transfer that
reached the derived account before its init, because missing chunks reordered the shards: nearcore
reports `AccountDoesNotExist`. The collector records it and does not fail the run.

Population: 66–74 honest chunks and 2,581–2,697 mutants per run (`NEAR_XFAM_MUTATE_EVERY=1`).
Replayed: every honest chunk and every 8th mutant, 392–412 rows per run. **1,595 rows, 0
disagreements.**

## Deliberate-breakage controls (`generation.json` `control_checkers` and `run_scripts.ctl.py`)

Each control is this tree's checker with one deliberate bug in the family's semantics (C-D2 has two), built and
replayed on part of the family (`replay/<run>-ctl-*.json`):

| control | breakage | replayed | rows that flip against nearcore |
|---|---|---|---|
| C-M `ctl-mldsa-norm` | `zNormOk` admits `‖z‖∞ = γ1 − β` (`MlDsa65.lean:294`, `<` → `≤`) | mb1618 bound-step honest chunks + every 8th of their mutants (97) | 8, including all three honest chunks with an at-bound signature (post-state root / missing access key); the vectors flip 16/16 |
| C-S `ctl-stateinit-then` | one extra yocto credited by a state init followed by more actions in the receipt (`GlobalExecution.stateInitL`) | se701 honest (66) | 4: the four state-init-emit composition chunks, one per round (post-state root) |
| C-Y `ctl-yield-timeout-result` | a timed-out yield's callback gets `Successful([])` instead of `Failed` (`StorageExecution.yieldLoop`) | cy601 honest chunks from the callback heights (88) | 56 honest chunks rejected (`InvalidReceiptsProof`: the resume data receipt differs) |
| C-D1 `ctl-dist-proof` | incoming receipt proofs that carry a distribution receipt are not verified (`RuntimeCore.lean:298,536`, `ReshardCore.lean:313`); the two `rfl` legacy-core equalities this breaks are dropped from the control build only | gdb812 population (140) | 0 verdict flips: all 110 mutants are still rejected, now by the second check, `invalid: applied receipts hash` (the witness's applied-receipts hash covers the honest receipts). The rejection reason moves on 110/110 rows |
| C-D2 `ctl-dist-proof-hash` | C-D1, and the applied-receipts hash is also skipped when a distribution receipt is present | gdb812 population (140) | **35 rows stop rejecting**: every `CodeHash` mutant whose code no longer matches reaches the identity guard, `out of domain (w.shape): global_code_identity`. The other 75 mutants are rejected by the post-state root or a missing global-contract nonce. None is accepted |

## Blind replay (`--blind`)

`tools/mainnet-replay/blind_corpus.py` blinds each honest chunk: every produced value is zeroed,
and the 11 header outputs Lean computes are graded against the header nearcore produced. The blinded
inputs are also run with comparisons on, as a control, which must not accept.

| family | honest chunks graded | match | of which exercise |
|---|---|---|---|
| state-init-emit (all honest, 4 runs) | 281 | 281 | balance burnt 199, buffered gas 74, implicit transitions 37, proposals 10 |
| curve-yield-timeout (every honest chunk at the timeout-callback heights, ≥ 10205) | 330 | 330 | balance burnt 214, buffered gas 87, bandwidth requests 2, implicit transitions 39 |
| mldsa-z-bound (honest chunks carrying or executing steps 47–52) | 79 | 79 | balance burnt 53, implicit transitions 14 |
| dist-identity (honest chunks with an incoming distribution receipt) | 110 | 110 | balance burnt 74, delayed gas 12, buffered gas 14, implicit transitions 14 |

**800 / 800 match**, with 0 field differences (`replay/blind-*.json`).

## Committed cases (`cases.tar.gz`, `cases-index.json`)

There are 86 cases with nearcore's and Lean's verdicts, and the sha256 of every file:

| family | honest chunks | mutants |
|---|---|---|
| state-init-emit | 8: chunks applying a successful post-init emit | 18 |
| curve-yield-timeout | 8: chunks from the callback heights | — |
| mldsa-z-bound | 8: chunks carrying a bound step | 12 |
| dist-identity | 8 | 24 `w.dist.*` |

All agree with nearcore: 42 accept (the 32 honest chunks and 10 nearcore-valid mutants: 8
`dup_last_good` and 2 state-init-emit mutants) and 44 reject.

## Reproduce

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=T cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
B=T/release/near-arena-oracle-v3-successor
export NEAR_SUCCESSOR_OBSERVABLES=1
# curve hosts in timed-out yield callbacks (also seeds 602–604, first chains 1, 2, 6)
NEAR_SUCCESSOR_SCENARIO=curve-callbacks NEAR_XFAM_VARIANT=curve-yield-timeout NEAR_XFAM_MUTATE_EVERY=3 \
  $B gen --domain d3 --seed 601 --first-chain 0 --chains 1 --blocks 280 --mutate-every 0 --code-mutant-p 0 \
  --ood-cap 100000 --drop-cap 12 --min-gas-price 100000000 --out cy601
# state init then a successful emit (also 702–704)
NEAR_SUCCESSOR_SCENARIO=rollback-refund NEAR_XFAM_VARIANT=state-init-emit NEAR_XFAM_MUTATE_EVERY=1 \
  $B gen --domain d3 --seed 701 --first-chain 0 --chains 1 --blocks 70 --mutate-every 0 --code-mutant-p 0 \
  --ood-cap 100000 --drop-cap 12 --min-gas-price 100000000 --out se701
# ML-DSA z at the norm bound (also 2718, 31415, 6151)
NEAR_SUCCESSOR_SCENARIO=mldsa NEAR_MLDSA_BOUND_SIGNER=$PWD/tools/d3/mldsa65_bound.py \
  $B gen --domain d3 --seed 1618 --chains 1 --blocks 300 --mutate-every 0 --code-mutant-p 0 --ood-cap 2000 --out mb1618
# distribution identity mutants (also 812–818, first chains 1, 2, 6, 7, 8, 9, 10)
NEAR_SUCCESSOR_SCENARIO=global-cache NEAR_DIST_MUTANTS=1 \
  $B gen --domain d3 --seed 811 --first-chain 0 --chains 1 --blocks 140 --mutate-every 0 --code-mutant-p 0 \
  --ood-cap 2000 --min-gas-price 100000000 --out gdb811
python3 tools/d3/collect_xfam.py --source cy601 --out col/cy601
python3 tools/d3/collect_keys.py --source mb1618 --binary $B --out col/mb1618 --scenario mldsa-bound
python3 tools/d3/replay_successor.py --tier allFeatures --cases-file LIST --out rep --jobs 2
python3 tools/mainnet-replay/blind_corpus.py --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor --cases HONEST --root / --out blind
# vectors
python3 tools/d3/mldsa65_bound.py sign keys-main-s2kmldsa MSG_HEX at+   # or at-, in+, in-
$B mldsa-vectors --check FILE              # lines: SEED_STR MSG_HEX SIG_HEX
(cd spec/lean/v3 && lake build nearspec-v3-mldsa-check) && .lake/build/bin/nearspec-v3-mldsa-check < PK_MSG_SIG_LINES
```

`generation.json` records the exact commands (`run_scripts`), the binary and source hashes, and
per-run totals. The raw runs, including nearcore's per-witness observable records
`nearcore-observables-*.jsonl` (`NEAR_SUCCESSOR_OBSERVABLES=1`, for the W01 comparator), are local
under `/data/illia/nearproof-deps/w10-runs/runs/` and are bound by the hashes in the manifests and
replay reports.

## Not covered

* The curve and state-init-emit populations are sampled for replay: every 16th or 8th mutant, all
  honest chunks. The ML-DSA population is sampled at every second mutant for three seeds.
* In the failed-result variants of section 1, the host is not reached: the read of a missing
  register fails first. That is nearcore's behaviour, and Lean agrees. Host execution inside timeout
  callbacks is covered by the argument variants (70 per run).
* A deferred timeout (one that falls due while the compute limit is exhausted) whose callback runs
  a host is not targeted. Deferred timeouts are covered without hosts by `yield-congestion`.
* `version = 1` is not implemented in Lean (section 2): it is a PV155 behaviour.
* ML-DSA boundary signatures appear as transaction and delegate signatures only. ML-DSA is never
  verified by a host function at PV86 (`mldsa-fixtures/README.md` §1).
* A malformed distribution receipt in a *custom* genesis `DelayedReceipt` record is not excluded by
  nearcore. It is outside the mainnet claim, and Lean keeps it out of domain.
* The observable records of these runs are produced, not yet compared: that is item 9's comparator.
