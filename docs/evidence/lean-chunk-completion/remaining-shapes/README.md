# Remaining shapes (workplan item 10, W05–W07)

Target: nearcore 2.13.4 (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`), PV86, mainnet parameters.
Checker: `nearspec-v3-check-successor --tier allFeatures` (sha256 `a1627ea3…`). Generator:
`oracle/v3-successor`, with two new opt-in scenarios in `src/xfam.rs`:
`NEAR_SUCCESSOR_SCENARIO=curve-yield-timeout | state-init-emit` (binary sha256 `f00dd236…`,
`oracle-d1`). Every honest chunk was accepted by the cold nearcore validator. Lean only computes;
nearcore's results are never inputs.

| # | shape | disposition | evidence |
|---|---|---|---|
| (i) | curve hosts called from a **timed-out** yield callback | fixtures: 4 seeds, 2,051 verdict rows, 0 disagreements | §1 |
| (ii) | post-NEP-488 BLS `version = 1` | **unreachable at PV86** (source argument) | §2 |
| (iii) | ML-DSA-65 `z` exactly at the norm bound | unit vectors, 16/16: pinned crate = FIPS 204 = Lean; the earlier "needs forging" claim is wrong | §3 |
| (iv) | distribution receipt whose identifier does not match its code | `CodeHash` mismatch **unreachable**; the realistic `AccountId` stale-nonce shape is reachable and not yet fixtured | §4 |
| (v) | state init followed by a **successful** emit | fixtures: 4 seeds, 6,583 verdict rows, 0 disagreements | §5 |

**No Lean accept of a nearcore reject. No Lean reject of a nearcore-accepted chunk.** The only
non-matching rows are 5 code-blob mutants that Lean puts out of domain as `e.wasm-α`, the W08
preparation-race exclusion (§6). nearcore rejects all 5.

## Reproduce

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=/tmp/oracle-target cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
B=/tmp/oracle-target/release/near-arena-oracle-v3-successor
export RAYON_NUM_THREADS=128
# (i) seeds 601–604 on chains 0, 1, 2, 6; gas price 1e8 on 601 and 603
NEAR_XFAM_MUTATE_EVERY=3 NEAR_SUCCESSOR_SCENARIO=curve-yield-timeout $B gen --domain d3 --seed 601 \
  --first-chain 0 --chains 1 --blocks 260 --p-missing 0.05 --mutate-every 0 --code-mutant-p 0 \
  --ood-cap 100000 --drop-cap 10 --min-gas-price 100000000 --out cy601
# (v) seeds 701–704 on chains 0, 1, 2, 6; gas price 1e8 on 701 and 703
NEAR_XFAM_MUTATE_EVERY=1 NEAR_SUCCESSOR_SCENARIO=state-init-emit $B gen --domain d3 --seed 701 \
  --first-chain 0 --chains 1 --blocks 45 --p-missing 0.05 --mutate-every 0 --code-mutant-p 0 \
  --ood-cap 100000 --drop-cap 8 --min-gas-price 100000000 --out se701
python3 tools/d3/collect_xfam.py --source cy601 --out col/cy601     # fails on a violated family fact
cat col/cy601/honest.txt > list; sort col/cy601/mutants.txt | awk 'NR%4==1' >> list   # (v): every mutant
python3 tools/d3/replay_successor.py --tier allFeatures --cases-file list --out rep --jobs 24
```

The generator changes are opt-in. With no scenario set, the pre-change binary and this one produce
**byte-identical** output on seed 7, 2 chains, 40 blocks, `--mutate-every 10` (8,545 files,
`diff -r` empty). That covers both new scenarios here and `code-cap` (`../size-limit-chunks`).

`manifests/*.json.gz` hold the collected per-step nearcore outcomes. `rows-*.jsonl.gz` hold the Lean
rows. `replay-summary.json` holds the replay reports, including the committed cases and the controls.

## 1. Curve hosts from timed-out yield callbacks (`curve-yield-timeout`, W05)

**The gap.** `../cross-family-fixtures` §2 left this open: its `curve-callbacks` yields were all
resumed, to keep runs short.

**The steps.** Each of the 40 curve-host picks of `curve-callbacks` is used: the first pos / neg /
edge input of each host, plus the gas-exhaustion input. Each becomes a `yslot` yield on `xcurve` that
is **never resumed**. The yield's callback is chosen as follows:
- for every pick, the host itself, on the callback arguments (`timeout-args`);
- for the pos picks, also `<host>_rm` and `<host>_rr`, which read the timed-out (failed) promise
  result into memory or a register.

That gives 66 steps per run. They are submitted 4 per height; every third step is signed from
another shard, and receivers alternate between shards. Runs last 260 blocks, so every timeout
fires: **all 66 callbacks ran at +201 or +202 blocks in all 4 seeds**
(`steps-curve-yield-timeout.md`).

Per run, identical in the 4 seeds:

| callback outcome (nearcore) | steps |
|---|---|
| host returned normally (result 0) | 19 |
| host returned normally (non-zero result / output) | 13 |
| `Accessed invalid register id: 0` (`_rm`: the failed promise result writes no register) | 18 |
| `Integer overflow` at the per-element charge (`_rr` register input, `value_len = u64::MAX`) | 8 |
| `Exceeded the prepaid gas` at the element charge (gas-exhaustion picks) | 5 |
| AltBn128 input errors (invalid fr, invalid g2, bad slice size) | 3 |

| run | chain (shards) | gas price | honest (family) | mutants replayed (of generated) | Lean rows | disagreements |
|---|---|---|---|---|---|---|
| cy601 | 0 (4) | 1e8 | 105 | 449 (1,793) | 554 | 0 |
| cy602 | 1 (5) | 0 | 92 | 376 (1,503) | 468 | 0 |
| cy603 | 2 (6) | 1e8 | 104 | 429 (1,716) | 533 | 0 (1 named OOD) |
| cy604 | 6 (4) | 0 | 96 | 400 (1,599) | 496 | 0 (1 named OOD) |
| **total** | | | **397** | **1,654** | **2,051** | **0** |

- **Sampling.** Every honest chunk is replayed. Mutants are sampled 1 in 4 (the sorted list), as in
  cross-family §Results; Lean takes up to about 2 minutes on a curve chunk.
- **Verdict split.** Honest: 397 accept / 397. Mutants: 336 accepted, 1,316 rejected,
  2 out of domain. Lean equals nearcore on all of them.

## 2. Post-NEP-488 BLS `version = 1` — unreachable at PV86

1. **Where the flag turns on.**
   - `bls12381_not_in_group_fix` is `false` in the base config (`parameters.yaml:292`,
     `parameters.snap:289`).
   - It changes to `true` only in `runtime_configs/155.yaml:1`, registered at
     `core/parameters/src/config_store.rs:65`.
2. **No node runs PV155.**
   - `STABLE_PROTOCOL_VERSION = 86` and `NIGHTLY_PROTOCOL_VERSION = 155`
     (`core/primitives-core/src/version.rs:628-631`).
   - `PROTOCOL_VERSION` is 155 only under `cfg!(feature = "nightly")` (`:640-646`). A 2.13.4
     release node never supports or votes for it.
3. **Config lookup.** `RuntimeConfigStore::get_config` takes the last entry ≤ the requested version
   (`config_store.rs:240-248`), so every version below 155 gets `false`.
4. **Where the hosts branch.**
   - The runner picks `version = 1` only if the flag is set
     (`runtime/near-vm-runner/src/logic/bls12381.rs:49-53`, also `wasmtime_runner/logic.rs:62-66`).
   - It uses that version in parse (`bls12381.rs:109-110`) and decompress (`:211`).
   - The only other place the flag is forced on is `enable_all_features` (`core/parameters/src/vm.rs:274-283`),
     which only the parameter estimator calls.
5. **Which config a witness uses.**
   - The main transition and every implicit transition are applied with the config of the
     protocol version of their own block's epoch
     (`chain/chain/src/stateless_validation/chunk_validation.rs:318-322,591,714`;
     `chain/chain/src/runtime/mod.rs:277,282,1255`).
   - The next epoch's `next_wasm_config` (`runtime/mod.rs:311-319`) only pre-warms the compile cache
     (`runtime/runtime/src/pipelining.rs:253-262`).
6. **Every epoch is PV86.** At the pinned target, all epochs are PV86. Mainnet goes PV84 → PV86, and
   PV84 also has the flag `false` ([resharding-fixtures-2](../resharding-fixtures-2/README.md) §3,
   UQ-009).

**Lean.** `bls12381Version : Nat := 0` (`BLS12381.lean:583`, `Wasm/CryptoHost.lean:164`). The
version-1 branches are written but unreachable (`BLS12381.lean:461,688`). Every non-86 epoch is
rejected (`checkSuccessor_unsupported_pv`, `Successor/Config.lean:294`). **No fixture is possible at
the pinned target.**

One small comment fix for the integrator: the Lean comments cite `logic/bls12381.rs:17-28` for the
branch. The branch is at `:49-53`; `:24` is only the constant.

## 3. ML-DSA-65 `z` at the norm bound (`mldsa/`)

**Why it is possible.** `../mldsa-fixtures` §6 says a z-norm boundary signature "cannot be produced
without forging". That is not so. With the secret key, FIPS 204 `Sign_internal` (Algorithm 7) can be
run with only the ‖z‖∞ < γ1−β rejection replaced by a filter that keeps max|z| ∈ {B−1, B, B+1}
(B = γ1−β = 2¹⁹ − 196 = 524,092). Everything else is kept: the r0 / ct0 checks, ω,
c̃ = H(μ‖w1Encode(w1)) and the hint encoding. The result is a signature whose challenge and hints are
genuine and only the norm is at the boundary. It takes about 1 hit per 2,000–4,000 attempts per
category and sign.

**Validation of the signer.** `mldsa/mldsa65.py` is a pure-Python FIPS 204.
- Its keygen equals `SecretKey::from_seed(KeyType::MLDSA65, seed)`: `w06-mldsa-vector-0` is
  reproduced byte for byte.
- Its verifier matches all 74 pinned-crate verdicts of `MlDsaCrate.lean` and 30 ACVP vectors.
- With the norm test disabled, it accepts all 16 boundary signatures, which shows c̃ and the hints
  are correct.

**The vectors.** Keys use seeds `zbound-mldsa-0..3`; message k is `sha256("zbound-msg-k")`. They are
deterministic (`gen_zbound.py OUT 4 128 256`).

| case (k = 0..3) | max\|z\| | FIPS 204 | pinned crate (aws-lc-rs 1.16.2) | Lean `MlDsa65.verify` |
|---|---|---|---|---|
| `kK-zmax-bound-minus-1` | 524,091 | accept | accept 4/4 | accept 4/4 |
| `kK-zmax-bound-pos` (+B) | 524,092 | reject | reject 4/4 | reject 4/4 |
| `kK-zmax-bound-neg` (−B) | 524,092 | reject | reject 4/4 | reject 4/4 |
| `kK-zmax-bound-plus-1` | 524,093 | reject | reject 4/4 | reject 4/4 |

- **Crate verdicts.** From `oracle mldsa-vectors --verify FILE`, a new mode in
  `src/mldsa_vectors.rs` that reuses `Signature::verify` (`add_crate_verdict.py`). As a check, it
  reproduces all 74 verdicts in `MlDsaCrate.lean`.
- **Lean verdicts.** From a scratch program run against the built oleans
  (`lake env lean --run`, no source change).

**Lean test to add** (left for the integrator):
1. Emit `Examples/MlDsaZBound.lean` from `zbound-vectors.json`. Use
   `tools/d3/mldsa_vectors_to_lean.py` with a `--zbound` option, the same keys/sigs/cases layout,
   and `expect := crate_verdict`.
2. Add to `MlDsaVectors.lean`:
   `#guard MlDsaZBound.cases.size == 16`, `#guard (accepts).length == 4`, and
   `#guard zbFailures == []`.

That is 16 verifications, about 10 s in the interpreter. It catches a `≤`/`<` slip in either
direction.

**Whole-chunk inclusion.** Not done here. What it would take:
- The accepting variant (max|z| = B−1) is an ordinary valid signature. Re-signing a transaction hash
  with aws-lc's randomized signer until max|z| = B−1 takes about 400 tries, so it can sit in an
  honest chunk.
- The rejecting variants need the custom signer on the chunk's own transaction or NEP-461 hash.
  Ways in:
  - a delegate action inside a validly signed transaction gives
    `DelegateActionInvalidSignature` in an honest chunk;
  - or a `Mode::Inject` transaction, as `mldsa-tx-bad-z` already is.

## 4. Distribution receipts whose identifier does not match the code

1. **Creation.** The only consensus constructor is `initiate_distribution`
   (`runtime/runtime/src/global_contracts.rs:162-197`, called from `action_deploy_global_contract`
   `:57-65`). It computes the identifier from the action itself: `CodeHash(hash(&contract_code))` or
   `AccountId(account_id)` (`:171-178`), and builds the receipt with
   `Receipt::new_global_contract_distribution` (`core/primitives/src/receipt.rs:539-549`).
2. **Forwarding.** `forward_distribution_next_shard` (`global_contracts.rs:317-361`) uses
   `forward` (`receipt.rs:974-987`, `..v2.clone()`). Only the target shard and the delivered-shards
   list change.
3. **No injection.**
   - There is no user path: `verifier.rs:582` has nothing to check for this receipt type.
   - Incoming receipts must prove inclusion under the source chunk's `prev_outgoing_receipts_root`
     (`chain/chain/src/stateless_validation/chunk_validation.rs:449-526,529-560`). Delayed and
     buffered receipts come from the authenticated trie.
   - So a `CodeHash(h)` receipt with `h ≠ sha256(code)` is **unreachable**.
4. **Apply (nearcore).** `apply_distribution_current_shard` does not re-check the hash
   (`global_contracts.rs:222-268`).
5. **Lean.** Lean is stricter but safe.
   - `applyDistributionL` puts a `CodeHash` mismatch out of domain
     (`Successor/GlobalExecution.lean:93-95`, `w.shape: global_code_identity`). This cannot fire on
     a valid chunk, by items 1–3.
   - Source receipts are authenticated (`Successor/RuntimeCore.lean:296-298`).
6. **The reachable "mismatch": `AccountId` redeploys.**
   - A second `AccountId` deploy with **different** code, before the first distribution is applied,
     creates receipt #1 with nonce 1 and receipt #2 with nonce 2.
   - On the deploying shard, #1 arrives stale. It is skipped but still forwarded
     (`global_contracts.rs:238-240,273-298`).
   - Elsewhere, both receipts apply in nonce order.
   - Lean mirrors the nonce rule (`GlobalExecution.lean:100-115`). The stale branch is unit-tested
     only (`TestGlobalActions.lean:72-74,105`).
   - **Not yet fixtured:** the global-cache `redeploy-account-nonce` step redeploys the *same* code
     (`d3gen.rs:410-415`). An `AccountId` deploy of code A then code B in one receipt would be the
     honest whole-chunk fixture.

## 5. State init followed by a successful emit (`state-init-emit`, W07)

**Why the old scenario never reached the emit.** In `rollback-refund`, the derived account had no
balance for the 1,000-yocto promises. `action_deterministic_state_init` creates it with zero balance
and keeps only the storage-stake shortfall of the deposit, refunding the rest
(`runtime/runtime/src/deterministic_account_id.rs:35,55-89`).

**What the new scenario does.** It funds the derived account in the same receipt. After
`deploy-global-hash` / `deploy-global-account`, there are four rounds (rounds 0 and 2 use the
code-hash identifier, 1 and 3 the account identifier), one height each:

| step | actions | nearcore outcome (all 4 seeds) |
|---|---|---|
| `state-init-emit-deposit-then` | state init, `emit` mode 2 with 1 NEAR deposit (promises to `s2rbt.noop`, `s3rbt.fail`, then a callback) | init + **emit ok**, `noop` ok, `fail` panics, callback ok (`02`) |
| `state-init-transfer-emit` | state init, `Transfer` 1 NEAR, `emit` mode 0 (two `noop`s) | init + **emit ok**, both promises ok |
| `state-init-emit-local-target` | state init, `emit` with 0.1 NEAR (promise to `s0rbu.noop` + callback) | **emit ok**; callee fails `CodeDoesNotExist`; callback ok |
| `reinit-emit` | the same state init again on the now-active account, then `emit` | the second init is a no-op with refund; **emit ok** |
| `state-init-emit-same-shard-signer` | as the first, signed from the target's shard | **emit ok**, callback `01` |
| `state-init-emit-then-panic` | state init, `emit` mode 1 (panic after the promises) | whole receipt rolled back (`GuestPanic`) |
| `state-init-emit-unfunded` (control) | the original shape | `Exceeded the account balance` (BalanceExceeded), rolled back |

Per-step trees are in `steps-state-init-emit.md`.

| run | chain (shards) | gas price | honest (family) | mutants | Lean rows | disagreements |
|---|---|---|---|---|---|---|
| se701 | 0 (4) | 1e8 | 49 | 1,585 | 1,634 | 0 |
| se702 | 1 (5) | 0 | 48 | 1,592 | 1,640 | 0 |
| se703 | 2 (6) | 1e8 | 48 | 1,583 | 1,631 | 0 |
| se704 | 6 (4) | 0 | 45 | 1,633 | 1,678 | 0 (3 named OOD) |
| **total** | | | **190** | **6,393** | **6,583** | **0** |

Honest: 190 accept / 190. Mutants: 1,353 accepted, 5,037 rejected, 3 out of domain. Every mutant was
replayed.

## 6. Non-matching rows

| run | case | nearcore | Lean |
|---|---|---|---|
| se704 | `06-h10033-s3-code.{drop.0,flip.0,truncate.0}` | reject (`MissingTrieValue`) | out of domain `e.wasm-α` |
| cy603 | `02-h10016-s0-code.drop.2` | reject | out of domain `e.wasm-α` |
| cy604 | `06-h10218-s0-code.none` | reject | out of domain `e.wasm-α` |

These are code-blob mutants of chunks that deploy in the chunk and also call pre-state code. That is
the W08 preparation-race exclusion, as in cross-family "Non-matching rows". The generator labels them
`e.code_cache`, so the harness counts them as unasserted (state-init-emit) or asserted
(curve-yield-timeout) exclusions.

## 7. Committed cases and deliberate-breakage controls

**Committed cases.**
- `curve-yield-timeout-cases.tar.gz` (0.93 MB): per seed, the yield-creation chunk and the
  timeout-callback chunk with the most scenario receipts, each with 3 mutants of distinct families
  (8 honest + 24 mutants).
- `state-init-emit-cases.tar.gz` (0.73 MB): the same layout.
- Index files are `*-cases-index.json`.
- `allFeatures` on all 64: **64/64 agree** (20 accept, 44 reject).

**Controls.** One checker (sha256 `ae331c97…`) built from HEAD `e65da9101` in a scratch copy, with
one family-local bug per family. Detected rows flip against nearcore:

| control | breakage | population | detected |
|---|---|---|---|
| C-yield | a timed-out yield delivers a *successful empty* result instead of a failed one (`StorageExecution.yieldLoop`, `.data true d none` → `some []`) | 397 honest `curve-yield-timeout` chunks | **105** rejected (`InvalidReceiptsProof`), all among the 186 chunks that apply a timeout callback or its follow-up receipts |
| C-init | the state init does not write its `data` entries (`GlobalExecution.stateInitL`) | 190 honest `state-init-emit` chunks | **16** rejected (main transition post state root), one per seed and round (4 × 4) |
| C-code | `codeResponseBytes` without the 4-byte vector prefix | 286 `code-cap` cases (`../size-limit-chunks`) | 6 leave the exclusion; the honest 67,108,865-B chunk is **accepted** |

**A control that showed nothing.** A first C-init that refunded the whole deposit was not detected:
0 / 190. In every fixture the derived account stays within the zero-balance storage allowance, so
nearcore itself refunds the whole deposit, and that bug is a no-op on these chunks. Consequence: no
fixture here exercises a state init that consumes part of its deposit. The `rollback-refund`
`state-init-insufficient-deposit` step covers only the `LackBalanceForState` side.

## Not covered

- **(iv)** The `AccountId` stale-nonce redeploy with different code, as a whole chunk (§4.6).
- **(iii)** A boundary signature inside a whole chunk (§3).
- **(v)** A state init whose deposit is partly consumed by storage stake (§7).
- Curve mutants are sampled 1 in 4; all honest chunks are replayed.
- **The signed tier.** Not run. Curve hosts and global actions are outside its domain.
