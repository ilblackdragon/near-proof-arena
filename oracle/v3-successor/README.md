# Versioned successor fixture generator

Uses the pinned nearcore validator and existing D3 chain/witness generator. It is a separate
package from the signed oracle. Set `NEAR_SUCCESSOR_CONTRACT` to a Wasm file to replace only the
`d3float` test account code (its called method is `run`). Missing/empty configured files fail.
Without that variable the code registry is identical to the baseline.

Record the binary, contract, input/output hashes and generator seed with each run. Existing
D3 classifications describe the baseline; a newly generated runtime-error or global family
needs explicit successor expectations. Do not relabel generated evidence as the pinned corpus.

Build after `bash oracle/scripts/link-nearcore.sh`:
`cargo build --release --manifest-path oracle/v3-successor/Cargo.toml`.
The CLI is the existing D3 generator CLI; `gen --domain d3 --seed S --chains K --blocks N --out DIR`.

The versioned `src/d3.rs` case writer keeps baseline domain classifications in metadata,
but permits mutation of honest cases whose only exclusions are floats and/or the old gas cap.
Mutant metadata retains those base exclusions and adds cache exclusions when applicable.
The cold validator and mutation algorithms are reused. This is necessary because the signed
writer returns before mutating every baseline-excluded float case. No signed source is changed.

## Global action and cache scenario

Set `NEAR_SUCCESSOR_SCENARIO=global-cache` for 17 deterministic steps on dedicated funded accounts:
global deployment by hash/account, use+call, missing-use failure, failed-call rollback, third-party
state initialization, missing-code initialization, repeated initialization/refunds, redeployment
nonce, local deploy+call/rollback, subsequent calls and cross-account deploy/call traffic. The final
state-init step has 2,048 bytes of data and zero deposit to exceed the zero-balance storage exemption.
Steps wait six blocks for receipt/distribution delivery, except the cross-account pair, which is
submitted at the same height when traffic scheduling permits. Inspect actual receipt outcomes;
submission at one height does not guarantee execution in one chunk.

```
NEAR_SUCCESSOR_SCENARIO=global-cache near-arena-oracle-v3-successor gen --domain d3 \
  --seed 2718 --chains 1 --blocks 140 --mutate-every 0 --code-mutant-p 0.2 --ood-cap 2000 --out RUN
python3 tools/d3/collect_global_cache.py --source RUN --binary PATH_TO_ORACLE --out MANIFEST
```

Seed 31415 was also run with `--max-d3 8`. The collector fails if any of the 17 transaction labels or
all distribution receipts are absent. It separately records transaction-stage labels, executed action
outcomes, receipt classes and exact byte hashes; labels alone never establish action success.
Opt-in global scenarios allow code mutants of `w.shape` cases. Original domain classifications and
raw nearcore expectations are preserved. Neither this nor the collector claims that every `w.shape`
case is supported by Lean.

A complete-code successor policy can reject an incomplete witness that a warm or racing cold
nearcore cache happens to accept. These are different contracts: retain raw cold observations and
complete-code witness-policy expectations separately. No mutation expectation is rewritten here.

## Curve-host scenario

Set `NEAR_SUCCESSOR_SCENARIO=curve-hosts` to deploy `contracts/curvehosts.wat` (compiled at run time
with the lock's `wat`) on two funded accounts, `s0curvehosts` and `s2curvehosts`, and submit 149
deterministic FunctionCalls (`src/curve_hosts.rs`, at most 3 per height). They call every
alt_bn128 and BLS12-381 host plus `p256_verify` and `ecrecover`, from memory, from a register
(`value_len = u64::MAX`) and from out-of-bounds memory, with valid inputs, malformed lengths,
non-canonical field elements and scalars, off-curve and non-subgroup points, infinity, the
`(0, ±2)` corner, empty input and gas exhaustion at the per-element charge. Inputs are built with the
crates nearcore links (zeropool-bn, blst, p256, near-crypto); every output, error and gas figure is
nearcore's. Receivers alternate and every third call is signed by the other account, so some receipts
cross shards. Each executed call of the contract is recorded under `features.curve_calls` (status,
exact value bytes, gas, ext profile). The scenario's `e.ood_host` chunks are also mutated.

```
near-arena-oracle-v3-successor curve-steps > STEPS.json
NEAR_SUCCESSOR_SCENARIO=curve-hosts near-arena-oracle-v3-successor gen --domain d3 --seed 4242 \
  --chains 1 --blocks 100 --mutate-every 8 --code-mutant-p 0.2 --ood-cap 5000 \
  --min-gas-price 100000000 --out RUN
python3 tools/d3/collect_curve_hosts.py --source RUN --steps STEPS.json --binary PATH_TO_ORACLE --out DIR
```

The collector fails unless every step executed exactly once; it locates a step by method, args hash
and attached gas, never by label. Labels name the input class (`pos`/`neg`/`edge`), not an expected
result.

## Key-family and gas-key scenario

Set `NEAR_SUCCESSOR_SCENARIO=keys` for 60 labelled steps (`src/keys.rs`, `successor.keys.NN.name`)
on six dedicated genesis accounts: secp256k1 transaction keys, delegate actions with a secp256k1
inner key, ML-DSA-65 keys in key storage (and one ML-DSA-signed transaction), gas keys, and the
three gas-key promise host functions through `contracts/kgashost.wat`. Steps the transaction pool
refuses (bad signatures, stale nonces, invalid nonce indices, insufficient gas-key balance, invalid
AddKey) are injected into the next chunk of the account's shard. An injection that misses every
produced chunk is retried, and a step whose prerequisite key has not landed waits up to eight
blocks. `src/chaind3.rs` is a versioned copy of the signed `oracle/v3-d3/src/chaind3.rs` that
carries only this hook. With the scenario off it behaves exactly like the signed file: a 25-block
seed-77 run is byte-identical to the unmodified binary. The run also writes
`keys-outcomes-NN.json`, nearcore's stored outcome tree for every step.

```
NEAR_SUCCESSOR_SCENARIO=keys near-arena-oracle-v3-successor gen --domain d3 --seed 6151 --chains 1 \
  --blocks 280 --mutate-every 10 --code-mutant-p 0.2 --ood-cap 2000 --min-gas-price 100000000 --out RUN
python3 tools/d3/collect_keys.py --source RUN --binary PATH_TO_ORACLE --out COLLECTED
```

The collector fails if a step is missing. A nonzero gas price is what makes the
insufficient-gas-key-balance step reachable; with the default zero price, that step is valid.
Evidence: `docs/evidence/lean-chunk-completion/key-family-fixtures/`.

## ML-DSA-65 scenario

Set `NEAR_SUCCESSOR_SCENARIO=mldsa` for the 47-step `mldsa` table (`src/keys/mldsa.rs`, labels
`successor.mldsa.NN.name`). It reuses the `keys` driver and accounts and adds three genesis accounts
and keys (ML-DSA-65 keys for `s1kdeleg` and `s1krelay`, `s2kmlpoor` with 1 NEAR, `s2kmlpk` with the
`kmlpk` contract whose `pk` method returns `signer_account_pk`). Steps: ML-DSA-signed transfers; bad
`z`/`c̃`; every malformed hint class (unordered, non-zero padding, count over ω, decreasing count);
an all-zero signature; wrong ML-DSA key; ED25519 and secp256k1 signatures on an ML-DSA key and an
ML-DSA signature on an ED25519 key; stale, too-large and strict-gap nonces; AddKey of ML-DSA full
and function-call keys then used to sign (including a call reading `signer_account_pk` and a
refund into the function-call allowance); ML-DSA-signed AddKey/DeleteKey; an ML-DSA gas key funded
exactly `gas_cost − verification cost`, then `gas_cost − 1`, then `gas_cost`; an account whose
balance is short by the verification cost, short by one, and exact; delegates with an ML-DSA
inner key (valid, bad signature, malformed hints, stale nonce, type mismatches, wrong key, V2,
inner AddKey of an ML-DSA key then used, an ML-DSA relayer); a Stake with an ML-DSA key. Boundary
amounts come from nearcore's `tx_cost` at PV86 and the tip gas price; the verification share is the
cost difference against the same transaction with an ED25519 key. aws-lc's ML-DSA signing is
randomized, so two runs of a seed differ in signature bytes (and everything hashed over them).

```
NEAR_SUCCESSOR_SCENARIO=mldsa near-arena-oracle-v3-successor gen --domain d3 --seed 6151 --chains 1 \
  --blocks 300 --mutate-every 10 --code-mutant-p 0.2 --ood-cap 2000 --min-gas-price 100000000 --out RUN
python3 tools/d3/collect_keys.py --scenario mldsa --source RUN --binary PATH_TO_ORACLE --out COLLECTED
near-arena-oracle-v3-successor mldsa-vectors > crate-vectors.json   # the Lean unit pin's crate verdicts
```

Evidence: `docs/evidence/lean-chunk-completion/mldsa-fixtures/`.

## Yield and storage-limit scenarios

`src/chaind3.rs` is a versioned copy of the signed D3 loop with one per-height hook for scenario
transactions (`src/scenarios.rs`); quiet scenarios also skip baseline traffic. Without
`NEAR_SUCCESSOR_SCENARIO` (and with `global-cache`) the output is byte-identical to the previous
sources (checked on seed 7, two chains, 40 blocks, `--mutate-every 10`).

* `NEAR_SUCCESSOR_SCENARIO=yield`: 36 scheduled `promise_yield_*` steps on `s0yield` / `s1ycall` /
  `s2ynote` with the `yieldc` contract (WAT in `scenarios.rs`), on top of baseline traffic: resume in
  the same receipt, same chunk and a later chunk; timeouts; duplicate resumes (same receipt, same
  chunk, after completion, after timeout); wrong and malformed data ids; 1,024/1,025-byte payloads;
  cross-shard triggers and callback-emitted cross-shard receipts; `_with_id` create/duplicate/resume;
  a returned yield; a panicking callback; create-then-fail rollback; a resume in the chunk whose
  timeout loop resolves the same yield, and one in the next chunk (timeout cancelled). Every chunk
  that ran `yieldc` gets the full mutant set. Needs at least 250 blocks for the timeouts.
* `NEAR_SUCCESSOR_SCENARIO=storage-limits`: a quiet chain (no baseline transactions or injections).
  Shard of `s0zlim`: nearcore-driven binary search over one value length (`pad`) for the exact
  `per_receipt_storage_proof_size_limit` flip, then below/at/above, repeated-read, panic and
  removal+reinsertion variants (second search). Shard of `s1zsoft`: the same for the chunk soft
  limit (an incoming receipt in the probe chunk is executed or delayed), failed receipts, several
  delayed local/incoming receipts, and yield-timeout resolution 256 B below/above the soft boundary.
  Shards of `s2zmisc` / `s3zcode`: deletion/reinsertion, 29 removals, rollback, repeated reads and a
  1.5 MB contract deployed and called next to a 3.99 MB read. Needs about 300 blocks; use
  `--p-missing 0`. Only the final at/above chunks get (non-drop) mutants.

Both write `scenario-<chain>.json` with nearcore's outcome tree of every scenario transaction and
every search probe. `tools/d3/collect_successor_scenarios.py --source RUN --out MANIFEST` checks the
intended semantics against those outcomes and maps steps to cases; `select_successor_fixtures.py`
copies the mapped cases. Commands, seeds and results:
`docs/evidence/lean-chunk-completion/{yield,storage-limit}-fixtures/`.

## Cross-family scenarios

`src/xfam.rs` adds five opt-in scenarios on dedicated genesis accounts, next to the unchanged
baseline traffic. Contracts are `xfam` (WAT in `xfam.rs`: yields, a gas-heavy `burn` made of
empty-input `sha256` calls, promise emission with optional rollback, init methods) and `xcurve`
(generated from `CURVE_HOSTS`: every curve host with memory, register, out-of-bounds,
promise-result-memory and promise-result-register input, plus `then`/`then2`/`thenx`/`yield`
dispatchers). Labels are `successor.<scenario>.NN.name` and say what was submitted.

* `yield-congestion`: yields created, resumed and timed out while the yield shard's delayed queue is
  non-empty. Two floods of `burn` receipts (offsets 4–13 and 194–205) exhaust the chunk gas
  limit, so run it on the low-gas-limit chain shapes (`--first-chain 3|4|8|9`). It includes a 200 KB
  cross-shard resume trigger that the bandwidth scheduler buffers, a resume after 360 KB of
  own-shard receipts, and a resume whose yield's timeout is due but deferred. Needs 235 blocks.
* `yield-congestion-v2parent`: `yield-congestion` on a genesis layout rebuilt as V2 with an identity
  split map (`d3gen::genesis_layout`), so the layout carries `shards_parent_map` with every shard its
  own parent, like mainnet's unsplit shards since PV75. Bandwidth requests then chain each shard's
  own buffer twice (`congestion_control.rs:545-554`). Same steps, labels and chain shapes as
  `yield-congestion`. Evidence: `docs/evidence/lean-chunk-completion/signed-valid-rejects/v2-parent-map/`.
* `curve-callbacks`: the `curve-hosts` inputs (first pos/neg/edge and the gas-exhaustion input of
  each host), called from `promise_then` callbacks (callback arguments, promise result in memory and
  in a register), a three-promise chain, a callback after a cross-shard promise, yield callbacks
  resumed in the same receipt or by a later cross-shard transaction, and register/out-of-bounds
  input for the BLS writers.
* `genesis-tx`: transactions submitted before the first block at three heights, so that the first
  chunks after genesis carry them. Every genesis-B2 case gets the full mutant set plus
  `g.*` mutants (`xfam::genesis_mutants`): a transaction placed into the genesis chunk's empty
  list, inconsistent `tx_valid` flags, `genesis_chunk_extra` removed (claim discipline) or altered
  (derived expectation).
* `gaskey-target`: gas-key funding, nonce-index transactions, withdrawal, transfer out and deletion
  with a balance, by receipts on a shard other than the signer's (including CreateAccount receipts
  that add, fund and delete a gas key, or delete the account), with ordinary receipts in the same
  chunks.
* `rollback-refund`: four rounds, each submitted at one height from one shard, so that one chunk
  of the target shard applies all of these together: a failed deterministic state init (missing
  global code, and insufficient deposit), a state init that then emits receipts, a CreateAccount
  with UseGlobalContract whose init fails, local deploy+init success and failure, emitted receipts
  that are rolled back by a panic, emitted receipts to a failing callee, and deposit refunds.
* `runtime-errors` (W03, contracts in `src/rterr.rs`): a quiet chain (no baseline traffic or
  crafted injections). Its 101 steps call modules whose instance layout does not fit Wasmtime's
  pooling allocator (`LoadingError`), and three shapes at nearcore's last fitting global count and
  at one more. They also call modules with an unknown `env` import (including `burn_gas`,
  `sleep_nanos`, `sandbox_debug_log` and `finite_wasm_gas`) or a wrongly typed host import
  (`LinkError`), and imports that preparation rejects (`PrepareError::Instantiate` / `Memory`).
  The calls come directly, cross-shard, from `promise_then` chains, with too little gas for the
  loading fee, with a missing method, in multi-action receipts, and after in-chain deployments
  (deploy+call in one receipt, then deploy alone, then a call). The setup's cache warm-up
  tolerates the contracts that fail preparation; it caches their compilation error, as nearcore
  does.

Without `NEAR_SUCCESSOR_SCENARIO` none of this code changes the output (the hooks return early and
use no RNG). Relevant chunks get the full mutant set. `NEAR_XFAM_MUTATE_EVERY=k` keeps one in k of
them (genesis-B2 chunks always), and drop-each-node mutants for every second kept chunk. Each run
writes `xfam-<chain>.json`: every scenario transaction with nearcore's outcome tree, the
shard map and every chunk header's congestion info and bandwidth-request count.

```
NEAR_SUCCESSOR_SCENARIO=yield-congestion NEAR_XFAM_MUTATE_EVERY=4 near-arena-oracle-v3-successor gen --domain d3 \
  --seed 101 --first-chain 3 --chains 1 --blocks 235 --p-missing 0 --mutate-every 0 --code-mutant-p 0 \
  --ood-cap 100000 --drop-cap 12 --out RUN
python3 tools/d3/collect_xfam.py --source RUN --out COLLECTED
```

The collector fails if a planned step was never submitted, an honest witness was rejected, or a
family's defining condition fails, for example no yield receipt applied while the delayed queue
was non-empty. Evidence and the other commands:
`docs/evidence/lean-chunk-completion/cross-family-fixtures/`.

## Legacy ETH wallet scenario (`eth-wallet`, row L0-D3-006)

`NEAR_SUCCESSOR_SCENARIO=eth-wallet` (`src/xfam.rs` `eth_wallet`, `src/ethwallet.rs`) adds these
genesis accounts:

* four ETH-implicit accounts whose contract is a legacy wallet magic hash (mainnet, testnet,
  testnet pv70 and localnet magic bytes, as `actions.rs:251-270` wrote them before PV83, with no
  access key);
* an ETH-implicit account with local `xfam` code, and one with no code;
* a named account holding the mainnet magic bytes;
* relayers `s1ewr`/`s2ewr`/`s3ewr`, the deployer `s3ewg` and the callee `s2ewc` (`xfam`).

`s3ewg` deploys the localnet wallet as a global contract by hash. Then, in 12 rounds, relayers call
`rlp_execute` with EIP-2930 transactions signed by each wallet's key (EVM chain id 399): transfers,
function calls through the wallet, and plain transfers to another wallet. The rounds also send
failing calls and direct `get_nonce`, and call the controls. `NEAR_XFAM_VARIANT=eth-wallet-predeploy`
instead calls the wallets with no global wallet deployed. nearcore's own validator rejects those
chunks, and the shard stalls, so use about 12 blocks. The scenario skips `t.chain_id` mutants,
because the redirect target depends on the chain id, and it does not warm the compiled cache with
the wallet. `tools/d3/collect_xfam.py` checks the family facts (`check_eth_wallet`). Evidence:
`docs/evidence/lean-chunk-completion/eth-wallet-fixtures/`.

## Codec normalization probes

`codec-roundtrip KIND HEX` decodes and re-encodes actual pinned-nearcore types. Supported kinds:
`action`, `signed-transaction`, `signed-delegate`, `state-init`. Successful output includes canonical
hex, and transaction/delegate hashes or the derived deterministic account ID where applicable.
These are codec probes; zero placeholder signatures are not asserted cryptographically valid.

`python3 tools/d3/gen_global_codec_vectors.py --binary PATH_TO_ORACLE --out FILE` generates 12
independent vectors covering reversed and duplicate StateInit map entries (last value wins, sorted
canonical encoding), stable derived hashes, and malformed/trailing input. Expected byte layouts are
also independently constructed in Python and compared with Rust output.

## Shard-split fixtures (`reshard`)

`near-arena-oracle-v3-successor reshard --seed S --out DIR [--chains K] [--first-chain I] [--blocks N]
[--split-k k] [--variant v] ...` runs `src/reshard.rs`. The genesis is PV85 with a static layout,
and PV86 enables dynamic resharding with a forced split of the shard of `s{k}a00`. nearcore's own
`proposed_split` → `shard_split` → `split_shard` path then runs. Every witness goes to
`DIR/cases/<case>`, with nearcore's pre-validated implicit transitions and the boundary shape in
`meta.json`. Split, layout and split-gate mutants go to `DIR/mutants/`. The D3 classifier is not
used. Commands, seeds and results are in
`docs/evidence/lean-chunk-completion/resharding-fixtures/README.md`.

Further options (all off by default; with none of them the output is unchanged):

* `--second-split SID` also forces the split of `SID` (a child of the first split), so a child splits
  again; `--max-shards M` overrides `max_number_of_shards`.
* `--no-force --mem-threshold T --min-child C`: no forced split; nearcore's thresholds decide.
  Every split-gate case records nearcore's own `total_mem_usage` and `find_trie_split` on the main
  transition's pre-state trie (`gate_probe`), and a gate that did not split gets the mutant
  `h.proposed_split_unmet_threshold` (the split `find_trie_split` would give).
* `--starve SID:E`: from the first post-split epoch, shard `SID`'s chunks are not produced for `E`
  epochs, so the next witness walks back across several epoch starts (and layout changes).
* `--zlim`: the split shard holds `s{k}zlim` (the storage-limit contract); the parent's chunk of
  the resharding block runs a receipt above the per-receipt storage-proof limit and one the chunk
  soft limit postpones.
* `--p-global-hot P`: global-contract deployments in the hot window, whose distribution receipts
  cross the split buffered and delayed.

Evidence: `docs/evidence/lean-chunk-completion/resharding-fixtures-2/README.md`.

## Fuel-stress scenario (W02)

Set `NEAR_SUCCESSOR_SCENARIO=fuel-stress` for a quiet chain with the `fuelc` contract
(`scenarios::fuel_wat`) on `s0fuel` and `s1fuel`, and 16 FunctionCalls (`fuel_schedule`): the
cheapest instruction burning 300 Tgas (`nops`, `spin`), loops of 200 and 4,999 empty `block`s
(zero finite-wasm fee, so the most interpreter steps per unit of gas), recursion to the stack
limit (empty frames and 1,000-local frames), 2,048 pages with 128 MiB fill and 64 MiB copy, a
64 MiB fill loop, loops of `sha256(64 KiB)`, `used_gas` and `memory.grow(0)`, a 10^7-iteration
counted loop that succeeds, and three 300 Tgas calls in one chunk. `scenario-<chain>.json` holds
nearcore's outcome tree for every call. `tools/d3/collect_fuel_stress.py --source RUN --out
MANIFEST` maps each call to the case that validates it.

```
NEAR_SUCCESSOR_SCENARIO=fuel-stress $B gen --domain d3 --seed 2026 --chains 1 --blocks 45 \
  --p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --out RUN
```

Evidence: `docs/evidence/lean-chunk-completion/fuel-termination/`.

## Eval-time scenario (W02 arcs)

Set `NEAR_SUCCESSOR_SCENARIO=eval-time` for a quiet chain with the `evalc` contract
(`scenarios::eval_wat`) on `s0eval` and `s1eval`, and 6 FunctionCalls (`eval_schedule`). Three run
at 300 Tgas: `blocks4999`, `deep4999` (4,998 pushed labels discarded by the back-edge) and
`midrun4998` (a `br_if` that lands mid-run). Three run at 3 Tgas: `blocks4999`, `pushpop4999`
(labels pushed and popped across a charged group) and `brif4999` (a `br_if` back-edge).
`tools/d3/collect_fuel_stress.py` maps each call to its case.

```
NEAR_SUCCESSOR_SCENARIO=eval-time $B gen --domain d3 --seed 2027 --chains 1 --blocks 30 \
  --p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --out RUN
```

Evidence: `docs/evidence/lean-chunk-completion/eval-time/`.

## Per-outcome nearcore observables (`NEAR_SUCCESSOR_OBSERVABLES=1`, W01)

With `NEAR_SUCCESSOR_OBSERVABLES=1`, `gen` and `reshard` also write
`nearcore-observables-<chain>.jsonl`: one record per honest witness, keyed by the sha256 of the
case's `claim.bin` and `witness.bin`. Each record comes from a separate cold validator runtime
(`src/observables.rs`). It pre-validates the witness with the needed code blobs and runs
`apply_new_chunk` as the stateless validator does. The record holds the execution outcomes (id,
executor, status with return value or receipt id or failure, gas, tokens, compute, logs, receipt
ids), the outgoing receipts the header root commits to (reassigned across a split as the validator
does), and the committed state changes with each change's cause. It also holds the outcome root
and the producer's stored outcome ids. The variable never touches the RNG, so the cases are
byte-identical with and without it (checked on seed 7, 30 blocks, `--mutate-every 10`).

`mainnet-observables --home HOME --exports EXPORTS --cases CASES --out FILE` reads the same fields
from a stopped node's database opened read-only (`src/mainnet_obs.rs`): stored outcomes, outgoing
receipts and state changes of each captured witness's main-transition block. `compute_usage` is not
persisted by nearcore, so it is reported as unknown.

`tools/mainnet-replay/full_observables.py` compares these records with the checker's
`--blind-full` output. Results: `docs/evidence/lean-chunk-completion/full-observables/`.
