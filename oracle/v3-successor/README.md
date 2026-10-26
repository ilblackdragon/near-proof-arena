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
