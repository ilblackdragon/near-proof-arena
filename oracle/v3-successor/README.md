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
