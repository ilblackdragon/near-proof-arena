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
