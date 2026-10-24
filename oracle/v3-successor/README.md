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
