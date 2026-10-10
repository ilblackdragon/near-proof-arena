# np-udr-stark-v2: Rust prover for the v3 succinct proof (work in progress)

The Rust prover for `np-udr-stark-v2` (`docs/zk-formal/FORMATS.md` §8):
v1's STARK (DESIGN.md §4) with **public segments** (bus messages read by the
verifier from the prepared statement) and **`auxGroup = g ∈ {1, 2, 3}`**
(`ZkFormal.V2.G.pg g`, V3-D0-DESIGN §5.3). The target AIR is the frozen
`ZkFormal.NearV3.Assembly.nearAirV3` (25 tables) at `g = 2`, verified by
`ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b`
(`docs/zk-formal/STATUS-V3-ASSEMBLY.md`).

Validity, not zero knowledge (as v1).

## Provenance

`source/` and `conformance/` are forked from `examples/np-udr-stark-fast2`
(the admitted, live rank-4 v1 prover, commit `2cadc9fb`), then `cargo fmt`
was applied to the whole crate (fast2 was not rustfmt-clean). To review the
v2 changes against fast2, format a copy of fast2 first and diff the trees.
The v1 NEAR generators (`src/near/`, `bin/prove`, `bin/prepare`) are still the
v1 ones; they are kept so the v1 conformance suite keeps running.

## Status

| piece | state |
|---|---|
| `auxGroup` | `Air.aux_group` (`Air::with_aux_group(g)`); `AuxLayout::new(t, g)`, `Table::{degree,aux_width,num_quot_chunks,num_finals}(g)` mirror `Table.auxCount/auxDegree/degree/quotCount g` and `chunksOf g` (`ZkFormal.Stark.Protocol`). |
| `np-air-v2` | `Air::from_json` reads v1 and v2 (`pubSegs`, `maxPub`), `Air::to_json` writes them byte-identically to `ZkFormal.V2.AirP.exportJson`. |
| reference verifier | `pub_fit`, `pub_msgs`, `pub_prod` (`PubSeg.count/startOffset/record/fits`, `pubFit`, `pubMsgs`, `pubProd`); bus equation `∏sends·Π_pub(true) = ∏recvs·Π_pub(false)` (`globalChecksP`), `pubFit` checked before any record is enumerated (as Lean's `okLens && pubFit && …`). The provers self-check with the same equation. |
| prover messages | unchanged from v1 (FORMATS §8.5): the v2 prover is v1's honest prover for `AP.toAir` at `pg g`. |
| `nearAirV3` | read from `np-lean-export-v3` (1,639,407 B, sha256 `73bcf1dd…`), validated, per-table layout equal to Lean's at g = 1, 2, 3. |
| trace generation for `nearAirV3` (witness → 25 tables) | **not started** (part 2; follows the Lean renders, `RenderV3Stmt`). |
| `prepD0`/hint codec in Rust, candidate package, build recipe, `formal/` model | **not started**. |

## Verification

* `cargo test --release` in `source/`: v1 suites unchanged plus `tests/v2.rs`
  (JSON round trip, layouts at g = 1/2/3, prove/verify at every g, proofs
  rejected under every other g, tampered claims, hostile counts/offsets
  rejected by `pubFit`, prover refuses an unbalanced claim).
* `conformance/run-v2.sh` (166 checks, all pass on 2026-10-10): the deployed
  Lean `ZkFormal.V2.verifierP Fp Fp8 AP (pg g)` (`np-lean-verify-v2`) accepts the
  Rust v2 toy proofs at g = 1, 2, 3 and logs 4/6/10, rejects them under every
  other `auxGroup`, rejects 9 proof mutations and 5 claim mutations each, and the
  AIR re-exports byte-identically; `nearAirV3` layouts equal at g = 1, 2, 3.
* `conformance/run.sh` (inherited v1 suite; 205 checks, all pass on the fork).
* `cargo clippy --all-targets -- -D warnings`: 50 findings, the same count as
  fast2 (inherited; none from the v2 changes).

`conformance/` needs a built `zk-formal/.lake` (it `require`s `../../../zk-formal`).
