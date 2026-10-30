# Lean chunk completion — item 10 (remaining W05–W07 shapes), 2026-10-29/30

Lane: item-10 fork of the W01/item-9 lane (worktree branch `worktree-agent-ad54daf2830fc99ec`, base
`4f07a7fdf`). Nearcore `44f7ae6c` (2.13.4), PV86, cold. Evidence:
`docs/evidence/lean-chunk-completion/remaining-shapes/README.md`.

## Outcome

| shape | status |
|---|---|
| curve hosts from timed-out yield callbacks | fixtures: 4 runs, 540 timeout callbacks, 1,500 verdict rows, 330 blind, 0 disagreements |
| BLS `version = 1` (NEP-488) | unreachable at PV86 (`155.yaml` = nightly PV155; `enable_all_features` is estimator-only); Lean implements version 0; the existing `edge.corner_0_2` fixtures cover the version-0 rejection |
| ML-DSA `z` at the norm bound | produced by the key holder with a FIPS 204 boundary signer; 40 vectors agree across aws-lc, Python and Lean; 4 runs, 2,150 verdict rows, 79 blind, 0 disagreements |
| mismatched distribution code identities | unreachable on valid chunks (both constructors keep `id`/`code` coherent; inputs bound by receipt proofs or the state root; mainnet genesis has no such receipt); 917 identity mutants + 110 honest = 1,027 rows over 8 seeds, 0 disagreements; Lean rejects them at the receipt proof, before its identity guard |
| state init then a successful emit | fixtures: 4 runs, 23–24 successful post-init emits per run, 1,595 verdict rows, 281 blind, 0 disagreements |

No Lean semantic change. The checker binary after all control builds is byte-identical to the base
build (`a1627ea3…`), so the corpus, fixture and 3,138-case census verdicts cannot move.

## What was done

1. Generators (`7f6786eb4`): opt-in variants in `oracle/v3-successor`.
   * `NEAR_XFAM_VARIANT=curve-yield-timeout` and `state-init-emit` (`xfam.rs`).
   * `NEAR_MLDSA_BOUND_SIGNER` (`keys/mldsa.rs`, steps 47–52).
   * `NEAR_DIST_MUTANTS` (`d3.rs`).
   * `mldsa-vectors --check`.
   * `tools/d3/mldsa65_bound.py`.
   * `spec/lean/v3/MlDsaCheck.lean`.

   Baseline byte-identity: 8,547 files, `diff -r` empty.
2. Runs: 20 generator runs under `/data/illia/nearproof-deps/w10-runs/runs`.
   * `cy601–604`, `se701–704`, `mb1618/2718/31415/6151`.
   * `gd811–814` (first dist-mutant version, superseded) and `gdb811–818`.
   * `bl-base` / `bl-final`.

   Every run was made with `NEAR_SUCCESSOR_OBSERVABLES=1`, so `nearcore-observables-*.jsonl` exists
   for item 9. Every honest witness was cold-accepted by nearcore.
3. Replays with `tools/d3/replay_successor.py` at `allFeatures`, and blind replays with
   `blind_corpus.py`. After the coordinator's request, these ran at `--jobs 2`.
4. Controls: four checkers, one deliberate bug each, built by `ctl.py`. All are detected:
   * C-M: 8 rows, plus 16/16 vectors.
   * C-S: 4 honest chunks.
   * C-Y: 56 honest chunks.
   * C-D: see the README.

   The first C-D build patched only `RuntimeCore`. The widest tier runs `ReshardCore`, so that
   control had no effect: 140/140 still agreed. It was rebuilt with the `ReshardCore` copy patched
   as well; the ineffective run is kept, not counted.

## Measured vs carried over

Every number in the README was measured in these runs, except the cross-references to earlier
families (`curve-host-fixtures` corner steps, `yield-congestion` deferred timeouts), which are
carried over from their READMEs.

## Open

* The replays sample mutants: curve every 16th, state-init-emit every 8th, ML-DSA every 2nd for
  three seeds. All honest chunks are replayed.
* No timeout callback that falls due while the compute limit is exhausted runs a host.
* A malformed distribution in a custom genesis `DelayedReceipt` is not excluded by nearcore. It is
  outside the mainnet claim, and Lean keeps it out of domain.
* `mldsa-fixtures/README.md` §6 still says a `z` at the bound "cannot be produced without forging".
  This README supersedes it. That file was not edited, because it belongs to another family's
  evidence; the integrator can update it.
* Host: load average 130–240 throughout. Wall times in `generation.json` reflect that.
