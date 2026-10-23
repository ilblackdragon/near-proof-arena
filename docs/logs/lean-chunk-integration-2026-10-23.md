# Lean chunk progress integration — 2026-10-23

This is a progress checkpoint, not certification of Gate A, B or C. Integrated from `d196f0339`
in `/data/illia/nearproof-wt/lean-chunk-integration`. Lane branches/worktrees and all uncommitted
lane changes remain intact. Historical lane logs describe their original snapshots; this record
supersedes their merged/pending status only for the exact tips below.

| Lane | Committed tip | Integration status and remaining work |
|---|---|---|
| L0 | `1d242e6c2` | Merged inventory/boundary analysis; unresolved questions remain. |
| L1 | `a5ef42e0c` | Already on main; capacity and successor obligations remain. |
| L2 | `2816a0882` | Merged float implementation and recorded replay; broader generated whole-chunk coverage and chunk-level agreement proof remain. |
| L3 | `51ddfaff1` | Merged ecrecover/p256 arithmetic, host layer and tests; not wired into the accepted chunk path, other crypto families remain missing. |
| L4 | `41b98f2bd` | Merged additive codecs, resolution and action bodies; no existing chunk dispatch is enabled, whole-chunk validation remains open. |
| L5 | `a98bd9965` | Merged storage-bound analysis/proofs; protocol accounting and boundary tests remain open. |
| L6 | `df9112f88` | **Not merged.** The lane's uncommitted GenesisD3 correction documents 307 header mutants wrongly accepted by the committed checker. Keep the correction and validation in the lane; review its next committed checkpoint before integration. |
| L7 | `0cf6f3491` | Merged committed corpus manifests, harness and evidence; subsequent uncommitted audit/harness updates remain in the lane. |
| L8 | `a5ef42e0c` | No additional committed work; admission remains open. |

## Integration changes

- Regenerated the combined coverage inventory rather than choosing one lane's generated JSON.
  L2's current rows take precedence over matching historical L0 supplement rows; all 219 IDs are unique.
- Preserved L3's partial host statuses, and corrected float evidence wording to distinguish the
  focused d3c9 tests from the full replay. Static inventory descriptions of other unfinished lanes
  do not certify their additive modules as accepted paths.
- Added CryptoDomain, CryptoHost and GlobalContractExec to the root import closure. L2 and L5
  root imports are both retained. No L6 module is imported or merged. The review-only branch
  `integration/lean-chunk-progress-20261023` contains the rejected L6 merge and must not be
  promoted; `integration/lean-chunk-ready-20261023` is the accepted integration branch.
- Preserved the old checker entry point and signed oracle pins. Successor extensions remain
  separate entry points; this integration is not a release or live admission.

## Validation

Checks on the combined tree (fresh integration worktree; no copied or hard-linked Lean cache):

- `cd spec/lean/v3 && lake build`: PASS, 182 jobs. Additive L3/L4 modules are in the root closure.
- Core plus changed logged-execution theorem audit: 201 theorem axiom reports, only `propext`, `Classical.choice`, `Quot.sound`
  (or no axioms). Reproduce with `lake env lean ../../../docs/evidence/lean-chunk-integration/AllAxioms.lean`
  from `spec/lean/v3`; source and output are archived under `docs/evidence/lean-chunk-integration/`.
- Changed `NearSpecV3.Logged.WasmStepE` closure: PASS (fresh build, including its host-call dependency).
- Oracle driver build: PASS, 187 jobs (`nearspec-v3-wasm`, `check-d3`, `check-d3f`, float and crypto test executables).
- Fresh crypto executable: ecrecover 161 vectors / 20 edge / 23 host cases; p256 17 vectors/gates /
  13 host cases; zero failures in all five modes.
- `difftest_float.py --cases 4 --seed 1`: 79,742 comparisons over 70 opcodes, zero disagreements.
  This is an integration smoke rerun, not a replacement for the lane's four-seed campaign.
- `chunk_float.py --sample 4 --tamper-dir /tmp/lean-chunk-integration-tamper`: 3 float-blocked
  chunks lifted, 1 still excluded for ETH-implicit local-contract handling, 12/12 mutants rejected.
- `python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json`:
  PASS, 18 families; D1 53,048 / D2 67,384 / D3 115,284. This verifies content, not execution.
- Harness unit tests: 28/28 PASS. Coverage regeneration/drift check: PASS, 219 unique IDs.
- `make pin-check`, `git diff --check`, L7 shell syntax check: PASS.

Historical long corpus runs are carried forward from lane logs, not claimed as fresh full replays
of this integration. No live admission or Gate B/C completion is claimed.

## Continuing lane work

Continue committing in existing lanes. Rebase or merge main when ready, reconciling shared
`NearSpecV3.lean` and `tools/d3/lean_chunk_coverage.py` changes; regenerate the coverage JSON.
Do not restore stale generated inventory snapshots. L6 has no merged ancestry and can deliver its
corrected checkpoint normally. L7's newer uncommitted work was deliberately not snapshotted here.
