# Mainnet shard-13 diagnostic replay — 2026-10-25

**PASS for the captured single-shard diagnostic. Full W13 remains open.**

- 1,223 consecutive shard-13 chunks: heights 221489407–221490629, mainnet PV86.
- Native synchronous prevalidation/validation: 1,223 accepts, zero rejects/export failures.
- Lean `allFeatures`: 1,223 accepts, zero rejects, unsupported cases or runner errors.
- Mismatch: **0%**; replay coverage: **100%**; verified matches: **100%**.
- Lean replay elapsed: 161.04 seconds, four workers, 120-second per-case timeout.
- 279 captures report accessed contract code, spanning eight distinct code hashes; none report
  missing code. Raw witnesses total 15,215,689 bytes.

The native exporter constructs claims from the offline capture node's actual chain/epoch store
using the existing claim-v3 builder adapted from Client to Chain. It checks captured block bytes
against the canonical store and hashes exported code. Native validation uses a fresh transition
cache per case but retains the existing compiled-contract cache: this is **not cold-cache W13
validation**. Lean checks recomputed transition commitments; this run does not add the outstanding
W01 export/comparison of all internal observables.

This run is bound to the working-tree `allFeatures` checker, including the uncommitted source
changes retained in `working-tree.patch` relative to `git-head.txt`. The changes were not staged
as implementation by this task. Exact source hashes and frozen binary hashes are retained.
This is a current-state diagnostic, not a frozen release or a clean-HEAD claim.

`report.json` contains denominators, scope and identities. `results.jsonl.gz` retains every native
and Lean result; `inputs.json.gz` binds every input. `manifest.json` hashes the evidence files.
Runtime cases, binaries, node database and raw captures remain under
`/data/illia/nearproof-deps/mainnet-w13/` (`replay-cases/`, `replay-results/`, `exports/`, `home/`).
The native export binary is `/tmp/nearproof-neard-target/release/neard`; its full source diff was
saved under `replay-provenance/native-source.patch`. No node keys or database are committed.

Reproduce using [the diagnostic exporter and runner](../../../../tools/mainnet-replay/native/README.md).
Native release and Lean driver builds passed. Five offline diagnostic-report tests pass, including
wrong verdict, unsupported/missing case, malformed output, and preventing a single-shard diagnostic
from reporting a full W13 pass. No artifact changed during the run.

Remaining: all-shard representative coverage, independently validating supplied claim facts in the
cold native adapter, rare-feature fixtures, finality/authentication closure, and frozen-package
validation. The all-shard `make w13-gate` requirements were not weakened.
