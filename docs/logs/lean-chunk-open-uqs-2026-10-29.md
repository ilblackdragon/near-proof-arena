# Open UQs, versioned schema, environment assumptions — lane log (2026-10-29)

Workplan items 8 (UQ-002, -003, -004, -007, -013, -015, -016, -017 and the versioned claim/witness
schema; UQ-001 belongs to another lane) and 12 (environment assumptions). Evidence:
[open-uqs/README.md](../evidence/lean-chunk-completion/open-uqs/README.md).

| field | value |
|---|---|
| worktree / branch | `.claude/worktrees/agent-ae751a39c6ba20b86` / `worktree-agent-ae751a39c6ba20b86` |
| base | `4f07a7fdf` |
| target | nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86 |
| not edited | `LEAN_CHUNK_COMPLETION_WORKPLAN.md`, `HANDOVER.md`, `lean-chunk-coverage.json`, `spec/claim-v3.md` (pinned by digest in the signed challenge) |
| `make pin-check` | ok |

## What was done, in order

1. **Read the register and the sources.** Several UQs were already answered in code by later lanes
   and only lacked a disposition with a test: UQ-002 (pipeline rule), UQ-007 (proof), UQ-015 (proof
   modulo a hypothesis), UQ-017 (genesis branch). The register text in
   `lean-chunk-w00-owner-map.md` is the integrator's to update.
2. **UQ-004, UQ-007 pins.** Two scripts recompute the pinned values from nearcore itself (YAML diffs
   + `CONFIG_DIFFS` + `parameters.snap`; the embedded wallet wasm) and compare with Lean. 32/32 and
   7/7; each has a `--break` control.
3. **UQ-016.** Static producer/consumer check over all 30 `pushAction` sites. First run flagged the
   two signed-only `OTHER` sites (a bug in the branch detector: the `else` and the `if` are at the
   same indentation); fixed, re-run clean; injected-tag control fails as it must.
4. **Item 12 / UQ-003.** No aarch64 host and no cross toolchain. Built a probe crate with
   `wasmtime = 45.0.0` and nearcore's exact engine configuration, cross-compiled it to
   `aarch64-unknown-linux-musl` (rust-lld; wasmtime's one C file compiled with clang and a stub
   `stdlib.h`), and ran it under QEMU 8.2.2 user mode from the extracted Ubuntu package. Calibrated
   first on x86_64: the probe reproduces the pinned harness's three boundaries exactly. aarch64 gives
   the same three numbers; a +64 B pool control moves each by 4. The same probe ran 5,920 float calls:
   bit-identical across x86_64/Winch, aarch64/Cranelift and the Lean float kernel; turning
   canonicalisation off produces 2,496 violations (control).
5. **UQ-013.** Measured with 2,348 single-fact mutants of 240 honest chunks (4 seeds). A first run
   had 6 spurious rejects on every field: case names repeat across corpora and the mutant dirs
   collided. Fixed (corpus-qualified names) and re-run; the table in the evidence is the second run.
   Disposition is a decision; proposal A1 is written down, not adopted.
6. **UQ-015, UQ-017.** Source arguments (partial-storage retrieval, missing-chunk early return; the
   genesis comparison set) plus runs: signed tier on 88 storage-limit fixtures, `allFeatures` on the
   266 genesis-main corpus chunks.
7. **Versioned schema.** `spec/claim-v3.md` is pinned by digest in the signed challenge, so the
   envelope is specified in a new `spec/claim-v3-versioning.md`. Lean: `Successor/SchemaVersion.lean`
   (normaliser + `checkVersioned`, theorems for the legacy rule and faithfulness, allowed axioms),
   used by `MainSuccessor.lean` on every non-signed tier. Python: `tools/d3/claim_schema.py`, a unit
   test, and two CI steps in `difftest-gates`.

## Measured vs carried over

Measured here: every number in the summary table of the evidence README except those marked
*carried over* (pipeline-rule control 89, float whole-chunk families, curve-host 111/111, exact
recorder flips, yield/promise agreement, cross-family genesis negatives, pinned-harness boundaries).

## Left open, with reasons

* **UQ-013** needs the user's decision (admission contract A1 or an in-relation authentication).
* **UQ-007** has no whole-chunk fixture with a pre-PV83 legacy-wallet account: the generator cannot
  create one at PV86 without a genesis-records scenario. Covered by proof and pins only.
* **aarch64** is excluded by statement: trap classification, native stack use, compile-time limits,
  real silicon and whole-chunk replay were not measured.
* The UQ register rows and the workplan table are not edited here (integrator-owned files).
