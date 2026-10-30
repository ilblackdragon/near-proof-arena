# Lean proof debt (workplan item 11) — 2026-10-29

Lane: item 11 of `docs/requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md` (float overlap/range W04, split
correctness and authentication W11, `WitnessLift`, wider kernel non-vacuity, `Logged.API`/`D3LSpec`).
Worktree branch `worktree-agent-ab18ad53358787ddb`, base `4f07a7fdf`. Evidence summary:
[`docs/evidence/lean-chunk-completion/proof-debt/README.md`](../evidence/lean-chunk-completion/proof-debt/README.md).

## Commits

| commit | content |
|---|---|
| `ebb151685` | `Logged.API`/`D3LSpec` repaired; `NearSpecV3.Logged.Audit` added to `defaultTargets` |
| `81d6cb079` | W11: `NearSpecV3/ReshardingProofs.lean` |
| `30d534b85`, `d166197c9`, `9ea617df8` | W04: `NearSpecV3/Wasm/FloatRange.lean`; guarded audit `NearSpecV3/ProofDebtAudit.lean` |
| (this commit) | wider kernel non-vacuity `Examples/RealCaseD3Wide*`, generator `--name`, evidence, this log |

## 1. `Logged.API` / `D3LSpec` (repaired, now in the default build)

Cause of the rot, found by building `NearSpecV3.Logged.API` from a clean cache:

1. `St` gained `globalActions` and `curveHosts`. The `se` simp set had no `E_globalActions` /
   `E_curveHosts`, so `E_enter` (`WasmStepE.lean:185`) left `(E σ s).globalActions` unreduced.
   Fixed by the two `rfl` lemmas in `WasmCR.lean` and adding them to the simp sets.
2. `callHost` now dispatches through `dispatchArm` (signed `hostCall` plus the W05 curve hosts) behind
   a guard that also reads `globalActions` (`WasmStepE.lean:200`). New `Logged/WasmCRCrypto.lean`
   proves every `cryptoHostCall` arm commutes with the store erasure `E σ` (`CR_cryptoHostCall`,
   14 arms, by the existing `cr` tactic) and lifts that to `CR_dispatchArm`. `callHostL` mirrors the
   new guard.
3. `runCall` seeds `St.curveHosts := cfg.curveHosts`, and `functionCall` now calls
   `runCallWithLimits` (instance-loading preflight). `runCallL` seeds `curveHosts` too; the new
   `runCallWithLimitsL` (+ `runCallWithLimitsL_spec`) mirrors the preflight, `functionCallL` calls
   it, and the `D3LSpec` tactics generalise `runCallWithLimits` instead of `runCall`.

No theorem statement changed. To stop silent rot, `NearSpecV3.Logged.Audit` (guarded
`#print axioms` of the headline theorems) is in `defaultTargets`, which the CI `lean` matrix job
builds for `spec/lean/v3`; any break in the spine or a new axiom fails CI. Not retired: the spine is
live (`Successor/{Queue,Global,Storage}Execution` import `Logged.D2*`, `oracle/wasm-d3/lean` and
`research/near-compression` import `Logged.API`/`WasmRun`).

## 2. W11 — split correctness, partition, authentication (proved)

`NearSpecV3/ReshardingProofs.lean`. Structure: lexicographic lemmas on nibble keys
(`append_lt_iff_of_not_prefix`: extending a key that is not a prefix of a boundary does not cross
it), hence `retainDecision`'s `retainAll`/`discardAll` are sound for every key in the subtree; lookup
lemmas for the squash helpers (`extendChild_get`, `squashBranch_get`); then a mutual structural
induction over `PTrie`/`Kids` for `retainSplit_get`. The partition is two adjacent half-open
intervals (`inRange_adjacent`) with `c ≤ c‖b < c+1` (`toNibbles_boundary_lt`, needs `c < 255`,
discharged for the table by `allColumns_id_lt`). Authentication is a second mutual induction:
`retainSplit` commutes with `PTrie.refinedBy` (the existing NearSpec refinement order, which
preserves `hashOf`), tracking `memory_usage` because the squash recomputes it from retained
children.

## 3. W04 — float fuel and range (proved); overlap (not attempted)

`NearSpecV3/Wasm/FloatRange.lean`. The L2 log's "`bitLen`'s 4096 fuel bounds every operand" is now
`bitLen_spec` plus per-operator operand bounds; `isqrt`'s 64 steps are `isqrt_spec` (below
`2^128`). Range: `roundPackS_lt` shows the rounding never hands the encoders more than `p`
significand bits (subnormal grid, exact, rounded, carry), so every rounded result is a `w`-bit
pattern. `add_lt`/`sub_lt` (aligned operands below `2^(p + 2^eb)`, `decode_e_bounds`), `mul_lt`,
`div_lt`, `sqrt_lt`, `min_lt`, `max_lt`, `roundToInt_lt`, `convertInt_lt`, `demote_lt`,
`promote_lt`, `truncSat_lt` cover every value-producing operator: `w`-bit inputs give `w`-bit
results. **Not attempted:** chunk-level float overlap (`checkD3` vs `checkD3F` on float-free chunks)
— it is tier obligation O1, owned by the sibling W12 lane (`Successor/TierMono.lean`), and
duplicating it would conflict. Agreement with nearcore remains measured, not proved.

## 4. `WitnessLift` (open)

See the evidence README §4. Summary: the identity lift `w2 = w` is the natural witness (both
checkers decode the same `ChunkStateWitness` bytes; the D1 decoder is a restriction), so the lift
reduces to `RelD1a B cb w → RelD3 cb w`, i.e. `D1 ⊂ D2 ⊂ D3` on identical bytes. Only `D0 ⊂ D1` is
proved. Each remaining inclusion is a phase simulation of the `D0SubD1` kind but several times
larger (D2's runtime has actions, queues, congestion, bandwidth, fees; D3's step needs "success never
dispatches the `FunctionCall` hook"). Not attempted in this lane; still tested-only.

## 5. Wider kernel non-vacuity

KERNEL_LOG_PLACEHOLDER

## 6. Axiom audit (`#print axioms`, measured on this branch)

```
-- NearSpecV3.ProofDebtAudit (guarded, default build) and Logged.Audit (guarded, default target)
'NearSpecV3.retainSplit_get' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.retainSplitKids_get' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.splitChild_get' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.splitKey_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.allColumns_id_lt' does not depend on any axioms
'NearSpecV3.retainSplit_refinedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.splitRootE_refinedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.bitLenF_spec' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.bitLen_spec' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.bitLen_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.isqrt_spec' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.neg_lt' depends on axioms: [propext]
'NearSpecV3.Wasm.abs_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.copysign_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.specials_lt' depends on axioms: [propext]
'NearSpecV3.Wasm.encodeNormal_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.encodeSub_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.roundPackS_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.add_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.div_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.sqrt_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.min_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.max_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Wasm.roundToInt_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.convertInt_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.demote_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.promote_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.truncSat_lt' depends on axioms: [propext, Quot.sound]
'NearSpecV3.Logged.W.E_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.W.CR_dispatchArm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.W.callHostL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.W.runCallWithLimitsL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.W.runUntil_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.W.runL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.checkD2L_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.checkD3L_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.checkD3Reads_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.checkD3_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.reads_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Logged.reads_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 7. Host conditions

The host was oversubscribed (load average 140–170 on 32 cores; `zkbuild.slice` at its 42.9 GB
`MemoryHigh`, CPU weight 50). Small proof checks were run as plain `lean` against the built oleans in
a 6 GB `systemd-run` scope (normal CPU weight) — each took 1–3 s; kernel runs went through `heavy`
(40 G), one module per `decide +kernel`.
