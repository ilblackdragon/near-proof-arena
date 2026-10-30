# W02 fuel sufficiency theorem — lane log, 2026-10-29/30

Workplan item 3. Evidence: `docs/evidence/lean-chunk-completion/fuel-sufficiency/README.md`.

## Done

- New module `spec/lean/v3/NearSpecV3/Wasm/FuelSufficiency.lean` (~1,640 lines), added to
  `defaultTargets`. It contains no `sorry` and changes no definition.
- The potential argument for `Wasm.run` under `wasmFuel` is proved: `step_dec` → `run_stable` /
  `run_from_step` → `callEntry_stable` → `runCallWithLimits_stable` → `wasmFuel_sufficient`.
- It is proved relative to two explicit hypotheses:
  - `HostsOK`: a host keeps the frames and the prepaid gas, and does not raise `remaining`. Open.
  - `CodeCertified`: every prepared function passes the decidable certificate `certOK`. Open in
    general. The census over 76,144 functions in 19,674 prepared modules (corpus and evidence
    witnesses, 4 `gen_d3a` seeds, `opcases`) found 0 failures. The breakage control, which
    under-charges every charge point by one `r`, flags 19,635 modules.
- O-W1b and O-W2 (every `exec` arm) are proved. O-W3 is a certificate check. The runtime half of O-W4
  is proved; its static half (finite-wasm `optimize` correctness) is `CodeCertified`.
- No obligation was found false, so `wasmFuel` is unchanged and no verdict can move.
- Tools: `oracle/wasm-d3/lean/FuelCert.lean` (`nearspec-v3-fuel-cert`, `--break`) and
  `tools/d3/extract_witness_wasm.py`.
- `make pin-check`: ok.

## Axiom audit (`lake build NearSpecV3.Wasm.FuelSufficiency`)

```
'NearSpecV3.Wasm.step_dec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.run_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.run_from_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.callEntry_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.callEntry_run_from_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.runCallWithLimits_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Wasm.wasmFuel_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Notes

- Tier scope: `allFeatures` (successor `wasmFuel`) only. The signed `legacyFuel` is item 6b.
- Dead code must be exempt from the certificate's fee check. finite-wasm emits charge points in
  unreachable regions (an adjusted loop header after `br`) whose fee does not cover the dead group.
- `exec_fin_gas` needs `maxHeartbeats 4000000` (47-arm case split). A cold build of the module took
  several minutes on the loaded host (load average around 280).

## Round 2 (2026-10-30): the three hypotheses discharged

- Merged main (`807f78b09`, fast-forward).
- **HostsOK proved**: `Wasm/FuelHost.lean`, `hostsOK`, one theorem per arm (75 + 14), using a port
  of the `Logged/WasmCR` `cr` approach (relation `HOR`, tactic `hr`). It was written by a delegated
  sub-agent and checked here; it compiles in about 93 s. No arm is non-monotone.
- **CodeCertified made a checked condition**: the successor's VM call is now `vmCall`
  (`Successor/StorageExecution.lean`). It runs `fuelCertified` and on failure reports
  `out of domain (e.wasm-α): w.fuel_certificate`. The definitions moved to `Wasm/FuelCert.lean`
  so the checker does not depend on the proof modules. The README explains why the general proof
  (prepare ⇒ validation ⇒ nesting ⇒ finite-wasm `gasTable`/`optimize`) was not attempted in this lane.
- **The wasmFuel / prepaidGas link**: the theorem is now stated about the hook itself
  (`functionCallRecordedF F = functionCallRecorded`), so no inspection step is left.
- **Final theorem** `NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient` (default
  target `NearSpecV3.Successor.FuelFinal`). Its only hypotheses are `0 < regular_op_cost` and
  `F ≥ wasmFuel`; the `_pv86` corollary discharges the first.
- Relation-change evidence: before/after on 12,562 cases (seeded corpus sample of 2,000 per corpus,
  the 224 warm originals, and 338 evidence fixtures). 0 verdicts or reasons moved. The
  breakage control (guard under-charging by one `r`) moved 587 of 1,200 cases (300 each from
  d3c7–d3c10) to out of domain and none to accept.
- Checker sha256: before `f40158a4bb72…`, after `12f2fbbdca3c…`. A rebuild from the committed source
  reproduces `12f2fbbdca3c…`. The breakage control binary is `b6796a5e6b08…` (not committed).

Axioms (from the build):
```
'NearSpecV3.Wasm.hostsOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Successor.StorageExecution.vmCall_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient_pv86' depends on axioms: [propext, Classical.choice, Quot.sound]
```
