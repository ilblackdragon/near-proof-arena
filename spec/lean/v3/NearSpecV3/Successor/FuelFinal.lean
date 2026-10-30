import NearSpecV3.Successor.StorageExecution
import NearSpecV3.Wasm.FuelHost
/-!
# W02 fuel sufficiency at the successor's `FunctionCall` hook (workplan item 3)

`Wasm/FuelSufficiency.lean` proves the potential argument relative to the host obligation
`HostsOK` and the static obligation `CodeCertified`. `Wasm/FuelHost.lean` proves `HostsOK` for
every host arm. The successor discharges `CodeCertified` by checking it: `vmCall` runs the
certificate (`fuelCertified`) before the VM and reports out of domain on failure. So the theorem
below has no hypothesis beyond the hook's own inputs and the configuration's `0 < regular_op_cost`:
the `FunctionCall` hook the `allFeatures` checker runs (`functionCallRecorded`, step budget
`wasmFuel cfg gas` with `prepaidGas := gas`) is equal, as a function of its inputs, to the same
hook under **any** larger step budget. The budget never decides a verdict, so no execution is
rejected as fuel exhaustion.
-/
namespace NearSpecV3.Successor.StorageExecution
open NearSpecV3.Wasm

theorem fuelCertified_codeCertified {cfg : NearCfg} {code : ByteArray}
    (h : fuelCertified cfg code = true) : CodeCertified cfg code true := by
  intro p hp
  unfold fuelCertified at h
  rw [hp] at h
  exact h

/-- The guarded VM call is independent of the step budget above `wasmFuel`. -/
theorem vmCall_stable (cfg : NearCfg) (hr : 0 < cfg.regularOpCost) (F : NearCfg → Nat → Nat)
    (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) (code : ByteArray) (method : String) (ctx : CallCtx)
    (real : TTN.RealStore) :
    vmCall F cfg code method ctx real = vmCall wasmFuel cfg code method ctx real := by
  unfold vmCall
  cases hc : fuelCertified cfg code
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [runCallWithLimits_stable hostsOK hr code method ctx true false (some real)
      (fuelCertified_codeCertified hc).prep (F cfg ctx.prepaidGas) (hF _)]

/-- The checker's hook passes `wasmFuel` (item 3, part 3): `functionCallRecorded` is
`functionCallRecordedF wasmFuel`, whose VM call uses `wasmFuel cfg ctx.prepaidGas` with
`ctx.prepaidGas := gas`. -/
theorem functionCallRecorded_fuel (fl : Flags) (cfg : NearCfg) :
    functionCallRecorded fl cfg = functionCallRecordedF fl wasmFuel cfg := rfl

/-- **W02 fuel sufficiency (final).** For every configuration with `0 < regular_op_cost` and every
step budget `F ≥ wasmFuel`, the successor's `FunctionCall` hook computes exactly what it computes
under `wasmFuel`, on every input. -/
theorem functionCall_fuel_sufficient (fl : Flags) (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (F : NearCfg → Nat → Nat) (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) :
    functionCallRecordedF fl F cfg = functionCallRecorded fl cfg := by
  have h : vmCall F cfg = vmCall wasmFuel cfg := by
    funext code method ctx real
    exact vmCall_stable cfg hr F hF code method ctx real
  rw [functionCallRecorded_fuel]
  unfold functionCallRecordedF
  rw [h]

/-- At the successor's configurations (`regular_op_cost = 822,756`). -/
theorem functionCall_fuel_sufficient_pv86 (fl : Flags) (cfg : NearCfg) (hr : cfg.regularOpCost = pv86.regularOpCost)
    (F : NearCfg → Nat → Nat) (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) :
    functionCallRecordedF fl F cfg = functionCallRecorded fl cfg :=
  functionCall_fuel_sufficient fl cfg (by rw [hr]; decide) F hF

end NearSpecV3.Successor.StorageExecution

#print axioms NearSpecV3.Successor.StorageExecution.vmCall_stable
#print axioms NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient
#print axioms NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient_pv86
