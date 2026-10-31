import NearSpecV3.Successor.StorageExecution
import NearSpecV3.Wasm.FuelGeneral
import NearSpecV3.Wasm.FuelCertOK
/-!
# W02 fuel sufficiency at the successor's `FunctionCall` hook (workplan item 3)

`Wasm/FuelGeneral.lean` proves, for every contract, that the step budget `wasmFuel` never decides
the result of `runCallWithLimits` (`FuelGen.wasmFuel_sufficient`). Its static facts come from
`prepare` itself (`FuelGen.prepare_fnOK`: `FuelNest` for the nesting and the block limit,
`wc_gasTable` for finite-wasm's gas table), and the host arms from `hostsOK` (`Wasm/FuelHost.lean`).
Its hypotheses are only `0 < regular_op_cost ≤ linear_op_base_cost`, which hold at PV86
(822,756 ≤ 26,328,192).

So the theorem below has no hypothesis beyond the hook's own inputs and those two cost facts: the
`FunctionCall` hook the `allFeatures` checker runs (`functionCallRecorded`, step budget
`wasmFuel cfg gas` with `prepaidGas := gas`) is equal, as a function of its inputs, to the same hook
under **any** larger step budget. The budget never decides a verdict, so no execution is rejected
as fuel exhaustion.

Until 2026-10-31 `vmCall` ran the fuel certificate first (`fuelCertified`) and reported
`out of domain (e.wasm-α): w.fuel_certificate` on failure; that check discharged the round-1
hypothesis `CodeCertified`. `FuelCertOK.fuelCertified_true` proves the check never fails, and
`vmCallGuarded_eq` below states that the guarded call is the current one.
-/
namespace NearSpecV3.Successor.StorageExecution
open NearSpecV3.Wasm

/-- The VM call is independent of the step budget above `wasmFuel`. -/
theorem vmCall_stable (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (F : NearCfg → Nat → Nat)
    (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) (code : ByteArray) (method : String) (ctx : CallCtx)
    (real : TTN.RealStore) :
    vmCall F cfg code method ctx real = vmCall wasmFuel cfg code method ctx real := by
  unfold vmCall
  rw [FuelGen.wasmFuel_sufficient_le hr hl code method ctx (hF _) false (some real)]

/-- The checker's hook passes `wasmFuel` (item 3, part 3): `functionCallRecorded` is
`functionCallRecordedF wasmFuel`, whose VM call uses `wasmFuel cfg ctx.prepaidGas` with
`ctx.prepaidGas := gas`. -/
theorem functionCallRecorded_fuel (fl : Flags) (cfg : NearCfg) :
    functionCallRecorded fl cfg = functionCallRecordedF fl wasmFuel cfg := rfl

/-- **W02 fuel sufficiency (final).** For every configuration with
`0 < regular_op_cost ≤ linear_op_base_cost` and every step budget `F ≥ wasmFuel`, the successor's
`FunctionCall` hook computes exactly what it computes under `wasmFuel`, on every input. -/
theorem functionCall_fuel_sufficient (fl : Flags) (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (F : NearCfg → Nat → Nat)
    (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) :
    functionCallRecordedF fl F cfg = functionCallRecorded fl cfg := by
  have h : vmCall F cfg = vmCall wasmFuel cfg := by
    funext code method ctx real
    exact vmCall_stable cfg hr hl F hF code method ctx real
  rw [functionCallRecorded_fuel]
  unfold functionCallRecordedF
  rw [h]

/-- At the successor's configurations (`regular_op_cost = 822,756`,
`linear_op_base_cost = 26,328,192`). -/
theorem functionCall_fuel_sufficient_pv86 (fl : Flags) (cfg : NearCfg)
    (hr : cfg.regularOpCost = pv86.regularOpCost) (hl : cfg.linearOpBaseCost = pv86.linearOpBaseCost)
    (F : NearCfg → Nat → Nat) (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) :
    functionCallRecordedF fl F cfg = functionCallRecorded fl cfg :=
  functionCall_fuel_sufficient fl cfg (by rw [hr]; decide) (by rw [hr, hl]; decide) F hF

/-! ## The retired guard -/

/-- `vmCall` as it was until 2026-10-31: the fuel certificate first, `w.fuel_certificate` out of
domain on failure. -/
def vmCallGuarded (fuelOf : NearCfg → Nat → Nat) (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (real : TTN.RealStore) : Except String Run :=
  if !fuelCertified cfg code then .error (NearSpecV3.D3.oodE "w.fuel_certificate: a prepared function fails the fuel certificate")
  else .ok (runCallWithLimits cfg code method ctx (fuelOf cfg ctx.prepaidGas) true false (some real))

/-- **The guard was dead.** With the certificate `Wasm/FuelCert.lean` defines, the guarded call is
the current `vmCall` on every input: removing the check moves no verdict. -/
theorem vmCallGuarded_eq (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (fuelOf : NearCfg → Nat → Nat) :
    vmCallGuarded fuelOf cfg = vmCall fuelOf cfg := by
  funext code method ctx real
  unfold vmCallGuarded vmCall
  rw [FuelCertOK.fuelCertified_true hr hl code]
  rfl

end NearSpecV3.Successor.StorageExecution

#print axioms NearSpecV3.Successor.StorageExecution.vmCall_stable
#print axioms NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient
#print axioms NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient_pv86
#print axioms NearSpecV3.Successor.StorageExecution.vmCallGuarded_eq
