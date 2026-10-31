import NearSpecV3.Wasm.FuelCall
import NearSpecV3.Wasm.FuelNest
import NearSpecV3.Wasm.FuelGas
import NearSpecV3.Wasm.FuelHost
/-!
# Fuel sufficiency (W02, workplan item 3): the theorem

No valid execution is decided by fuel exhaustion. For any configuration with
`0 < regular_op_cost ≤ linear_op_base_cost` (PV86: 822,756 ≤ 26,328,192), any contract, method,
context and storage, the successor's call `runCallWithLimits … (wasmFuel cfg ctx.prepaidGas)` has
the same result as with any larger step budget. `StorageExecution.functionCall` runs exactly this
call with `ctx.prepaidGas = gas`.

The obligations of `Wasm/Fuel.lean`, each now a theorem:

* O-W1 (free steps lower the potential) and O-W1b (`else` jumps forward, under the label
  invariant): `exec_post` (`Wasm/FuelSuff.lean`) on the invariant `Inv`, with `NestOK` from
  `FuelNest.nestOK_of_wellNested`.
* O-W2 (a costly step raises the potential by at most `F`): `exec_post`, `post_call`, and
  `hostsOK` for the host arms.
* O-W3 (`F ≤ 2·max_blocks_per_function + 1`): `FuelNest.freeCount_le_of_wellNested` and
  `FuelNest.prepare_funcs` (the `TooManyBlocksPerFunction` check).
* O-W4 (finite-wasm charges a group before it runs): `wc_gasTable` (`Wasm/FuelGas.lean`), the
  `g ≤ remaining` / host part in `step_post` and `callHost_cont`, and `hostsOK`.
-/
namespace NearSpecV3.Wasm.FuelGen

/-- Every function `prepare` produces satisfies the static fuel facts. -/
theorem prepare_fnOK {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) (p : Prepared)
    (hp : prepare cfg code true = .ok p) :
    ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf := by
  intro j pf hj
  obtain ⟨hw, he, hg, hb⟩ := FuelNest.prepare_funcs cfg code true p hp j pf hj
  have hn := FuelNest.nestOK_of_wellNested pf hw he
  refine ⟨openAt pf.code, hn, wc_gasTable cfg pf hw hn he hg hr hl, ?_⟩
  have := FuelNest.freeCount_le_of_wellNested pf.code hw
  omega

/-- **Fuel sufficiency.** With the successor budget `wasmFuel cfg ctx.prepaidGas`, the call's
result is the result under any larger budget: fuel exhaustion never decides it. -/
theorem wasmFuel_sufficient {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) (method : String)
    (ctx : CallCtx) (k : Nat) (full : Bool) (real : Option TTN.RealStore) :
    runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas + k) true full real =
      runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) true full real :=
  runCallWithLimits_stable hr hostsOK code true (prepare_fnOK hr hl code) method ctx
    _ k (Nat.le_refl _) full real

/-- The same for every budget at or above `wasmFuel`. -/
theorem wasmFuel_sufficient_le {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) (method : String)
    (ctx : CallCtx) {m : Nat} (hm : wasmFuel cfg ctx.prepaidGas ≤ m) (full : Bool)
    (real : Option TTN.RealStore) :
    runCallWithLimits cfg code method ctx m true full real =
      runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) true full real := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact wasmFuel_sufficient hr hl code method ctx k full real

/-- At the PV86 parameters, with and without the successor switches. -/
theorem wasmFuel_sufficient_pv86 (cfg : NearCfg) (hr : cfg.regularOpCost = pv86.regularOpCost)
    (hl : cfg.linearOpBaseCost = pv86.linearOpBaseCost) (code : ByteArray) (method : String)
    (ctx : CallCtx) (k : Nat) (full : Bool) (real : Option TTN.RealStore) :
    runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas + k) true full real =
      runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) true full real :=
  wasmFuel_sufficient (by rw [hr]; decide) (by rw [hr, hl]; decide) code method ctx k full real

end NearSpecV3.Wasm.FuelGen

#print axioms NearSpecV3.Wasm.FuelGen.wasmFuel_sufficient
#print axioms NearSpecV3.Wasm.FuelGen.wasmFuel_sufficient_pv86
