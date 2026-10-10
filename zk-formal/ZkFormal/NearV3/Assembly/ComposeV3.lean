import ZkFormal.NearV3.Assembly.NearAirBus
import ZkFormal.NearV3.Assembly.ExtractV3

/-!
# ZkFormal.NearV3.Assembly.ComposeV3 — the `HoldsP` combinators of `nearAirV3`

`HoldsP nearAirV3 pub tr` is exactly (v1 `Holds` + public fit): per-table height,
constraints and bits, the public segments fit, and the bus balance.  This module
gives

* `holdsP_of_parts` — assemble `HoldsP` from the per-table `TableLocal`s, the
  public fit and the bus balance (the completion interface the render package
  produces into);
* `tableLocal_of_holdsP_v3` / `balance_decomp` — the reverse, for extraction.

Together with `ExtractV3.lean` (`*Local` from `HoldsP`) and `NearAirBus.lean`
(`busCount_nearAirV3`), these are the reusable plumbing of `ExtractV3Stmt`
(item 3) and `RenderV3Stmt` (item 4); the remaining content is the per-table
records and renders.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- **Assemble `HoldsP nearAirV3`.**  Given every table's local legality (`TableLocal`,
in `nearAirV3` order), the public-segment fit and the bus balance, `HoldsP` holds.
-/
theorem holdsP_of_parts {pub : List Fp} {tr : Trace Fp}
    (hL : ∀ (t : Nat) (ht : t < nearAirV3.tables.length),
      ZkFormal.Near.TableLocal nearAirV3.tables[t] tr t pub)
    (hfit : pubFit nearAirV3 pub = true)
    (hbal : ∀ b m, busCount nearAirV3.toAir tr pub b true m + pubCount nearAirV3 pub b true m =
      busCount nearAirV3.toAir tr pub b false m + pubCount nearAirV3 pub b false m) :
    HoldsP nearAirV3 pub tr where
  logBound := fun t ht => ⟨(hL t ht).log_ge, (hL t ht).log_le⟩
  constr := fun t ht r hr e he => (hL t ht).constr r hr e he
  bits := fun t ht r hr i hi b hb => (hL t ht).bits r hr i hi b hb
  pubFit := hfit
  balance := hbal

/-- The bus balance of `nearAirV3` in decomposed (per-table) form. -/
theorem balance_decomp {pub : List Fp} {tr : Trace Fp}
    (hbal : ∀ b m, busCount nearAirV3.toAir tr pub b true m + pubCount nearAirV3 pub b true m =
      busCount nearAirV3.toAir tr pub b false m + pubCount nearAirV3 pub b false m)
    (b : Nat) (m : List Fp) :
    (nearTablesFull.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
        tableBusCount T.interactions tr t pub b true m).sum + pubCount nearAirV3 pub b true m =
      (nearTablesFull.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
        tableBusCount T.interactions tr t pub b false m).sum + pubCount nearAirV3 pub b false m := by
  rw [← busCount_nearAirV3 tr pub b true m, ← busCount_nearAirV3 tr pub b false m]
  exact hbal b m

end ZkFormal.NearV3.Assembly
