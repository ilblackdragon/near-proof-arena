import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.V2.G.Defs

/-!
# Static well-formedness of the assembled v3 AIR

`nearAirV3_wf` and `nearAirV3_npOkPg` are the side conditions the admission
certificate needs; both are kernel evaluations on the concrete `nearAirV3`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.V2

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Structural well-formedness of every table (columns, buses, constraint degree
≤ 16, multiplicity bits, height caps, and the global bus budgets). -/
theorem nearAirV3_wf : nearAirV3.wf 16 = true := by decide +kernel

/-- The v1 side condition on the underlying AIR. -/
theorem nearAirV3_air_wf : nearAirV3.toAir.wf 16 = true :=
  AirP.wf_air nearAirV3 16 nearAirV3_wf

/-- P2 side conditions at `auxGroup = g` for `1 ≤ g ≤ 3`. -/
theorem nearAirV3_npOkPg (g : Nat) (hg1 : 1 ≤ g) (hg3 : g ≤ 3) :
    ZkFormal.V2.G.NpOkPg nearAirV3 (ZkFormal.V2.G.pg g) := by
  have hg : g = 1 ∨ g = 2 ∨ g = 3 := by omega
  rcases hg with rfl | rfl | rfl
  · refine ⟨⟨⟨1, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨⟨2, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨⟨3, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel

end ZkFormal.NearV3.Assembly
