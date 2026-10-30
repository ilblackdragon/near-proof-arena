import NearSpecV3.Successor.TierO3Lift
import NearSpecV3.Successor.TierO2
import NearSpecV3.Examples.RealCaseD3Data
import NearSpecV3.Examples.RealCaseD3SplitData

/-!
# W12 / O3 — the layout hypothesis holds on real chunks

`LayoutsWF` (README §9) is the only premise of `Lift.globalActions_wf` and of the named O3 pairs
(`TierO3Lift.lean`). `layoutsWFb` decides it for a claim (`layoutsWF_of_b`), and `decide +kernel`
evaluates it on recorded mainnet-shaped claims: the honest D3 chunk `d3c7/d3/06-h10006-s0` and the
resharding chunk `seed37-00-h10085-s7` (a claim whose epoch table carries a parent and a child
layout). No `native_decide`.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.Examples

/-- The decision procedure of `LayoutsWF`. -/
def layoutsWFb (cb : Bytes) : Bool :=
  match decodeClaimE cb with
  | .ok cl => cl.epochs.all fun ep =>
      match decodeLayout ep.shardLayout with
      | .ok L => L.shardIds.length == L.boundaries.length + 1
      | .error _ => true
  | .error _ => true

theorem layoutsWF_of_b (cb : Bytes) (h : layoutsWFb cb = true) : LayoutsWF cb := by
  intro cl hcl ep hep L hL
  unfold layoutsWFb at h
  rw [hcl] at h
  have h2 := List.all_eq_true.mp h ep hep
  rw [hL] at h2
  exact beq_iff_eq.mp h2

set_option maxRecDepth 200000 in
theorem layoutsWF_06_h10006_s0 : LayoutsWF claimD3_06_h10006_s0 :=
  layoutsWF_of_b _ (by decide +kernel)

set_option maxRecDepth 200000 in
theorem layoutsWF_seed37_00_h10085_s7 : LayoutsWF claimD3_seed37_00_h10085_s7 :=
  layoutsWF_of_b _ (by decide +kernel)

set_option maxRecDepth 200000 in
/-- The resharding claim's epoch table carries more than one distinct layout, so the hypothesis is
checked on a layout change, not only on a single-layout segment. -/
theorem seed37_layouts_differ :
    (match decodeClaimE claimD3_seed37_00_h10085_s7 with
     | .ok cl => (cl.epochs.map (·.shardLayout)).eraseDups.length
     | .error _ => 0) ≥ 2 := by
  decide +kernel

/-- The O3 pairs apply to these chunks (their only premise holds). -/
theorem storageResolution_globalActions_06_h10006_s0 :
    Refines (Tier.checker .storageResolution claimD3_06_h10006_s0 witnessD3_06_h10006_s0)
      (Tier.checker .globalActions claimD3_06_h10006_s0 witnessD3_06_h10006_s0) :=
  relSuccessor_storageResolution_globalActions_wf _ _ layoutsWF_06_h10006_s0

theorem curveHosts_allFeatures_seed37_00_h10085_s7 :
    VRefines (Tier.checker .curveHosts claimD3_seed37_00_h10085_s7 witnessD3_seed37_00_h10085_s7)
      (Tier.checker .allFeatures claimD3_seed37_00_h10085_s7 witnessD3_seed37_00_h10085_s7) :=
  relSuccessor_curveHosts_allFeatures_wf _ _ layoutsWF_seed37_00_h10085_s7

/-! ## Compositions with O2 -/

/-- `.globalActions ⊑ .allFeatures` at verdict level, unconditionally: O2's curve-host lift
(`Lift.curveHosts`) discharges the `hC` premise of `relSuccessor_globalActions_allFeatures_of_C`. -/
theorem relSuccessor_globalActions_allFeatures (c w : Bytes) :
    VRefines (Tier.checker .globalActions c w) (Tier.checker .allFeatures c w) :=
  relSuccessor_globalActions_allFeatures_of_C (Lift.curveHosts _ rfl) c w

/-- `.storageResolution ⊑ .allFeatures` at verdict level, on claims whose shard layouts are well
formed (O3, then the line above). -/
theorem relSuccessor_storageResolution_allFeatures_wf (c w : Bytes) (hLay : LayoutsWF c) :
    VRefines (Tier.checker .storageResolution c w) (Tier.checker .allFeatures c w) :=
  (relSuccessor_storageResolution_globalActions_wf c w hLay).toV.trans (relSuccessor_globalActions_allFeatures c w)

#print axioms relSuccessor_globalActions_allFeatures
#print axioms relSuccessor_storageResolution_allFeatures_wf
#print axioms layoutsWF_06_h10006_s0
#print axioms layoutsWF_seed37_00_h10085_s7
#print axioms seed37_layouts_differ
#print axioms storageResolution_globalActions_06_h10006_s0
#print axioms curveHosts_allFeatures_seed37_00_h10085_s7

end NearSpecV3.Successor
