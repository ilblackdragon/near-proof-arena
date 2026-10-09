import ZkFormal.NearV3.Candidates.RawFrameFusion
namespace ZkFormal.NearV3.Candidates.PriorOverlaySlots
open ZkFormal.Air HorizontalProfile
/-- Existing fused tables excluding prior-memory and first-ID stages. -/
def base := GatedLengthFusion.selected.take 19

def histogram (send : Bool) : List (Nat×Nat) :=
  (List.range 7).map (fun d=>(d,((base.flatMap profiles).filter (fun i=>i.send==send && i.phi==d)).length))
theorem sends : histogram true=[(0,0),(1,0),(2,73),(3,9),(4,0),(5,0),(6,0)] := by decide +kernel
theorem receives : histogram false=[(0,0),(1,0),(2,119),(3,11),(4,0),(5,0),(6,0)] := by decide +kernel
theorem interaction_count : (base.flatMap profiles).length=212 := by decide +kernel
theorem width : (base.map (·.width)).sum=3373 := by decide +kernel
end ZkFormal.NearV3.Candidates.PriorOverlaySlots
