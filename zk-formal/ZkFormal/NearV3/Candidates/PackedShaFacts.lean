import ZkFormal.NearV3.Candidates.PackedShaAllocation
import ZkFormal.NearV3.Assembly.ShaBinUnion

namespace ZkFormal.NearV3.Candidates.PackedShaFacts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly

/-- The same physical packed SHA union supplies the semantic digest interface.
This transports the checked SHA facts through exact counts, rather than assuming
an independent logical SHA oracle for the packed tables. -/
theorem facts (bins : List (List Sha.Gen.Msg)) (pub : List Fp)
    (hok : ∀bin∈bins,Sha.MsgsOk bin) :
    ShaFacts (PackedShaBins.unionCount bins pub (List.range bins.length) true)
      (PackedShaBins.unionCount bins pub (List.range bins.length) false) := by
  have he (sd : Bool) :
      PackedShaBins.unionCount bins pub (List.range bins.length) sd=
        shaUnionCount (shaBinTrace bins) pub (List.range bins.length) sd := by
    funext b msg
    exact PackedShaBins.union_count bins pub _
      (PackedShaAllocation.selected_ok bins hok) sd b msg
  rw [he true,he false]
  exact shaBinUnionFacts bins pub hok

end ZkFormal.NearV3.Candidates.PackedShaFacts
