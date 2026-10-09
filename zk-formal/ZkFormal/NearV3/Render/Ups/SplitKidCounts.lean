import ZkFormal.NearV3.Render.Ups.SplitKids
import ZkFormal.NearV3.Render.Ups.EdgeInsert

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem oneKid_windows (x : Nat) (kid : NKid) (hk : kid≠.none) :
    (NodeGen3.branchWins (oneKid x kid)).length=1 := by
  rw [windows_present_count]
  have hp := (kid_present_none kid).2 hk
  simp [oneKid,kidOccupancy,NKid.present,hp]

theorem twoEdgeKids_windows (ts x : Nat) (old new : NKid) (ho : old≠.none) (hn : new≠.none) :
    (NodeGen3.branchWins (twoEdgeKids ts x old new)).length=2 := by
  rw [windows_present_count]
  have hp := (kid_present_none old).2 ho
  have hq := (kid_present_none new).2 hn
  by_cases h : ts=1 <;> simp [twoEdgeKids,h,kidOccupancy,NKid.present,hp,hq]

theorem encodePart_windows (base : UpsPartI) (src dst : NodeV3) :
    nWin (encodePart base src dst).shape=nodeChildren dst := by
  simp only [encodePart,nonempty_node_shape,nodeFields_windows]

end ZkFormal.NearV3.Render.UpsGen
