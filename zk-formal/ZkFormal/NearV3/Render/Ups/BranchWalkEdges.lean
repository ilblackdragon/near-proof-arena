import ZkFormal.NearV3.Render.Ups.NodeWalkEdges

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

/-- A revealed native branch child supplies a descent edge to its resolved record. -/
theorem branch_child_edge (n slot cid clen cres : Nat) (s : NodeS3)
    (value : Option NSlot3) (kids : List NKid) (pre post mem : List Nat)
    (hs : s.v=.branch value kids mem) (hk : kids[slot]?=some (.node cid clen cres pre post)) :
    [n,0,slot,cres,0,EK_DOWN]∈edgesOf3 n s := by
  simp only [edgesOf3,hs,List.mem_append]
  left
  apply List.mem_filterMap.mpr
  refine ⟨(.node cid clen cres pre post,slot),?_,rfl⟩
  apply List.mem_of_getElem? (i:=slot)
  apply List.getElem?_zip_eq_some.mpr
  refine ⟨hk,?_⟩
  have hb : slot<kids.length := (List.getElem?_eq_some_iff.mp hk).1
  simp [hb]

/-- Branch absence uses the source record's actual bitmap and value presence. -/
theorem branch_bitmap (s : NodeS3) (value : Option NSlot3) (kids : List NKid)
    (mem : List Nat) (hs : s.v=.branch value kids mem) :
    s.v.bmap=some (kidBitmap kids,if value.isSome then 1 else 0) := by
  rw [hs]; rfl
end ZkFormal.NearV3.Render.UpsGen
