import ZkFormal.NearV3.Render.Ups.EdgeInsert
import ZkFormal.NearV3.Render.Ups.RbiSlices
import ZkFormal.NearV3.Render.Node.WinFacts

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def insertSide (I : UpsInst) : Nat := if I.ts=1 then 0 else 1

theorem rbi_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=5)
    (sv : Option NSlot3) (rest : List NKid) (new : NKid) (oldMem newMem : List Nat)
    (hn : new≠.none) (hnw : new.wf)
    (hs : (NodeV3.branch sv (edgeKids (insertSide I) .none rest) oldMem).wf)
    (hd : (NodeV3.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem).wf) :
    CopyFields I (encodePart base (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
      (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem)) := by
  let Q := encodePart base (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
    (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem)
  have f : FieldsOk Q := encodePart_fields _ _ _ hd
  have ht : Q.ty=2 ∨ Q.ty=3 := by cases sv <;> simp [Q,encodePart,nodeTypeCode]
  let body := match sv with | none => [1] | some s => [2]++s.bytes true
  let bitmap := kidBitmap (edgeKids (insertSide I) .none rest)
  have hlen : rest.length=15 := by
    have hh := hs.1
    by_cases h : I.ts=1 <;> simp [edgeKids,insertSide,h] at hh <;> omega
  have hbitmap : kidBitmap (edgeKids (insertSide I) new (rest.map snapshotKid))=
      bitmap+2^(if I.ts=1 then 0 else 15) := by
    have hh := edge_insert_bitmap (insertSide I) rest new hn hlen
    by_cases h : I.ts=1 <;> simpa [bitmap,insertSide,h] using hh
  have hclear : bitmap/2^(if I.ts=1 then 0 else 15)%2=0 := by
    have hh := NodeGen3.bitOf_kidBitmap (edgeKids (insertSide I) .none rest)
      (if I.ts=1 then 0 else 15)
    change bitmap/2^(if I.ts=1 then 0 else 15)%2=_ at hh
    rw [hh]
    by_cases h : I.ts=1 <;> simp [NodeGen3.kbit,edgeKids,insertSide,h,List.getD_eq_getElem?_getD,List.getElem?_append,hlen]
  apply rbi_copy_slices I Q hk f ht body (rest.flatMap (NKid.bytes true))
    (new.bytes false) oldMem newMem bitmap
  · cases sv with
    | none => simp [Q,encodePart,nodeTypeCode,branchPrefix,fieldsLen,body]
    | some v =>
      have hv := slot_bytes_length (hs.2.1 v rfl) true
      simp [Q,encodePart,nodeTypeCode,branchPrefix,fieldsLen,body,hv]
  · exact present_kid_length hnw hn false
  · exact hd.2.2.2
  · exact Link.kidBitmap_lt hs.1
  · exact hclear
  · change (NodeV3.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem).ser false=_
    simp only [NodeV3.ser,hbitmap]
    cases sv <;> by_cases h : I.ts=1 <;>
      simp [Q,encodePart,body,edgeKids,insertSide,h,List.append_assoc]
  · change (NodeV3.branch sv (edgeKids (insertSide I) .none rest) oldMem).ser true=_
    cases sv <;> by_cases h : I.ts=1 <;>
      simp [NodeV3.ser,Q,encodePart,body,edgeKids,insertSide,h,NKid.bytes,List.append_assoc,bitmap]

end ZkFormal.NearV3.Render.UpsGen
