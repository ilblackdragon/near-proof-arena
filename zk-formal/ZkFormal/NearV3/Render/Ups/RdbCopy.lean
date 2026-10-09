import ZkFormal.NearV3.Render.Ups.KidOccupancy
import ZkFormal.NearV3.Render.Ups.RdbSlices
import ZkFormal.NearV3.Render.Ups.RbrCopy

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def edgeKids (sd : Nat) (child : NKid) (rest : List NKid) : List NKid :=
  if sd=1 then rest++[child] else child::rest

theorem edge_occupancy (sd : Nat) (old new : NKid) (rest : List NKid)
    (ho : old≠.none) (hn : new≠.none) :
    kidOccupancy (edgeKids sd old rest)=kidOccupancy (edgeKids sd new (rest.map snapshotKid)) := by
  have ho' := (kid_present_none old).2 ho
  have hn' := (kid_present_none new).2 hn
  by_cases h : sd=1 <;> simp [edgeKids,h,kidOccupancy,ho',hn',List.map_map,Function.comp_def]

theorem present_kid_length {k : NKid} (h : k.wf) (hn : k≠.none) (post : Bool) :
    (k.bytes post).length=32 := by
  cases k <;> cases post <;> simp_all [NKid.wf,NKid.bytes]

theorem rdb_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=0)
    (sd : base.sd=0 ∨ base.sd=1)
    (sv : Option NSlot3) (rest : List NKid) (old new : NKid) (oldMem newMem : List Nat)
    (ho : old≠.none) (hn : new≠.none) (how : old.wf) (hnw : new.wf)
    (hs : (NodeV3.branch sv (edgeKids base.sd old rest) oldMem).wf)
    (hd : (NodeV3.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem).wf) :
    CopyFields I (encodePart base (.branch sv (edgeKids base.sd old rest) oldMem)
      (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)) := by
  let Q := encodePart base (.branch sv (edgeKids base.sd old rest) oldMem)
    (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)
  have f : FieldsOk Q := encodePart_fields _ _ _ hd
  let header := (match sv with | none => [1] | some s => [2]++s.bytes true)++
    [kidBitmap (edgeKids base.sd old rest)%256,kidBitmap (edgeKids base.sd old rest)/256]
  have hbitmap := bitmap_eq_of_occupancy (edge_occupancy base.sd old new rest ho hn)
  apply rdb_copy_slices I Q hk f sd header (rest.flatMap (NKid.bytes true))
    (old.bytes true) (new.bytes false) oldMem newMem
  · cases sv with
    | none => simp [Q,encodePart,nodeTypeCode,nodeHeader,fieldsLen,header]
    | some v =>
      have hv := slot_bytes_length (hs.2.1 v rfl) true
      simp [Q,encodePart,nodeTypeCode,nodeHeader,fieldsLen,header,hv]
  · exact present_kid_length how ho true
  · exact present_kid_length hnw hn false
  · exact hd.2.2.2
  · change (NodeV3.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem).ser false=_
    simp only [NodeV3.ser,←hbitmap]
    cases sv <;> by_cases h : base.sd=1 <;>
      simp [Q,encodePart,header,edgeKids,h,snapshotValue_bytes,List.append_assoc]
  · change (NodeV3.branch sv (edgeKids base.sd old rest) oldMem).ser true=_
    cases sv <;> by_cases h : base.sd=1 <;>
      simp [NodeV3.ser,Q,encodePart,header,edgeKids,h,List.append_assoc]

end ZkFormal.NearV3.Render.UpsGen
