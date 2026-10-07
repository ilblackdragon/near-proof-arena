import ZkFormal.NearV3.Render.Ups.MoveCopy

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem mve_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=7)
    (key : List Nat) (sv : NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.ext key sv oldMem).wf)
    (hd : (NodeV3.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem).wf)
    (hcut : I.ti+1≤key.length) :
    CopyFields I (encodePart base (.ext key sv oldMem)
      (.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem)) := by
  let Q := encodePart base (.ext key sv oldMem) (.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem)
  have f : FieldsOk Q := encodePart_fields _ _ _ hd
  have ht : Q.ty=1 := rfl
  have hn : nWin Q.shape=1 := f.extension ht
  let mid := (if 1<Q.qhk then [(3,Q.qhk-1)] else [])++[(7,32)]
  let common := (hpN (key.drop (I.ti+1)) false).drop 1++sv.bytes true
  have hdelta : Q.phk-Q.qhk=key.length/2-(key.drop (I.ti+1)).length/2 := by
    change (1+key.length/2)-(1+(key.drop (I.ti+1)).length/2)=_
    omega
  apply moved_copy_suffix I Q (Or.inr hk) f mid common oldMem newMem
  · calc Q.shape=nodeFields Q.ty Q.qhk (nWin Q.shape) := f.shape
         _ = _ := by simp [mid,nodeFields,ht,hn,List.append_assoc]
  · exact hd.2.2.2
  · change 1+(key.drop (I.ti+1)).length/2≤1+key.length/2
    simp; omega
  · change ((NodeV3.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem).ser false).drop 6=_
    simp only [NodeV3.ser,snapshotKid_bytes]
    exact serial_suffix _ false 3 (sv.bytes true) newMem
  · change ((NodeV3.ext key sv oldMem).ser true).drop (6+(Q.phk-Q.qhk))=_
    rw [hdelta]
    exact move_serial_suffix key false (I.ti+1) 3 (sv.bytes true) oldMem hcut hs.1

end ZkFormal.NearV3.Render.UpsGen
