import ZkFormal.NearV3.Render.Ups.SplitKidCounts
import ZkFormal.NearV3.Render.Ups.CopyShift
import ZkFormal.NearV3.Render.Ups.RbrCopy
import ZkFormal.NearV3.Render.Ups.FieldStart

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem spb_child_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=10)
    (hi : I.ci=8 ∨ I.ci=10) (key : List Nat) (old new : NKid)
    (sv : Option NSlot3) (oldMem newMem : List Nat) (hn : new≠.none) (hnw : new.wf)
    (hs : (NodeV3.ext key old oldMem).wf)
    (hd : (NodeV3.branch sv (splitKids I (snapshotKid old) new) newMem).wf) :
    CopyFields I (encodePart base (.ext key old oldMem)
      (.branch sv (splitKids I (snapshotKid old) new) newMem)) := by
  let Q := encodePart base (.ext key old oldMem) (.branch sv (splitKids I (snapshotKid old) new) newMem)
  have f : FieldsOk Q := encodePart_fields _ _ _ hd
  let sourceHead := [3]++u32Bytes (hpN key false).length++hpN key false
  let header := (match sv with | none => [1] | some s => [2]++s.bytes false)++
    [kidBitmap (splitKids I (snapshotKid old) new)%256,kidBitmap (splitKids I (snapshotKid old) new)/256]
  have ho : snapshotKid old≠.none := by simpa using hs.2.1
  have hold : (old.bytes true).length=32 := present_kid_length hs.2.2.1 hs.2.1 true
  have hnew : (new.bytes false).length=32 := present_kid_length hnw hn false
  have hsource : Q.pb=sourceHead++old.bytes true++oldMem := rfl
  have hplen : Q.pb.length=sourceHead.length+40 := by rw [hsource]; simp [hold,hs.2.2.2]
  have hhead : fieldsLen (nodeHeader Q.ty Q.qhk)=header.length := by
    cases sv with
    | none => simp [Q,encodePart,nodeTypeCode,nodeHeader,header,fieldsLen]
    | some v =>
      have hv := slot_bytes_length (hd.2.1 v rfl) false
      simp [Q,encodePart,nodeTypeCode,nodeHeader,header,fieldsLen,hv]
  change CopyFields I Q
  constructor
  intro pre post st width he hc
  have hkind : Q.kind=10 := hk
  have hst : st=7 := by
    rcases hi with hi|hi <;> simp [CpB,VcpB,WfrB,XcpB,hkind,hi] at hc <;> omega
  subst st
  have hw := field_start_window f pre post width he
  rw [hhead] at hw
  have hstart : sourceFieldStart I Q 7 (nWin pre) (fieldsLen pre)=(sourceHead.length : Int) := by
    simp [sourceFieldStart,hkind,hplen]
  refine ⟨by omega,by rw [hstart]; omega,?_⟩
  simp only [hkind,Nat.reduceBEq,Bool.false_and,hstart,Int.toNat_natCast]
  have hsrcslice : (Q.pb.drop sourceHead.length).take width=old.bytes true := by
    rw [hsource,hw.1,List.append_assoc,List.drop_append_length]
    rw [List.take_append_of_le_length (by omega),←hold,List.take_length]
  have houtslice : (Q.q.drop (fieldsLen pre)).take width=old.bytes true := by
    rcases hi with hi|hi
    · have hwin : nWin Q.shape=1 := by
        simp [Q,encodePart_windows,nodeChildren,splitKids,splitHasNew,hi,oneKid_windows _ _ ho]
      have hp0 : fieldsLen pre=header.length := by omega
      have hout : Q.q=header++old.bytes true++newMem := by
        simp [Q,encodePart,NodeV3.ser,header,splitKids,splitHasNew,hi,oneKid_bytes,List.append_assoc]
        cases sv <;> rfl
      rw [hout,hp0,hw.1,List.append_assoc,List.drop_append_length]
      rw [List.take_append_of_le_length (by omega),←hold,List.take_length]
    · have hwin : nWin Q.shape=2 := by
        simp [Q,encodePart_windows,nodeChildren,splitKids,splitHasNew,hi,twoEdgeKids_windows _ _ _ _ ho hn]
      have hout : Q.q=header++(if I.ts=1 then new.bytes false++old.bytes true else old.bytes true++new.bytes false)++newMem := by
        simp [Q,encodePart,NodeV3.ser,header,splitKids,splitHasNew,hi,twoEdgeKids_bytes,List.append_assoc]
        cases sv <;> rfl
      simp [CpB,VcpB,WfrB,XcpB,WyB,FwB,Spy1B,Spy2B,hkind,hi] at hc
      by_cases ht : I.ts=1
      · have hp1 : fieldsLen pre=header.length+32 := by simp [ht] at hc; omega
        rw [hout,hp1,hw.1]
        simp only [ht,ite_true]
        rw [←List.append_assoc header (new.bytes false) (old.bytes true)]
        rw [slice_after_prefix (header++new.bytes false) (old.bytes true) newMem (header.length+32) 32
          (by simp [hnew]) (by simp [hnew,hold])]
        simp [hnew,←hold]
      · have hp0 : fieldsLen pre=header.length := by simp [ht] at hc; omega
        rw [hout,hp0,hw.1]
        simp only [ht,ite_false,List.append_assoc,List.drop_append_length]
        rw [List.take_append_of_le_length (by omega),←hold,List.take_length]
  rw [hsrcslice,houtslice]
  exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
