import ZkFormal.NearV3.Render.Ups.RbrCopy
import ZkFormal.NearV3.Render.Ups.CopyShift

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem spb_value_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=10) (hi : I.ci=4)
    (key : List Nat) (sv : NSlot3) (kids : List NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.leaf key sv oldMem).wf)
    (hd : (NodeV3.branch (some (snapshotValue sv)) kids newMem).wf) :
    CopyFields I (encodePart base (.leaf key sv oldMem)
      (.branch (some (snapshotValue sv)) kids newMem)) := by
  let Q := encodePart base (.leaf key sv oldMem) (.branch (some (snapshotValue sv)) kids newMem)
  have f : FieldsOk Q := encodePart_fields _ _ _ hd
  let sourceHead := [0]++u32r (hpN key true).length++hpN key true
  let tailBytes := [kidBitmap kids%256,kidBitmap kids/256]++kids.flatMap (NKid.bytes false)++newMem
  have hshape : Q.shape=([(0,1),(4,4),(5,32)]++[(6,2)]++List.replicate (nWin Q.shape) (7,32))++[(8,8)] := by
    calc Q.shape=nodeFields Q.ty Q.qhk (nWin Q.shape) := f.shape
         _ = _ := by have ht : Q.ty=3 := rfl; simp [nodeFields,ht]
  have hval : (sv.bytes true).length=36 := slot_bytes_length hs.2.1 true
  have hsource : Q.pb=sourceHead++sv.bytes true++oldMem := rfl
  have hout : Q.q=[2]++sv.bytes true++tailBytes := by
    simp [Q,encodePart,NodeV3.ser,tailBytes,List.append_assoc]
  have hplen : Q.pb.length=sourceHead.length+44 := by rw [hsource]; simp [hval,hs.2.2]
  change CopyFields I Q
  constructor
  intro pre post st width he hc
  change Q.shape=pre++(st,width)::post at he
  change CpB I Q st (nWin pre)=true at hc
  have hst : st=4 ∨ st=5 := by simpa [CpB,VcpB,WfrB,XcpB,hk,hi,Q,encodePart] using hc
  have hu := field_headBytes_bound [(0,1),(4,4),(5,32)]
    ([(6,2)]++List.replicate (nWin Q.shape) (7,32)++[(8,8)]) pre post (st,width)
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using hshape.symm.trans he)
    (by rcases hst with h|h <;> simp [h,List.mem_replicate])
  have hl := field_tail_bound [(0,1)]
    ([(4,4),(5,32)]++[(6,2)]++List.replicate (nWin Q.shape) (7,32)++[(8,8)]) pre post (st,width)
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using hshape.symm.trans he)
    (by rcases hst with h|h <;> simp [h])
  have hu' : fieldsLen pre+width≤37 := by simpa [fieldsLen] using hu
  have hl' : 1≤fieldsLen pre := by simpa [fieldsLen] using hl
  have hstart : sourceFieldStart I Q st (nWin pre) (fieldsLen pre)=
      ((sourceHead.length+(fieldsLen pre-1) : Nat) : Int) := by
    have hkind : Q.kind=10 := hk
    have hne : st≠7 := by omega
    simp [sourceFieldStart,hkind,hne,hplen]
    omega
  refine ⟨by simp [Q,encodePart,hk],by rw [hstart]; omega,?_⟩
  change FieldPayloadEdit (Q.kind==5 && st==6) (if I.ts=1 then 0 else 15)
    ((Q.pb.drop (sourceFieldStart I Q st (nWin pre) (fieldsLen pre)).toNat).take width)
    ((Q.q.drop (fieldsLen pre)).take width)
  have hkind : Q.kind=10 := hk
  simp only [hkind,Nat.reduceBEq,Bool.false_and,hstart,Int.toNat_natCast]
  have hbytes : (Q.q.drop (fieldsLen pre)).take width=
      (Q.pb.drop (sourceHead.length+(fieldsLen pre-1))).take width := by
    rw [hout,hsource]
    rw [slice_after_prefix [2] (sv.bytes true) tailBytes (fieldsLen pre) width
      (by simp;omega) (by simp [hval];omega)]
    rw [slice_after_prefix sourceHead (sv.bytes true) oldMem (sourceHead.length+(fieldsLen pre-1)) width
      (by omega) (by rw [hval];omega)]
    simp
  rw [←hbytes]
  exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
