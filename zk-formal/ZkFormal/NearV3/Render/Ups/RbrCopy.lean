import ZkFormal.NearV3.Render.Ups.PostSnapshot
import ZkFormal.NearV3.Render.Ups.CopyMiddle

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem slot_bytes_length {s : NSlot3} (h : s.wf) (post : Bool) :
    (s.bytes post).length=36 := by
  cases s <;> cases post <;> simp_all [NSlot3.wf,NSlot3.bytes]

theorem rbr_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=3)
    (old new : NSlot3) (kids : List NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.branch (some old) kids oldMem).wf)
    (hd : (NodeV3.branch (some new) (kids.map snapshotKid) newMem).wf) :
    CopyFields I (encodePart base (.branch (some old) kids oldMem)
      (.branch (some new) (kids.map snapshotKid) newMem)) := by
  let Q := encodePart base (.branch (some old) kids oldMem)
    (.branch (some new) (kids.map snapshotKid) newMem)
  have f : FieldsOk Q := encodePart_fields _ _ _ hd
  have ht : Q.ty=3 := rfl
  have hkind : Q.kind=3 := hk
  let front : List (Nat×Nat) := [(0,1),(4,4),(5,32)]
  let middle : List (Nat×Nat) := [(6,2)]++List.replicate (nWin Q.shape) (7,32)
  let common := [kidBitmap kids%256,kidBitmap kids/256]++kids.flatMap (NKid.bytes true)
  have hshape : Q.shape=(front++middle)++[(8,8)] := by
    calc Q.shape=nodeFields Q.ty Q.qhk (nWin Q.shape) := f.shape
         _ = _ := by simp [front,middle,nodeFields,ht,List.append_assoc]
  have hnew : (new.bytes false).length=36 := slot_bytes_length (hd.2.1 new rfl) false
  have hold : (old.bytes true).length=36 := slot_bytes_length (hs.2.1 old rfl) true
  have hq : Q.q=(([2]++new.bytes false)++common)++newMem := by
    simp [Q,encodePart,NodeV3.ser,common,List.append_assoc]
  have hpb : Q.pb=(([2]++old.bytes true)++common)++oldMem := by simp [Q,encodePart,NodeV3.ser,common,List.append_assoc]
  have hflen : fieldsLen (front++middle)=37+common.length := by
    have hb := f.bytes
    rw [hshape,fieldsLen_append,hq] at hb
    simp only [List.length_append,List.length_cons,List.length_nil,hnew,hd.2.2.2] at hb
    simp only [fieldsLen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hb
    change 1+36+common.length+8=fieldsLen (front++middle)+8 at hb
    omega
  change CopyFields I Q
  constructor
  intro pre post st width he hc
  change Q.shape=pre++(st,width)::post at he
  change CpB I Q st (nWin pre)=true at hc
  have hst : st=0 ∨ st=6 ∨ st=7 := by
    simpa [CpB,VcpB,WfrB,hkind,or_assoc] using hc
  have hu := field_headBytes_bound (front++middle) [(8,8)] pre post (st,width)
    (hshape.symm.trans he) (by simp; rcases hst with h|h|h <;> omega)
  have hstart : sourceFieldStart I Q st (nWin pre) (fieldsLen pre)=(fieldsLen pre : Int) := by
    simp [sourceFieldStart,hkind]
  refine ⟨by omega,by rw [hstart]; omega,?_⟩
  change FieldPayloadEdit (Q.kind==5 && st==6) (if I.ts=1 then 0 else 15)
    ((Q.pb.drop (sourceFieldStart I Q st (nWin pre) (fieldsLen pre)).toNat).take width)
    ((Q.q.drop (fieldsLen pre)).take width)
  simp only [hkind,Nat.reduceBEq,Bool.false_and,hstart,Int.toNat_natCast]
  have hbytes : (Q.q.drop (fieldsLen pre)).take width=(Q.pb.drop (fieldsLen pre)).take width := by
    rcases hst with hst | hst
    · have hh : (st,width) ∉ [(4,4),(5,32)]++middle++[(8,8)] := by
        simp [hst,middle,List.mem_replicate]
      have he' : [(0,1)]++([(4,4),(5,32)]++middle++[(8,8)])=pre++(st,width)::post := by
        rw [← he, hshape]; simp [front,List.append_assoc]
      have hb := field_headBytes_bound [(0,1)] _ pre post (st,width) he' hh
      rw [hq,hpb]
      simpa only [List.append_assoc] using slice_common_headBytes [2]
        (new.bytes false++common++newMem) (old.bytes true++common++oldMem)
        (fieldsLen pre) width (by simpa [fieldsLen] using hb)
    · have hl := field_tail_bound front (middle++[(8,8)]) pre post (st,width)
        (by rw [← he,hshape]; simp [List.append_assoc])
        (by rcases hst with h|h <;> simp [front,h])
      rw [hq,hpb]
      exact slice_common_middle ([2]++new.bytes false) ([2]++old.bytes true) common newMem oldMem
        (fieldsLen pre) width (by simp [hnew,hold])
        (by simpa [front,fieldsLen,hnew] using hl) (by simp only [List.length_append,List.length_cons,List.length_nil,hnew]; rw [hflen] at hu; omega)
  rw [← hbytes]
  exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
