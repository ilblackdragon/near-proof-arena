import ZkFormal.NearV3.Render.Ups.BranchPrefix
import ZkFormal.NearV3.Render.Ups.CopyShift

namespace ZkFormal.NearV3.Render.UpsGen

/-- Inserting a first/last child preserves value fields, inserts one bitmap bit, and
shifts only the inherited windows following a newly inserted first child. -/
theorem rbi_copy_slices (I : UpsInst) (Q : UpsPartI) (hk : Q.kind=5)
    (f : FieldsOk Q) (ht : Q.ty=2 ∨ Q.ty=3)
    (body rest child oldMem newMem : List Nat) (bitmap : Nat)
    (hbody : fieldsLen (branchPrefix Q.ty)=body.length)
    (hch : child.length=32) (hm : newMem.length=8)
    (hb : bitmap<65536) (clear : bitmap/2^(if I.ts=1 then 0 else 15)%2=0)
    (hq : Q.q=body++[(bitmap+2^(if I.ts=1 then 0 else 15))%256,(bitmap+2^(if I.ts=1 then 0 else 15))/256]++
      (if I.ts=1 then child++rest else rest++child)++newMem)
    (hp : Q.pb=body++[bitmap%256,bitmap/256]++rest++oldMem) : CopyFields I Q := by
  have hshape := branch_field_shape f ht
  have hheader : fieldsLen (nodeHeader Q.ty Q.qhk)=body.length+2 := by
    rw [←hbody]; rcases ht with ht|ht <;> simp [nodeHeader,branchPrefix,ht,fieldsLen]
  have hrest : rest.length+32=32*nWin Q.shape := by
    have he := f.bytes
    rw [hq,hshape,fieldsLen_append,hbody] at he
    simp only [fieldsLen_cons,fieldsLen_windows] at he
    by_cases h : I.ts=1 <;> simp [h,hch,hm] at he <;> omega
  constructor
  intro pre post st width he hc
  have hnmem : st≠8 := by intro h; simp [CpB,VcpB,WfrB,hk,h] at hc
  by_cases hbm : st=6
  · subst st
    have hw := branch_bitmap_start f ht pre post width he
    have hstart : sourceFieldStart I Q 6 (nWin pre) (fieldsLen pre)=(fieldsLen pre : Int) := by
      simp [sourceFieldStart,hk]
    refine ⟨by omega,by rw [hstart]; omega,?_⟩
    simp only [hk,Nat.reduceBEq,Bool.true_and,hstart,Int.toNat_natCast]
    rw [hw.1,hw.2,hbody,hq,hp]
    simp only [List.append_assoc,List.drop_append_length,List.take_cons,List.take_zero]
    exact FieldPayloadEdit.insert _ bitmap (by split <;> decide) hb clear
  · have hstart : (sourceFieldStart I Q st (nWin pre) (fieldsLen pre)).toNat=
        fieldsLen pre-(if st=7 ∧ nWin pre≠0 ∧ I.ts=1 then 32 else 0) := by
      simp [sourceFieldStart,hk]; split <;> omega
    have hnonneg : 0≤sourceFieldStart I Q st (nWin pre) (fieldsLen pre) := by
      by_cases hs : st=7
      · subst st
        have hw := field_start_window f pre post width he
        rw [hheader] at hw
        simp [sourceFieldStart,hk]; split <;> omega
      · simp [sourceFieldStart,hk,hs]
    refine ⟨by omega,hnonneg,?_⟩
    have hcpfalse : (Q.kind==5 && st==6)=false := by simp [hbm]
    simp only [hcpfalse,hstart]
    have hbytes : (Q.q.drop (fieldsLen pre)).take width=
        (Q.pb.drop (fieldsLen pre-(if st=7 ∧ nWin pre≠0 ∧ I.ts=1 then 32 else 0))).take width := by
      by_cases hs : st=7
      · subst st
        have hw := field_start_window f pre post width he
        rw [hheader] at hw
        have htarget : ¬((nWin pre=0 ∧ I.ts=1) ∨ (nWin pre+1=nWin Q.shape ∧ I.ts≠1)) := by
          simp [CpB,VcpB,WfrB,TgtB,FwB,LastwB,S15B,hk] at hc
          omega
        by_cases hs : I.ts=1
        · have hw0 : nWin pre≠0 := by omega
          rw [if_pos (show 7=7 ∧ nWin pre≠0 ∧ I.ts=1 from ⟨rfl,hw0,hs⟩)]
          rw [hq,hp]
          simp only [hs,ite_true]
          have hlo : body.length+2+32≤fieldsLen pre := by omega
          have hhi : fieldsLen pre+width≤body.length+2+32+rest.length := by omega
          rw [←List.append_assoc (body++_) child rest]
          rw [slice_after_prefix ((body++_)++child) rest newMem (fieldsLen pre) width
            (by simp [hch];omega) (by simp [hch];omega)]
          rw [slice_after_prefix (body++_) rest oldMem (fieldsLen pre-32) width
            (by simp;omega) (by simp;omega)]
          congr 2
          simp [hch]; omega
        · simp only [hs,and_false,ite_false,Nat.sub_zero]
          rw [hq,hp]
          simp only [hs,ite_false]
          rw [←List.append_assoc (body++_) rest child,List.append_assoc _ child newMem]
          rw [slice_after_prefix (body++_) rest (child++newMem) (fieldsLen pre) width
            (by simp;omega) (by simp;omega)]
          rw [slice_after_prefix (body++_) rest oldMem (fieldsLen pre) width
            (by simp;omega) (by simp;omega)]
          simp
      · have hnot : (st,width)∉(6,2)::(List.replicate (nWin Q.shape) (7,32)++[(8,8)]) := by
          simp [List.mem_replicate,hs,hbm,hnmem]
        have hu := field_headBytes_bound (branchPrefix Q.ty) _ pre post (st,width) (hshape.symm.trans he) hnot
        rw [hbody] at hu
        simp only [hs,false_and,ite_false,Nat.sub_zero]
        rw [hq,hp]
        simpa only [List.append_assoc] using slice_common_headBytes body _ _ (fieldsLen pre) width hu
    rw [←hbytes]
    exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
