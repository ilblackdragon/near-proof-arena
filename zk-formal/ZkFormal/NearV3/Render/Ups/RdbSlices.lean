import ZkFormal.NearV3.Render.Ups.FieldStart
import ZkFormal.NearV3.Render.Ups.CopyMiddle

namespace ZkFormal.NearV3.Render.UpsGen

/-- A branch-child replacement changes only the chosen first/last child window and MEM. -/
theorem rdb_copy_slices (I : UpsInst) (Q : UpsPartI) (hk : Q.kind=0)
    (f : FieldsOk Q) (sd : Q.sd=0 ∨ Q.sd=1)
    (header rest oldChild newChild oldMem newMem : List Nat)
    (hhead : fieldsLen (nodeHeader Q.ty Q.qhk)=header.length)
    (ho : oldChild.length=32) (hn : newChild.length=32) (hm : newMem.length=8)
    (hq : Q.q=header++(if Q.sd=1 then rest++newChild else newChild++rest)++newMem)
    (hp : Q.pb=header++(if Q.sd=1 then rest++oldChild else oldChild++rest)++oldMem) : CopyFields I Q := by
  have hshape : Q.shape=nodeHeader Q.ty Q.qhk++(List.replicate (nWin Q.shape) (7,32)++[(8,8)]) := by
    rw [←nodeFields_eq_header]; exact f.shape
  have hrest : rest.length+32=32*nWin Q.shape := by
    have hb := f.bytes
    rw [hq,hshape,fieldsLen_append,fieldsLen_windows,hhead] at hb
    rcases sd with sd|sd <;> simp [sd,hn,hm] at hb <;> omega
  constructor
  intro pre post st width he hc
  have hnmem : st≠8 := by intro h; simp [CpB,VcpB,WfrB,hk,h] at hc
  have hstart : sourceFieldStart I Q st (nWin pre) (fieldsLen pre)=(fieldsLen pre : Int) := by simp [sourceFieldStart,hk]
  refine ⟨by omega,by rw [hstart]; omega,?_⟩
  simp only [hk,Nat.reduceBEq,Bool.false_and,hstart,Int.toNat_natCast]
  have hb : (Q.q.drop (fieldsLen pre)).take width=(Q.pb.drop (fieldsLen pre)).take width := by
    by_cases hs : st=7
    · subst st
      have hw := field_start_window f pre post width he
      have ht : ¬((nWin pre=0 ∧ Q.sd≠1) ∨ (nWin pre+1=nWin Q.shape ∧ Q.sd=1)) := by
        simp [CpB,VcpB,WfrB,TgtB,FwB,LastwB,S15B,hk] at hc
        omega
      rcases sd with sd|sd
      · have hl : header.length+32≤fieldsLen pre := by rw [hhead] at hw; omega
        rw [hq,hp]
        simp only [sd,Nat.reduceEqDiff,ite_false]
        rw [←List.append_assoc header newChild rest,←List.append_assoc header oldChild rest]
        exact slice_common_middle (header++newChild) (header++oldChild) rest newMem oldMem
          (fieldsLen pre) width (by simp [hn,ho]) (by simp [hn];omega)
          (by simp [hn]; rw [hhead] at hw;omega)
      · have hu : fieldsLen pre+width≤header.length+rest.length := by rw [hhead] at hw; omega
        rw [hq,hp]
        simp only [sd,ite_true]
        simpa only [List.append_assoc] using slice_common_headBytes (header++rest)
          (newChild++newMem) (oldChild++oldMem) (fieldsLen pre) width (by simpa using hu)
    · have hnot : (st,width)∉List.replicate (nWin Q.shape) (7,32)++[(8,8)] := by simp [List.mem_replicate,hs,hnmem]
      have hb := field_headBytes_bound (nodeHeader Q.ty Q.qhk) _ pre post (st,width)
        (hshape.symm.trans he) hnot
      rw [hhead] at hb
      rw [hq,hp]
      simpa only [List.append_assoc] using slice_common_headBytes header
        ((if Q.sd=1 then rest++newChild else newChild++rest)++newMem)
        ((if Q.sd=1 then rest++oldChild else oldChild++rest)++oldMem)
        (fieldsLen pre) width hb
  rw [←hb]
  exact FieldPayloadEdit.preserve _ _

end ZkFormal.NearV3.Render.UpsGen
