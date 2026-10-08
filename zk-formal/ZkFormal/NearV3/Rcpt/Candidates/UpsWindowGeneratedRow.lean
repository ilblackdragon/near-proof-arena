import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowMessages
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderWindowKey

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open Render
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsGen Render.UpsRelay UpsRows

/-- A physical compact read is a genuine part byte, never padding or a walk row. -/
theorem compact_read_part (insts : List UpsInst) (t r : Nat)
    (hr : (Candidates.CompactHeight.trace insts).cell t r UpsV3.rd=1) :
    ∃ i k p,i<insts.length ∧ k<nQ (inst insts i) ∧
      p<(part (inst insts i) k).q.length ∧
      (compactRecs insts).getD r default=(i,.q k p) ∧
      ∀c,isSeg c=false →
        (Candidates.CompactHeight.trace insts).cell t r c=
          (qCell (inst insts i) k p (compactU insts r) c : Fp) := by
  have ha : r<compactR insts := by
    by_cases hn : r<compactR insts
    · exact hn
    exfalso
    have hz:=compact_pad (by omega : compactR insts≤r) UpsV3.rd
    change (compactCell insts r UpsV3.rd : Fp)=1 at hr
    rw [hz] at hr
    exact (by decide : (0 : Fp)≠1) hr
  have hm:=compact_mem.mp (compact_get_mem ha)
  rcases compact_mem_I.mp hm.2 with ⟨j,hj,hrow⟩ | ⟨k,p,hk,hp,hrow⟩
  · have he : (compactRecs insts).getD r default=
        (((compactRecs insts).getD r default).1,.w j) := Prod.ext rfl hrow
    change (compactCell insts r UpsV3.rd : Fp)=1 at hr
    simp only [compactCell,ha,ite_true,compactRowCell,hrow] at hr
    have hz : isSeg UpsV3.rd=false := by decide
    simp only [hz,Bool.false_eq_true,ite_false] at hr
    exact False.elim ((by decide : (0 : Fp)≠1) hr)
  · refine ⟨_,k,p,hm.1,hk,hp,Prod.ext rfl hrow,?_⟩
    intro c hc
    simp only [Candidates.CompactHeight.trace,compactCell,ha,ite_true,compactRowCell,hc,
      Bool.false_eq_true,ite_false,hrow]

/-- The six generated fields are exactly the source-key payload. Nonnegative
source position is explicit: a cast of a negative address cannot authenticate
an ordinary native byte index. -/
theorem compact_part_window_key (insts : List UpsInst) (t r i k p : Nat)
    (hr : r<compactR insts)
    (hrow : (compactRecs insts).getD r default=(i,.q k p))
    (hpos : 0≤sposV (inst insts i) (part (inst insts i) k)
      (fieldAt (part (inst insts i) k).shape p).1
      (fieldAt (part (inst insts i) k).shape p).2.1
      (fieldAt (part (inst insts i) k).shape p).2.2.2 p) :
    windowFieldKey (Candidates.CompactHeight.trace insts) t r=
      (readerSourceKey (part (inst insts i) k)
        (sposV (inst insts i) (part (inst insts i) k)
          (fieldAt (part (inst insts i) k).shape p).1
          (fieldAt (part (inst insts i) k).shape p).2.1
          (fieldAt (part (inst insts i) k).shape p).2.2.2 p).toNat).map Fp.ofNat := by
  simp only [windowFieldKey,Candidates.CompactHeight.trace,compactCell,hr,ite_true,hrow,
    compactRowCell]
  have castN (n : Nat) : ((n : Int) : Fp)=Fp.ofNat n := rfl
  have castPos (z : Int) (hz : 0≤z) : (z : Fp)=Fp.ofNat z.toNat := by
    exact (congrArg (fun x : Int => (x : Fp)) (Int.toNat_of_nonneg hz)).symm
  simp [qCell,qRowCell,qRow,isSeg,isPC,pcCell,rbV,readerSourceKey,msgId,
    UpsV3.sN,UpsV3.spos,UpsV3.rb,UpsV3.plen,UpsV3.pdep,UpsV3.rcid,
    castN,castPos _ hpos]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
