import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowGeneratedRow
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowReadBounds
import ZkFormal.NearV3.Render.Ups.AcceptedTrafficList

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render Render.UpsGen Render.UpsRelay UpsRows

/-- Decode the actual generated read gate without assuming integer/field cast
injectivity for arbitrary cells: this register is an explicit indicator. -/
theorem qCell_read_gate (I : UpsInst) (k p u : Nat)
    (h : (qCell I k p u UpsV3.rd : Fp)=1) :
    rdV I (part I k) (fieldAt (part I k).shape p).1
      (fieldAt (part I k).shape p).2.1 (fieldAt (part I k).shape p).2.2.2=1 := by
  change (rdV I (part I k) (fieldAt (part I k).shape p).1
    (fieldAt (part I k).shape p).2.1 (fieldAt (part I k).shape p).2.2.2 : Fp)=1 at h
  unfold rdV ind at h ⊢
  split <;> rename_i hb
  · rfl
  · rw [ite_eq_right hb] at h
    exact False.elim ((by decide : (0 : Fp)≠1) h)

/-- Actual compact-table reads resolve to a bounded byte of a nonfresh source
part and exactly the mapped native UPB key. -/
theorem compact_read_address (insts : List UpsInst)
    (hi : ∀I∈insts,InstOk I ∧ NativePartFamily I)
    (hroom : ∀I∈insts,∀k,k<nQ I→(part I k).phk+9≤(part I k).pb.length)
    (t r : Nat) (hr : (Candidates.CompactHeight.trace insts).cell t r UpsV3.rd=1) :
    ∃i k p pos,i<insts.length ∧ k<nQ (inst insts i) ∧
      p<(part (inst insts i) k).q.length ∧ (part (inst insts i) k).kind≠8 ∧
      pos<(part (inst insts i) k).pb.length ∧
      windowFieldKey (Candidates.CompactHeight.trace insts) t r=
        (readerSourceKey (part (inst insts i) k) pos).map Fp.ofNat := by
  obtain ⟨i,k,p,hi',hk,hp,hrow,hcells⟩:=compact_read_part insts t r hr
  have him : inst insts i∈insts := by
    simp only [inst,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi',Option.getD_some]
    exact List.getElem_mem hi'
  obtain ⟨hok,hfamily⟩:=hi _ him
  obtain ⟨⟨bytes⟩,hf,hplan,_⟩:=hfamily k hk
  have hg:=qCell_read_gate _ k p (compactU insts r)
    ((hcells UpsV3.rd (by decide)).symm.trans hr)
  obtain ⟨hkind,hpos,hlt⟩:=window_read_bounds hf bytes.sourceLayout hplan bytes.copyFields
    (hok.bits k hk).2.2.2 (hroom _ him k hk) hp hg
  have hactive : r<compactR insts := by
    have hm : (compactRecs insts).getD r default∈compactRecs insts :=
      compact_mem.mpr (by rw [hrow]; exact ⟨hi',compact_mem_I.mpr (Or.inr ⟨k,p,hk,hp,rfl⟩)⟩)
    by_cases ha : r<compactR insts
    · exact ha
    · have hz:=compact_pad (by omega : compactR insts≤r) UpsV3.rd
      change (compactCell insts r UpsV3.rd : Fp)=1 at hr
      rw [hz] at hr
      exact False.elim ((by decide : (0 : Fp)≠1) hr)
  exact ⟨i,k,p,_,hi',hk,hp,hkind,hlt,compact_part_window_key insts t r i k p hactive hrow hpos⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
