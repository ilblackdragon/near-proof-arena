import ZkFormal.NearV3.Assembly.RcptStateCurrent

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem continuation_gated (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hh : oneHotConstraint.eval tr 0 pos pub=0)
    (hg : tr.cell 0 pos act=0 ∨ tr.cell 0 pos fe=1) :
    ∀e∈continuationConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [continuationConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl|rfl|rfl)|he
  · exact hh
  · simp only [eval_mul3,eval_c,eval_not]
    rcases hg with hg|hg <;> rw [hg] <;> grind only
  · simp only [eval_mul3,eval_c,eval_not]
    rcases hg with hg|hg <;> rw [hg] <;> grind only
  · obtain ⟨s,_,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul3,eval_c,eval_not]
    rcases hg with hg|hg <;> rw [hg] <;> grind only

theorem booleanReceiptTrace_continuation (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈continuationConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  have hh := booleanReceiptTrace_oneHot own ctx lists log pos constants pub digests fallback headerFallback
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    apply continuation_gated _ pos pub hh
    exact Or.inl (by simpa only [ha] using hc act (by decide))
  | some a =>
    by_cases hend : (eraseRow a).index+1=(eraseRow a).length
    · apply continuation_gated _ pos pub hh
      apply Or.inr
      rw [hc fe (by decide),ha]
      simp [controlCell,fe,idx,act,fs,hend]
    · have hi := planned_row_coord_bound lists a (List.mem_of_getElem? ha)
      have hin : (eraseRow a).index+1<(eraseRow a).length := by omega
      cases hb : (plannedRows lists)[pos+1]? with
      | none =>
        obtain ⟨p,_,row,_,hl,he,hea⟩ := planned_before_padding lists pos a ha hb
        rw [hea,p.erase_wrap] at hin
        omega
      | some b =>
        have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hb).1 hcap
        have hnext : eraseRow b=advance (eraseRow a) := by
          rcases planned_index_neighbor_shape lists pos a b ha hb with
            ⟨p,_,row,_,_,_,hea,heb⟩|⟨p,row,_,hl,he,hea⟩
          · rw [hea,heb,p.erase_wrap,p.erase_wrap]
          · rw [hea,p.erase_wrap] at hin;omega
        intro e he
        rw [control_eval_agree _ (controlPair (eraseRow a) (advance (eraseRow a))) 0 pos 0 0 pub ?_ ?_ e
          (List.all_eq_true.mp continuation_footprint e he)]
        · exact control_continuation (eraseRow a) (planned_row_state lists a (List.mem_of_getElem? ha)) hin pub e he
        · intro col hcol
          simpa only [ha,controlPair,ite_true] using hc col hcol
        · intro col hcol
          have hn := booleanReceiptTrace_control own ctx lists log (pos+1) constants pub digests fallback headerFallback col hcol
          have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
          simp only [ht,Nat.mod_eq_of_lt hpos]
          simpa only [hb,hnext,controlPair,Trace.height,Nat.reducePow,Nat.reduceAdd,Nat.reduceMod,show ¬(1=0) by decide,ite_false] using hn

theorem continuationConstraints_count : continuationConstraints.length=26 := by decide

theorem booleanReceiptTrace_regs_emit_bool_continuation (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs++cEmit++booleanConstraints++continuationConstraints,
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_regs_emit_bool own ctx lists hw log constants pub digests fallback headerFallback hcap hown pos hp e he
  · exact booleanReceiptTrace_continuation own ctx lists log pos constants pub digests fallback headerFallback hcap e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
