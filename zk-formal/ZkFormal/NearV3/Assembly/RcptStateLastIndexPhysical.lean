import ZkFormal.NearV3.Assembly.RcptStateLastIndex

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem plannedTrace_lastIndex (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (receiptAux : ReceiptPlan→Coord→Nat→Fp)
    (headerAux : ListPlan→Coord→Nat→Fp) :
    ∀e∈lastIndexConstraints,e.eval (plannedTrace lists log constants receiptAux headerAux) 0 pos []=0 := by
  intro e he
  have hf := List.all_eq_true.mp lastIndexConstraints_footprint.1 e he
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    obtain ⟨⟨s,x⟩,_,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul3,eval_c,plannedTrace_padding lists log pos constants receiptAux headerAux (List.getElem?_eq_none_iff.mp ha) fe]
    grind only
  | some a =>
    have hm := List.mem_of_getElem? ha
    rw [←plannedSegments_rows] at hm
    obtain ⟨seg,_,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨row,hr,hea⟩ := List.mem_map.mp hm
    obtain ⟨hs,_,hl⟩ := segment_member hr
    subst a
    cases seg with
    | header p =>
      change row.state=sCL at hs
      change row.length=12 at hl
      cases row with
      | mk state i len =>
        dsimp only at hs hl
        subst state len
        rw [currentExpr_eval _ (⟨fun _=>1,fun _ _ col=>headerCell headerAux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 pos 0 0 []
          (fun col=>plannedTrace_cell lists log pos constants receiptAux headerAux _ ha col) e hf]
        exact header_lastIndex headerAux p i [] e he
    | receipt p s =>
      have hlen : row.length=fieldLen p.input row.state := by
        change row.state=s at hs
        change row.length=fieldLen p.input s at hl
        rw [hs];exact hl
      rw [currentExpr_eval _ (receiptPair constants receiptAux p row row) 0 pos 0 0 []
        (fun col=>plannedTrace_cell lists log pos constants receiptAux headerAux _ ha col) e hf]
      exact receipt_lastIndex constants receiptAux p row (planned_receipt_wf lists hw p row (List.mem_of_getElem? ha)) hlen [] e he

/-- Last-index expressions use no public cells, so the generic skeleton lemma
extends to arbitrary prepared public inputs. -/
theorem lastIndex_noPub : ∀x∈lastIdx,∀(tr : Trace Fp) (pos : Nat) (pub : List Fp),
    x.2.eval tr 0 pos pub=x.2.eval tr 0 pos [] := by
  intro x hx tr pos pub
  simp only [lastIdx,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx <;>
    cases hx <;> rfl

theorem booleanReceiptTrace_lastIndex (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈lastIndexConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp lastIndexConstraints_footprint.2 e he)]
  have hh := plannedTrace_lastIndex lists hw log pos (booleanConstants constants)
    (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux fallback))
    (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
      (emissionHeaderFallback (booleanHeaderAux headerFallback))) e he
  obtain ⟨⟨s,x⟩,hm,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_sub,eval_c] at hh ⊢
  rw [lastIndex_noPub (s,x) hm]
  exact hh

theorem lastIndexConstraints_count : lastIndexConstraints.length=23 := by decide

theorem booleanReceiptTrace_regs_emit_bool_continuation_lastIndex (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs++cEmit++booleanConstraints++continuationConstraints++lastIndexConstraints,
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_regs_emit_bool_continuation own ctx lists hw log constants pub digests fallback headerFallback hcap hown pos hp e he
  · exact booleanReceiptTrace_lastIndex own ctx lists hw log pos constants pub digests fallback headerFallback e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
