import ZkFormal.NearV3.Assembly.RcptCharacterLengthLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_characterLengths (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈characterLengthConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests (characterLengthAux fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp characterLengthConstraints_shape.2.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub characterLengthConstraints
    characterLengthConstraints_shape.2.1 ?_ ?_ ?_ e he
  · intro p row hw _ e he
    have hp := receipt_character_length_pair ctx lists constants pub digests fallback p row hw sP Lp (by simp) rfl
    have hv := receipt_character_length_pair ctx lists constants pub digests fallback p row hw sV Lv (by simp) rfl
    have hs := receipt_character_length_pair ctx lists constants pub digests fallback p row hw sS Ls (by simp) rfl
    simp only [characterLengthConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hp.1
    · exact hv.1
    · exact hs.1
    · exact hp.2
    · exact hv.2
    · exact hs.2
  · intro p i e he
    have hp : headerCell (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
        (emissionHeaderFallback (booleanHeaderAux headerFallback))) p ⟨sCL,i,12⟩ sP=0 := rfl
    have hv : headerCell (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
        (emissionHeaderFallback (booleanHeaderAux headerFallback))) p ⟨sCL,i,12⟩ sV=0 := rfl
    have hs : headerCell (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
        (emissionHeaderFallback (booleanHeaderAux headerFallback))) p ⟨sCL,i,12⟩ sS=0 := rfl
    simp only [characterLengthConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [eval_mul3,eval_c]
    all_goals change _=0
    all_goals simp only [hp,hv,hs]
    all_goals grind only
  · intro e he
    simp only [characterLengthConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [eval_mul3,eval_c,zeroCurrentTrace] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
