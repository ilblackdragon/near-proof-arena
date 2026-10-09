import ZkFormal.NearV3.Assembly.RcptDigestMetadataLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem header_digestMetadata (aux : ListPlan→Coord→Nat→Fp) (p : ListPlan) (i : Nat)
    (pub : List Fp) (hg : aux p ⟨sCL,i,12⟩ gDg=0) :
    ∀e∈digestMetadataConstraints,
      e.eval (⟨fun _=>1,fun _ _ col=>headerCell aux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0 := by
  have hx : headerCell aux p ⟨sCL,i,12⟩ sXRI=0 := rfl
  have hl : headerCell aux p ⟨sCL,i,12⟩ sXLH=0 := rfl
  have hd : headerCell aux p ⟨sCL,i,12⟩ gDg=0 := hg
  intro e he
  simp only [digestMetadataConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl <;>
    simp only [eval_sub,eval_mul,eval_mul3,eval_add,eval_c]
  all_goals change _=0
  all_goals simp only [hx,hl,hd]
  all_goals grind only

theorem booleanReceiptTrace_digestMetadata (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈digestMetadataConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests (digestMetadata fallback)
        (digestHeaderMetadata headerFallback)) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp digestMetadataConstraints_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub digestMetadataConstraints
    digestMetadataConstraints_footprint.1 ?_ ?_ ?_ e he
  · intro p row _ _
    apply receipt_digestMetadata
    · simpa only [tokenReceiptAux,streamAux,tokenAux,reg,tok,xb,gDg,b,
        Nat.reduceAdd,Nat.reduceLT,Nat.reduceEqDiff,and_false,and_true,↓reduceIte] using digestMetadata_gate fallback p row
    · simp only [tokenReceiptAux,streamAux,tokenAux,reg,tok,xb,dI,b,
        Nat.reduceAdd,Nat.reduceLT,Nat.reduceEqDiff,and_false,and_true,↓reduceIte]
      rfl
    · simp only [tokenReceiptAux,streamAux,tokenAux,reg,tok,xb,dL,b,
        Nat.reduceAdd,Nat.reduceLT,Nat.reduceEqDiff,and_false,and_true,↓reduceIte]
      rfl
  · intro p i
    apply header_digestMetadata
    change boolInput gDg 0=0
    exact boolInput_preserves _ _ (Or.inl rfl)
  · intro e he
    simp only [digestMetadataConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl <;>
      simp only [eval_sub,eval_mul,eval_mul3,eval_add,eval_c,zeroCurrentTrace] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
