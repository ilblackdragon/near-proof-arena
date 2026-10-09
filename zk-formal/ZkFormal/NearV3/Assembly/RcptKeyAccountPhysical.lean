import ZkFormal.NearV3.Assembly.RcptCurrentBoundedFamily

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem keyAccount_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hv : tr.cell 0 pos sV=0) (hr : tr.cell 0 pos sRID=0)
    (hl : tr.cell 0 pos sVL=0) (hk : tr.cell 0 pos kz=0) :
    ∀e∈keyAccountCurrent,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [keyAccountCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_mul,eval_mul3,eval_c,hv,hr,hl,hk]
  all_goals grind only

theorem booleanReceiptTrace_keyAccount (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈keyAccountCurrent,e.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (characterAux (keyAux accountId accessId fallback)) (characterHeaderAux (keyHeaderAux headerFallback))) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp keyAccountCurrent_footprint.2 e he)]
  apply plannedTrace_current_bounded_family lists hw log pos _ _ _ pub keyAccountCurrent keyAccountCurrent_footprint.1
    (fun p row _ hw _ hi=>receipt_key_account_current ctx lists accountId accessId constants pub digests fallback p row hw hi) ?_ ?_ e he
  · intro p i
    apply keyAccount_zero _ _ _ (by rfl) (by rfl) (by rfl)
    change boolInput kz 0=0
    exact boolInput_preserves _ _ (Or.inl rfl)
  · exact keyAccount_zero _ _ _ rfl rfl rfl rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
