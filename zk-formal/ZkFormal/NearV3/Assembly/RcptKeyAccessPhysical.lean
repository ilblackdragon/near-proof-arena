import ZkFormal.NearV3.Assembly.RcptKeyAccessLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem keyAccess_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (ht : tr.cell 0 pos sT0=0) (hl : tr.cell 0 pos sSL=0)
    (hs : tr.cell 0 pos sS=0) (hk : tr.cell 0 pos sKT=0)
    (hp : tr.cell 0 pos sPK=0) (hg : tr.cell 0 pos sGP=0) :
    ∀e∈keyAccessCurrent,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [keyAccessCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_mul,eval_mul3,eval_c,ht,hl,hs,hk,hp,hg]
  all_goals grind only

theorem booleanReceiptTrace_keyAccess (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈keyAccessCurrent,e.eval (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))) pub digests
      (characterAux (keyAux accountId accessId fallback)) (characterHeaderAux (keyHeaderAux headerFallback))) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp keyAccessCurrent_footprint.2 e he)]
  apply plannedTrace_current_bounded_family lists hw log pos _ _ _ pub keyAccessCurrent keyAccessCurrent_footprint.1
    (fun p row _ hw _ hi=>receipt_key_access_current ctx lists accountId accessId constants pub digests fallback p row hw hi) ?_ ?_ e he
  · intro p i
    exact keyAccess_zero _ _ _ rfl rfl rfl rfl rfl rfl
  · exact keyAccess_zero _ _ _ rfl rfl rfl rfl rfl rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
