import ZkFormal.NearV3.Assembly.RcptKeyGateLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyHeaderAux (fallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col∈[gKA,gKB,kz,gF,gAK] then 0 else fallback p row col

theorem keyGate_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : ∀col∈[sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,rf,gKA,gKB,kz,gF,gAK],tr.cell 0 pos col=0) :
    ∀e∈keyGateConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [keyGateConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_sub,eval_add,eval_mul,eval_mul3,eval_not,eval_sum_cons,eval_sum_nil,eval_c,
    hz sV (by decide),hz sRID (by decide),hz sT0 (by decide),hz sSL (by decide),hz sS (by decide),
    hz sKT (by decide),hz sPK (by decide),hz sGP (by decide),hz rf (by decide),hz gKA (by decide),
    hz gKB (by decide),hz kz (by decide),hz gF (by decide),hz gAK (by decide)]
  all_goals grind only

theorem booleanReceiptTrace_keyGates (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈keyGateConstraints,e.eval (booleanReceiptTrace own ctx lists log
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants))))
      pub digests (keyAux accountId accessId fallback) (keyHeaderAux headerFallback)) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp keyGate_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub keyGateConstraints keyGate_footprint.1
    (fun p row _ _=>receipt_key_gates ctx accountId accessId constants pub digests (receiptPlanToken ctx lists) fallback p row) ?_ ?_ e he
  · intro p i
    apply keyGate_zero
    intro col hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | rfl | exact boolInput_preserves _ _ (Or.inl rfl)
  · exact keyGate_zero _ _ _ (by intro col _;rfl)

end ZkFormal.NearV3.Assembly.RcptSkeleton
