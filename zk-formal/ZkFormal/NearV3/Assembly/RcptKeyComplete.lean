import ZkFormal.NearV3.Assembly.RcptKeyAccessPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem key_header_character_commute (fallback : ListPlan→Coord→Nat→Fp) :
    keyHeaderAux (characterHeaderAux fallback)=characterHeaderAux (keyHeaderAux fallback) := by
  funext p row col
  by_cases hc : col∈[gKA,gKB,kz,gF,gAK]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  · simp only [keyHeaderAux,characterHeaderAux,if_neg hc]

theorem key_constraints_cover (e : Expr) (he : e∈cKey) :
    e∈keyGateConstraints ∨ e∈keyAccountCurrent ∨ e=keyZeroConstraint ∨ e∈keyAccessCurrent := by
  simp only [cKey,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [keyGateConstraints,keyAccountCurrent,keyZeroConstraint,keyAccessCurrent,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem booleanReceiptTrace_key (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈cKey,e.eval (booleanReceiptTrace own ctx lists log
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))) pub digests
      (characterAux (keyAux accountId accessId fallback)) (characterHeaderAux (keyHeaderAux headerFallback))) 0 pos pub=0 := by
  intro e he
  rcases key_constraints_cover e he with he|he|rfl|he
  · simpa only [key_character_commute,key_header_character_commute] using
      booleanReceiptTrace_keyGates own ctx lists hw log pos accountId accessId constants pub digests
        (characterAux fallback) (characterHeaderAux headerFallback) e he
  · exact booleanReceiptTrace_keyAccount own ctx lists hw log pos accountId accessId
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))) pub digests fallback headerFallback e he
  · simpa only [key_character_commute,key_header_character_commute] using
      booleanReceiptTrace_keyZero own ctx lists log pos accountId accessId
        (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))) pub digests
        (characterAux fallback) (characterHeaderAux headerFallback) hcap
  · exact booleanReceiptTrace_keyAccess own ctx lists hw log pos accountId accessId constants pub digests fallback headerFallback e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
