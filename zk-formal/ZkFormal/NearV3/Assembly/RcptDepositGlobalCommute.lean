import ZkFormal.NearV3.Assembly.RcptDepositFinalCommute
import ZkFormal.NearV3.Assembly.RcptCandidateGasProductNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def completeReceiptConstants (ctx : ApplyCtx) (k : WalkD0) (accountId : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) : ReceiptPlan→Nat→Fp :=
  nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants)))))

def completeReceiptHeaders (fallback : ListPlan→Coord→Nat→Fp) : ListPlan→Coord→Nat→Fp :=
  digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux fallback))))

def completeReceiptAux (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) : ReceiptPlan→Coord→Nat→Fp :=
  digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux
    (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasBorrowAux ctx
      (gasEffectiveAux ctx (candidateGasDelayAux ctx (gasFlagAux ctx
        (gasTokenAux (receiptPlanToken ctx lists) (gasProductAux ctx fallback)))))))))))))

theorem depositFinal_complete_aux (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (completeReceiptAux ctx k lists accountId accessId fallback)=
      completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback) := by
  simp only [completeReceiptAux,depositFinal_digest_commute,depositFinal_character_commute,
    depositFinal_length_commute,depositFinal_predecessor_commute,depositFinal_named_commute,
    depositFinal_system_commute,depositFinal_routing_commute,depositFinal_key_commute,
    ←depositFinal_borrow_commute,←depositFinal_effective_commute,←depositFinal_delay_commute,
    ←depositFinal_flag_commute,←depositFinal_token_commute,←depositFinal_product_commute]

theorem depositFinal_complete_constants (ctx : ApplyCtx) (k : WalkD0) (accountId : ReceiptPlan→Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account) (constants : ReceiptPlan→Nat→Fp) :
    depositConstants accounts (depositAgeConstants previous (completeReceiptConstants ctx k accountId constants))=
      completeReceiptConstants ctx k accountId (depositConstants accounts (depositAgeConstants previous constants)) := by
  funext p col
  by_cases hb : col=big
  · subst col
    simp [depositConstants,depositAgeConstants,completeReceiptConstants,nativePriceConstants,
      systemConstants,systemIdentityConstants,keyConstants,nativeRoutingConstants,gasEffectiveConstants,
      big,tprev,ge,sys,ee,dm,dd,kslot,q,gq]
  · by_cases ht : col=tprev
    · subst col
      simp [depositConstants,depositAgeConstants,completeReceiptConstants,nativePriceConstants,
        systemConstants,systemIdentityConstants,keyConstants,nativeRoutingConstants,gasEffectiveConstants,
        big,tprev,ge,sys,ee,dm,dd,kslot,q,gq]
    · simp only [depositConstants,depositAgeConstants,completeReceiptConstants,nativePriceConstants,
        systemConstants,systemIdentityConstants,keyConstants,nativeRoutingConstants,gasEffectiveConstants,
        if_neg hb,if_neg ht]

theorem depositFinal_complete_headers (fallback : ListPlan→Coord→Nat→Fp) :
    depositHeaderAux (completeReceiptHeaders fallback)=completeReceiptHeaders (depositHeaderAux fallback) := by
  funext p row col
  unfold depositHeaderAux completeReceiptHeaders digestHeaderMetadata characterHeaderAux systemHeaderAux routingHeaderAux keyHeaderAux
  by_cases h : col=r1 ∨ col=st
  · rcases h with rfl|rfl <;> simp [r1,st,gDg,gV,gS,gBd,gKA,gKB,kz,gF,gAK]
  · simp only [h,ite_false]

end ZkFormal.NearV3.Assembly.RcptSkeleton
