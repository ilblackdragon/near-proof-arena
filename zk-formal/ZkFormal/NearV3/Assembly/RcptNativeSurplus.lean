import ZkFormal.NearV3.Assembly.RcptSystemGasCandidate
import ZkFormal.NearV3.Assembly.RcptTokenLedger

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

/-- Ordinary native execution explicitly checks the refund product. This bound
must not be required of the unmasked system-branch price difference. -/
theorem applyReceipt_surplus_bound (ctx : Ctx) (st out : Acc) (r : Receipt)
    (h : applyReceipt ctx st r=some out) :
    Params.G*(r.gasPrice-min r.gasPrice ctx.blockGasPrice)<Params.two128 := by
  unfold applyReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h);split at h))
  all_goals simp_all only [Bool.or_eq_true,decide_eq_true_eq,not_or]
  all_goals omega

/-- The corrected gas product is the amount actually refunded by this branch. -/
def nativeRefundAmount (ctx : ApplyCtx) (r : Receipt) : Nat :=
  if r.predecessorId==AccountId.system then 0 else nativeSurplus ctx r

theorem nativeRefundAmount_system (ctx : ApplyCtx) (r : Receipt)
    (h : r.predecessorId=AccountId.system) : nativeRefundAmount ctx r=0 := by
  simp [nativeRefundAmount,h]

theorem nativeRefundAmount_ordinary (ctx : ApplyCtx) (r : Receipt)
    (h : r.predecessorId≠AccountId.system) : nativeRefundAmount ctx r=nativeSurplus ctx r := by
  simp [nativeRefundAmount,h]

theorem nativeRefundAmount_bound (ctx : ApplyCtx) (st out : Acc) (r : Receipt)
    (h : r.predecessorId=AccountId.system ∨
      applyReceipt ⟨ctx.height,ctx.gasPrice⟩ st r=some out) :
    nativeRefundAmount ctx r<256^16 := by
  rcases h with hs|ho
  · rw [nativeRefundAmount_system ctx r hs];decide
  · unfold nativeRefundAmount
    split
    · decide
    · exact applyReceipt_surplus_bound _ _ _ _ ho

/-- Every actual native batch supplies the corrected product bound, without
any artificial system-receipt gas-price restriction. -/
theorem applyReceipts_refund_amount_bounds (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (st out : Acc×List Limit),
      applyReceipts ctx i st rs=.ok out →
      ∀r∈rs,nativeRefundAmount ctx r<256^16
  | [],_,_,_,_ => by simp
  | r::rs,i,(acc,ls),out,h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · rename_i hr
        obtain ⟨acc',_,h⟩ := Sched.bind_ok h
        have ih := applyReceipts_refund_amount_bounds ctx rs (i+1) (acc',ls) out h
        intro x hx
        rcases List.mem_cons.mp hx with rfl|hx
        · simp [nativeRefundAmount,hr]
        · exact ih x hx
      · split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := Sched.bind_ok h
          have ih := applyReceipts_refund_amount_bounds ctx rs (i+1) (acc',ls') out h
          intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact nativeRefundAmount_bound ctx acc acc' _ (Or.inr ha)
          · exact ih x hx

end ZkFormal.NearV3.Assembly.RcptSkeleton
