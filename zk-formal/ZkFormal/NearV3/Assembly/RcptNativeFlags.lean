import ZkFormal.NearV3.Assembly.RcptStateCoverage

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Exactly the surplus used by native TransferV1.applyReceipt. -/
def nativeSurplus (ctx : ApplyCtx) (r : Receipt) : Nat :=
  Params.G * (r.gasPrice-min r.gasPrice ctx.gasPrice)

/-- System receipts do not emit refunds; ordinary receipts emit precisely when
native gas-price surplus is nonzero. -/
def nativeRefund (ctx : ApplyCtx) (r : Receipt) : Bool :=
  !(r.predecessorId == AccountId.system) && decide (nativeSurplus ctx r ≠ 0)

def nativeInput (ctx : ApplyCtx) (r : Receipt) : Input := ⟨r,nativeRefund ctx r⟩
def nativeInputs (ctx : ApplyCtx) (rs : List (List Receipt)) : List (List Input) :=
  rs.map (List.map (nativeInput ctx))

/-- The ge flag compares receipt and block gas prices, independently of the
refund flag; the latter also excludes the system branch. -/
def nativePriceConstants (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=ge then bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice)) else fallback p col

theorem nativeRefund_price (ctx : ApplyCtx) (r : Receipt)
    (h : nativeRefund ctx r=true) : ctx.gasPrice≤r.gasPrice := by
  have hn : nativeSurplus ctx r≠0 := by
    simpa only [nativeRefund,Bool.and_eq_true,decide_eq_true_eq] using (Bool.and_eq_true_iff.mp h).2
  by_cases hh : ctx.gasPrice≤r.gasPrice
  · exact hh
  · have hm : min r.gasPrice ctx.gasPrice=r.gasPrice := Nat.min_eq_left (by omega)
    simp [nativeSurplus,hm] at hn

theorem nativeRefund_system (ctx : ApplyCtx) (r : Receipt)
    (h : r.predecessorId=AccountId.system) : nativeRefund ctx r=false := by
  simp [nativeRefund,h]

theorem nativeInputs_receipts (ctx : ApplyCtx) (rs : List (List Receipt)) :
    (nativeInputs ctx rs).flatten.map Input.receipt=rs.flatten := by
  induction rs with
  | nil => rfl
  | cons xs rs ih =>
    simpa [nativeInputs,List.map_flatten,List.map_map,Function.comp_def,nativeInput] using ih

theorem nativeInputs_flags (ctx : ApplyCtx) (rs : List (List Receipt)) :
    ∀xs∈nativeInputs ctx rs,∀x∈xs,x.refund=nativeRefund ctx x.receipt := by
  intro xs hxs x hx
  obtain ⟨ys,_,rfl⟩ := List.mem_map.mp hxs
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
