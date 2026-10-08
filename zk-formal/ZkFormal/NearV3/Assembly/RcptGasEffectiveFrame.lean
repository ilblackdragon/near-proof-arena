import ZkFormal.NearV3.Assembly.RcptGasBorrowNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Actual burn-price bytes: the native system branch burns no tokens. -/
def gasEffectiveByte (ctx : ApplyCtx) (r : Receipt) (i : Nat) : Nat :=
  if r.predecessorId==AccountId.system then 0 else gasByte (min r.gasPrice ctx.gasPrice) i

def gasEffectiveConstants (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=gq then bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice) &&
    !(p.input.receipt.predecessorId==AccountId.system)) else fallback p col

def gasEffectiveAux (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP ∧ col=pc then Fp.ofNat (gasEffectiveByte ctx p.input.receipt row.index)
  else fallback p row col

theorem gasEffectiveByte_lt (ctx : ApplyCtx) (r : Receipt) (i : Nat) : gasEffectiveByte ctx r i<256 := by
  unfold gasEffectiveByte
  split
  · decide
  · exact gasByte_lt _ _

theorem gasPrice_selected_byte (ctx : ApplyCtx) (r : Receipt) (i : Nat) :
    (if ctx.gasPrice≤r.gasPrice then gasByte ctx.gasPrice i else gasByte r.gasPrice i)=
      gasByte (min r.gasPrice ctx.gasPrice) i := by
  by_cases h : ctx.gasPrice≤r.gasPrice
  · rw [if_pos h,Nat.min_eq_right h]
  · rw [if_neg h,Nat.min_eq_left (by omega)]

theorem gasEffective_gate (price system : Bool) :
    bitCell (price && !system)=bitCell price*(1-bitCell system) := by
  cases price <;> cases system <;> simp only [bitCell,Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_true,ite_false] <;> grind only

theorem gasEffective_constant_cells (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) :
    let cn := booleanConstants (nativePriceConstants ctx (systemConstants (gasEffectiveConstants ctx constants)))
    cn p ge=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice)) ∧
    cn p sys=bitCell (p.input.receipt.predecessorId==AccountId.system) ∧
    cn p gq=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice) && !(p.input.receipt.predecessorId==AccountId.system)) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  all_goals change boolInput _ (bitCell _)=_
  all_goals exact boolInput_preserves _ _ (bitCell_boolean _)

theorem gasEffective_cell (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasEffectiveAux ctx fallback))) p ⟨sGP,i,len⟩ pc=
      Fp.ofNat (gasEffectiveByte ctx p.input.receipt i) := rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
