import ZkFormal.NearV3.Assembly.RcptTokenWindows

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RoutingBoundedLayout

def tokenAux (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if tok 0≤col ∧ col<tok 16 then Fp.ofNat ((tokenOf (tokens plan) row (col-tok 0)).toNat) else
  if row.state=sGP ∧ xb 31≤col ∧ col<xb 39 then
    frameBit (((tokens plan).newBytes.getD row.index 0).toNat) (col-xb 31)
  else fallback plan row col

def tokenReceiptAux (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    ReceiptPlan→Coord→Nat→Fp := streamAux pub digests (tokenAux tokens fallback)

theorem receipt_token_cell (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (j : Nat) (hj : j<16) :
    receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan row (tok j)=
      Fp.ofNat ((tokenOf (tokens plan) row j).toNat) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl

theorem receipt_token_bit (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (pos j : Nat) (hj : j<8) :
    receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan ⟨sGP,pos,16⟩ (xb (31+j))=
      frameBit (((tokens plan).newBytes.getD pos 0).toNat) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases he with h|h|h|h|h|h|h|h <;> subst j <;> rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
