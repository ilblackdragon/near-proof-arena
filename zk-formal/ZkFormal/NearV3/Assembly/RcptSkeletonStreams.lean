import ZkFormal.NearV3.Assembly.RcptSkeletonShifts

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The two digest-loaded fields are supplied by their SHA message jobs. Other
register streams are computed from the unchanged public/shape load expressions. -/
def receiptStream (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (plan : ReceiptPlan) (state : Nat) : List Fp :=
  if state=sXRI ∨ state=sXLH then digests plan state else registerLoad plan.input pub state

def nativeFieldByte (plan : ReceiptPlan) (row : Coord) : Fp :=
  let r := plan.input.receipt
  let bytes := if row.state=sP then r.predecessorId else if row.state=sV then r.receiverId else
    if row.state=sRID then r.receiptId else if row.state=sS then r.signerId else
    if row.state=sPK then r.signerPk.data else if row.state=sGP then u128 r.gasPrice else
    if row.state=sDEP then u128 r.deposit else []
  Fp.ofNat ((bytes.getD row.index 0).toNat)

def streamAux (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  let data := receiptStream pub digests plan row.state
  if reg 0≤col ∧ col<reg 32 then registerCell data row.index col else
  if col=b then (if row.state∈regStates then data.getD row.index 0 else nativeFieldByte plan row)
  else fallback plan row col

theorem receiptStream_load (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (plan : ReceiptPlan) {state : Nat} {es : List Expr} (hm : (state,es)∈loads) :
    receiptStream pub digests plan state=registerLoad plan.input pub state := by
  have hh : ∀p∈loads,p.1≠sXRI ∧ p.1≠sXLH := by decide
  have hn : state≠sXRI ∧ state≠sXLH := hh (state,es) hm
  simp only [receiptStream,if_neg (show ¬(state=sXRI ∨ state=sXLH) by omega)]

theorem receipt_stream_reg (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row : Coord) (j : Nat) (hj : j<32) :
    receiptCell constants (streamAux pub digests fallback) plan row (reg j)=
      registerCell (receiptStream pub digests plan row.state) row.index (reg j) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22 ∨ j=23 ∨ j=24 ∨ j=25 ∨ j=26 ∨ j=27 ∨ j=28 ∨ j=29 ∨ j=30 ∨ j=31 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl

theorem receipt_stream_byte (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row : Coord) :
    receiptCell constants (streamAux pub digests fallback) plan row b=
      if row.state∈regStates then (receiptStream pub digests plan row.state).getD row.index 0
      else nativeFieldByte plan row := rfl

theorem receipt_stream_head (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row : Coord) (hs : row.state∈regStates) :
    receiptCell constants (streamAux pub digests fallback) plan row b=
      receiptCell constants (streamAux pub digests fallback) plan row (reg 0) := by
  rw [receipt_stream_byte,if_pos hs,receipt_stream_reg _ _ _ _ _ _ 0 (by decide),registerCell_read _ _ 0 (by decide)]
  simp only [Nat.add_zero]

end ZkFormal.NearV3.Assembly.RcptSkeleton
