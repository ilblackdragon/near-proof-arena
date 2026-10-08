import ZkFormal.NearV3.Assembly.RcptNativeStates

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Exact receipt-indexed RID/PEO digest request metadata. Digest bytes remain
provided by the native SHA stream; this constructor only fixes request keys. -/
def digestMetadata (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if col=gDg then bitCell (row.index==0 && (row.state==sXRI || row.state==sXLH)) else
  if col=dI then if row.state=sXRI then Fp.ofNat K_RID+16*Fp.ofNat p.receiptIndex
    else Fp.ofNat K_PEO+16*Fp.ofNat p.receiptIndex else
  if col=dL then if row.state=sXRI then 48
    else 37+32*bitCell p.input.refund+Fp.ofNat p.input.receipt.receiverId.length else
  fallback p row col

def digestHeaderMetadata (fallback : ListPlan→Coord→Nat→Fp)
    (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col=gDg then 0 else fallback p row col

def digestMetadataConstraints : List Expr :=
  [sub (c gDg) (.mul (c fs) (.add (c sXRI) (c sXLH))),
    mul3 (c fs) (c sXRI) (sub (c dI) (mid K_RID (c r))),
    mul3 (c fs) (c sXRI) (sub (c dL) (k 48)),
    mul3 (c fs) (c sXLH) (sub (c dI) (mid K_PEO (c r))),
    mul3 (c fs) (c sXLH) (sub (c dL) (sum [k 37,smul 32 (c hr),c Lv]))]

set_option maxRecDepth 4096 in
theorem digestMetadataConstraints_footprint :
    digestMetadataConstraints.all currentExpr=true ∧
    digestMetadataConstraints.all noEmissionExpr=true := by decide

theorem digestMetadataConstraints_in_end : ∀e∈digestMetadataConstraints,e∈cEnd := by
  intro e he
  simp only [cEnd,List.mem_append]
  exact Or.inr he

theorem digestMetadata_gate (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) :
    booleanReceiptAux (digestMetadata fallback) p row gDg=
      bitCell (row.index==0 && (row.state==sXRI || row.state==sXLH)) := by
  change boolInput gDg (bitCell _)=_
  exact boolInput_preserves _ _ (bitCell_boolean _)

end ZkFormal.NearV3.Assembly.RcptSkeleton
