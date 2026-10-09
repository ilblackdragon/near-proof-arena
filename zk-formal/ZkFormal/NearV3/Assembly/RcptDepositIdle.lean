import ZkFormal.NearV3.Assembly.RcptDepositEndpoint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxHeartbeats 2000000
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def depositHeaderAux (fallback : ListPlan→Coord→Nat→Fp)
    (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col=r1 ∨ col=st then 0 else fallback p row col

theorem deposit_receipt_idle (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hs : row.state≠sDEP) :
    let cell := receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous (depositAux accounts fallback)))) p row
    cell r1=0 ∧ cell st=0 := by
  constructor
  all_goals simp +decide [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,
    depositAgeAux,depositAux,hs,bitCell,boolInput,beq_eq_false_iff_ne.mpr hs]

theorem deposit_header_idle (own : Nat) (burn : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord) :
    let cell := headerCell (headerStreamAux own burn
      (emissionHeaderFallback (booleanHeaderAux (depositHeaderAux fallback)))) p row
    cell r1=0 ∧ cell st=0 := ⟨rfl,rfl⟩

theorem deposit_next_current (col : Nat) (hc : depositCandidateNext col=true) : depositCandidateColumn col=true := by
  simp only [depositCandidateNext,Bool.or_eq_true,decide_eq_true_eq] at hc
  rcases hc with (hc|hc)|hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · have hb : xb 0≤col ∧ col<xb 66 := by simp only [xb] at hc ⊢;omega
    simp only [depositCandidateColumn,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inl (Or.inr hb)
  · simp only [depositCandidateColumn,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
