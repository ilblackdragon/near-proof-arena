import ZkFormal.NearV3.Assembly.RcptTokenGas

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem tokenOf_internal (x : TokenInput) (row : Coord) (hs : row.state≠sGP) (j : Nat) :
    tokenOf x (advance row) j=tokenOf x row j := by
  cases row
  simp_all [tokenOf,advance]

theorem nonGas_field_order (refund : Bool) :
    ((fields refund).zip ((fields refund).drop 1)).all (fun (s,t)=>
      decide (s=sGP ∨ (s<sGP ∧ t≤sGP) ∨ (sGP<s ∧ sGP<t)))=true := by
  cases refund <;> decide

theorem tokenOf_field_boundary (x : TokenInput) (input : Input) {s t i len len' j : Nat}
    (hs : s≠sGP) (hj : j<16)
    (ht : (s,t)∈(fields input.refund).zip ((fields input.refund).drop 1)) :
    tokenOf x ⟨t,0,len'⟩ j=tokenOf x ⟨s,i,len⟩ j := by
  have ho := List.all_eq_true.mp (nonGas_field_order input.refund) (s,t) ht
  have ho' : (s<sGP ∧ t≤sGP) ∨ (sGP<s ∧ sGP<t) := by simpa [hs] using ho
  rcases ho' with ⟨hsl,htl⟩|⟨hsg,htg⟩
  · by_cases he : t=sGP
    · subst t
      simp only [tokenOf,if_pos hsl,ite_true,show ¬sGP<sGP by omega,ite_false]
      exact token_window_start x j hj
    · have hlt : t<sGP := by omega
      simp only [tokenOf,if_pos hsl,if_pos hlt]
  · have hsn : ¬s<sGP := by omega
    have htn : ¬t<sGP := by omega
    have hte : t≠sGP := by omega
    simp only [tokenOf,if_neg hsn,if_neg htn,if_neg hs,if_neg hte]

def carryTokenConstraints : List Expr := (List.range 16).map fun j=>
  .mul (sub (sub (c act) (c sGP)) (c lastR)) (sub (n (tok j)) (c (tok j)))

theorem carryToken_in_regs : ∀e∈carryTokenConstraints,e∈cRegs := by
  intro e he
  exact List.mem_append_right _ he

/-- This ordinary byte-level phase relation is discharged internally and at
all generated non-GP field boundaries by the lemmas above. Cross-receipt/header
instances still require the constructed running-total relation. -/
theorem receipt_token_carry (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row next : Coord)
    (ht : ∀j,j<16→tokenOf (tokens plan) next j=tokenOf (tokens plan) row j) :
    ∀e∈carryTokenConstraints,e.eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan row next) 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul,eval_sub,eval_c,eval_n]
  change _*(receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan next (tok j)-
    receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan row (tok j))=0
  rw [receipt_token_cell _ _ _ _ _ _ _ j hj',receipt_token_cell _ _ _ _ _ _ _ j hj',ht j hj']
  grind only

theorem receipt_token_carry_internal (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord) (hs : row.state≠sGP) :
    ∀e∈carryTokenConstraints,e.eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan row (advance row)) 0 0 pub=0 := by
  exact receipt_token_carry constants pub digests tokens fallback plan row (advance row)
    (fun j _=>tokenOf_internal _ row hs j)

theorem receipt_token_carry_field (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) {s t i len len' : Nat}
    (hs : s≠sGP) (ht : (s,t)∈(fields plan.input.refund).zip ((fields plan.input.refund).drop 1)) :
    ∀e∈carryTokenConstraints,e.eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan ⟨s,i,len⟩ ⟨t,0,len'⟩) 0 0 pub=0 := by
  exact receipt_token_carry constants pub digests tokens fallback plan _ _
    (fun j hj=>tokenOf_field_boundary _ plan.input hs hj ht)

end ZkFormal.NearV3.Assembly.RcptSkeleton
