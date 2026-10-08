import ZkFormal.NearV3.Assembly.RcptDepositLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem depositAgeAux_outside (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hc : ¬(xb 53≤col ∧ col<xb 66) ∨ row.index≠0) :
    depositAgeAux previous (depositAux accounts fallback) p row col=depositAux accounts fallback p row col := by
  unfold depositAgeAux
  split
  · rename_i hs
    rcases hs with ⟨hs,hcol⟩
    subst col
    simp only [depositAux,ite_true,hs,beq_self_eq_true,Bool.true_and]
  · have hn : ¬(row.state=sDEP ∧ row.index=0 ∧ xb 53≤col ∧ col<xb 66) := by omega
    rw [if_neg hn]

theorem depositAge_cell_outside (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hc : ¬(xb 53≤col ∧ col<xb 66) ∨ row.index≠0) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous (depositAux accounts fallback)))) p row col=
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p row col := by
  simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,depositAgeAux_outside previous accounts fallback p row col hc]

def depositStorageCheck : Expr :=
  mul3 (Dsl.not (c big)) (c r1) (sub (k 770) (sum [c (dl 0),smul 256 (c st),bitsX 47 10]))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositWithoutAge_overlap :
    depositWithoutAge.filter (fun e=>!(ageIndependent e))=[depositStorageCheck] := by decide

theorem receipt_deposit_agePatch_preserves (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositWithoutAge,e.eval
      (receiptPair (booleanConstants (depositConstants accounts constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous (depositAux accounts fallback))))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  let cn := depositConstants accounts constants
  let tr := receiptPair (booleanConstants cn)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous (depositAux accounts fallback)))) p ⟨sDEP,i,16⟩ next
  let old := receiptPair (booleanConstants cn)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,16⟩ next
  intro e he
  change e.eval tr 0 0 pub=0
  have hold := receipt_deposit_withoutAge_local accounts constants pub digests tokens fallback p i hi next hn h e he
  by_cases hind : ageIndependent e=true
  · rw [ageIndependent_eval tr old 0 0 pub rfl
      (fun col hc=>depositAge_cell_outside previous accounts cn pub digests tokens fallback p ⟨sDEP,i,16⟩ col (Or.inl hc))
      (fun col hc=>depositAge_cell_outside previous accounts cn pub digests tokens fallback p next col (Or.inl hc)) e hind]
    exact hold
  · have hm : e∈depositWithoutAge.filter (fun e=>!(ageIndependent e)) :=
      List.mem_filter.mpr ⟨he,by simpa using hind⟩
    rw [depositWithoutAge_overlap,List.mem_singleton] at hm
    subst e
    by_cases hi0 : i=0
    · subst i
      exact depositAge_first_storage previous cn pub digests tokens (depositAux accounts fallback) p next
    · rw [currentExpr_eval tr old 0 0 0 0 pub
        (fun col=>depositAge_cell_outside previous accounts cn pub digests tokens fallback p ⟨sDEP,i,16⟩ col (Or.inr hi0))
        depositStorageCheck (by decide)]
      exact hold

end ZkFormal.NearV3.Assembly.RcptSkeleton
