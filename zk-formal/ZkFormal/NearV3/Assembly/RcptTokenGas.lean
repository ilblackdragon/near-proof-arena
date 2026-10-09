import ZkFormal.NearV3.Assembly.RcptTokenCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def gasTokenConstraints : List Expr :=
  (List.range 15).map (fun j=>.mul (c sGP) (sub (n (tok j)) (c (tok (j+1))))) ++
  [.mul (c sGP) (sub (n (tok 15)) (bitsX 31 8))]

theorem gasToken_in_regs : ∀e∈gasTokenConstraints,e∈cRegs := by
  intro e he
  simp only [gasTokenConstraints,List.mem_append] at he
  simp only [cRegs,List.mem_append]
  grind only

theorem receipt_token_bits (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (pos : Nat) :
    (bitsX 31 8).eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan ⟨sGP,pos,16⟩ (nextGas pos)) 0 0 pub=
      Fp.ofNat (((tokens plan).newBytes.getD pos 0).toNat) := by
  rw [eval_frame_bits _ _ _ _ _ _ _ (fun j hj=>receipt_token_bit constants pub digests tokens fallback plan pos j hj)]
  rw [Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

theorem receipt_gas_token_constraints (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (pos : Nat) (hp : pos<16) :
    ∀e∈gasTokenConstraints,e.eval
      (receiptPair constants (tokenReceiptAux pub digests tokens fallback) plan ⟨sGP,pos,16⟩ (nextGas pos)) 0 0 pub=0 := by
  intro e he
  simp only [gasTokenConstraints,List.mem_append,List.mem_singleton] at he
  rcases he with he|rfl
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    simp only [eval_mul,eval_c,eval_sub,eval_n]
    change _*(receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan (nextGas pos) (tok j)-
      receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan ⟨sGP,pos,16⟩ (tok (j+1)))=0
    rw [receipt_token_cell _ _ _ _ _ _ _ j (by omega),receipt_token_cell _ _ _ _ _ _ _ (j+1) (by omega),
      tokenOf_gas_shift _ _ _ hp]
    grind only
  · simp only [eval_mul,eval_sub,eval_n,eval_c]
    rw [receipt_token_bits]
    change _*(receiptCell constants (tokenReceiptAux pub digests tokens fallback) plan (nextGas pos) (tok 15)-_)=0
    rw [receipt_token_cell _ _ _ _ _ _ _ 15 (by decide),tokenOf_gas_tail _ _ hp]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
