import ZkFormal.NearV3.Assembly.RcptGasTokenArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def gasTokenAux (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP ∧ col=burnt then Fp.ofNat (gasByte (tokens p).burnt row.index) else
  if row.state=sGP ∧ col=c4 then Fp.ofNat (gasTokenCarry (tokens p) row.index) else
  if row.state=sGP ∧ col=xb 39 then Fp.ofNat (gasTokenCarry (tokens p) (row.index+1)) else fallback p row col

theorem gasToken_burnt_cell (tokens : ReceiptPlan→TokenInput)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)))
      p ⟨sGP,i,len⟩ burnt=Fp.ofNat (gasByte (tokens p).burnt i) := rfl

theorem gasToken_carry_cell (tokens : ReceiptPlan→TokenInput)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)))
      p ⟨sGP,i,len⟩ c4=Fp.ofNat (gasTokenCarry (tokens p) i) := rfl

theorem gasToken_next_carry_cell (tokens : ReceiptPlan→TokenInput)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)))
      p ⟨sGP,i,len⟩ (xb 39)=Fp.ofNat (gasTokenCarry (tokens p) (i+1)) := by
  change boolInput (xb 39) (Fp.ofNat (gasTokenCarry (tokens p) (i+1)))=_
  apply boolInput_preserves
  have hh := gasTokenCarry_le (tokens p) (i+1)
  have he : gasTokenCarry (tokens p) (i+1)=0 ∨ gasTokenCarry (tokens p) (i+1)=1 := by omega
  rcases he with he|he
  · left;rw [he];rfl
  · right;rw [he];rfl

theorem gasToken_old_head (x : TokenInput) (i : Nat) (hi : i<16) :
    (tokenOf x ⟨sGP,i,16⟩ 0).toNat=gasByte x.before i := by
  rw [tokenOf_gas]
  simp only [TokenInput.window,Nat.add_zero,List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa only [TokenInput.oldBytes,u128,leN_length] using hi)]
  exact (gasByte_native x.before i).symm

theorem gasToken_new_eval (tokens : ReceiptPlan→TokenInput)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) (next : Coord) :
    (bitsX 31 8).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)))
      p ⟨sGP,i,16⟩ next) 0 0 pub=Fp.ofNat (gasByte ((tokens p).before+(tokens p).burnt) i) := by
  rw [eval_frame_bits _ 0 0 pub 31 (((tokens p).newBytes.getD i 0).toNat) 8
    (fun j hj=>by simpa only [receiptPair,ite_true] using (receipt_token_bit (booleanConstants constants) pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback)) p i j hj))]
  rw [Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
  rw [gasByte_native]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
