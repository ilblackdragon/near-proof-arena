import ZkFormal.NearV3.Assembly.RcptDepositNonmax

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout
open ZkFormal.Near.Render RcptGen RcptP

theorem deposit_total_bit (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (xb (9+j))=
      frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 9) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 10) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 11) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 12) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 13) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 14) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 15) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 16) (frameBit (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem deposit_total_carry (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (xb 17)=
      Fp.ofNat (chain (Seg.y2 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) := by
  change boolInput (xb 17) (Fp.ofNat _)=_
  apply boolInput_preserves
  have hh := deposit_c2d_le h (i+1)
  have he : chain (Seg.y2 (nativeDepositData (accounts p) p.input.receipt)) (i+1)=0 ∨
    chain (Seg.y2 (nativeDepositData (accounts p) p.input.receipt)) (i+1)=1 := by omega
  rcases he with he|he
  · rw [he];exact Or.inl rfl
  · rw [he];exact Or.inr rfl

theorem deposit_total_eval (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    (bitsX 9 8).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) := by
  change (bitsX 9 8).eval _ _ _ _=_
  rw [eval_frame_bits _ 0 0 pub 9 (Seg.totB (nativeDepositData (accounts p) p.input.receipt) i) 8
    (fun j hj=>by simpa only [receiptPair,ite_true] using deposit_total_bit accounts constants pub digests tokens fallback p i len j hj)]
  exact congrArg Fp.ofNat (Nat.mod_eq_of_lt (leBytes_getD_lt 16 _ i))


end ZkFormal.NearV3.Assembly.RcptSkeleton
