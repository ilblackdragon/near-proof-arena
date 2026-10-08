import ZkFormal.NearV3.Assembly.RcptDepositTotalLocal
import ZkFormal.Near.Render.Proof.RcptDep2

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout
open ZkFormal.Near.Render RcptGen RcptP

theorem deposit_storage_q_bit (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (xb (18+j))=
      frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 18) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 19) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 20) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 21) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 22) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 23) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 24) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 25) (frameBit (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem deposit_storage_carry_bit (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<12) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (xb (26+j))=
      frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 26) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 27) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 28) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 29) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 30) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 31) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 32) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 33) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 34) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 8)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 35) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 9)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 36) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 10)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 37) (frameBit (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 11)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem deposit_storage_dl_cell (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<7) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (dl j)=
      Fp.ofNat (byteDelay (Seg.stB (nativeDepositData (accounts p) p.input.receipt)) j i) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem deposit_storage_q_eval (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (next : Coord)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    (bitsX 18 8).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) := by
  rw [eval_frame_bits _ 0 0 pub 18 (Seg.qB (nativeDepositData (accounts p) p.input.receipt) i) 8
    (fun j hj=>by simpa only [receiptPair,ite_true] using deposit_storage_q_bit accounts constants pub digests tokens fallback p i len j hj)]
  rw [Nat.mod_eq_of_lt (deposit_qB_lt h i)]

theorem deposit_storage_carry_eval (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (next : Coord)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    (bitsX 26 12).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) := by
  rw [eval_frame_bits _ 0 0 pub 26 (chain (Seg.y3 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) 12
    (fun j hj=>by simpa only [receiptPair,ite_true] using deposit_storage_carry_bit accounts constants pub digests tokens fallback p i len j hj)]
  rw [Nat.mod_eq_of_lt (by have hh := deposit_c3d_le h (i+1);omega)]


end ZkFormal.NearV3.Assembly.RcptSkeleton
