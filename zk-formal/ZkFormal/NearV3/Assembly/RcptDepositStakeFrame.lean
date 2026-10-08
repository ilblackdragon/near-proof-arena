import ZkFormal.NearV3.Assembly.RcptDepositBorrowLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout
open ZkFormal.Near.Render RcptGen RcptP

theorem deposit_r1_cell (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ r1=
      bitCell (i==1) := by
  change boolInput r1 (bitCell (i==1))=_
  exact boolInput_preserves _ _ (bitCell_boolean _)

theorem deposit_storage_gap_bit (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (j : Nat) (hj : j<10)
    (hb : (nativeDepositData (accounts p) p.input.receipt).big=false) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,1,16⟩ (xb (47+j))=
      frameBit (770-(nativeDepositData (accounts p) p.input.receipt).stor) j := by
  let d := nativeDepositData (accounts p) p.input.receipt
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 47) (depositScratch d 1 47)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 48) (depositScratch d 1 48)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 49) (depositScratch d 1 49)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 50) (depositScratch d 1 50)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 51) (depositScratch d 1 51)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 52) (depositScratch d 1 52)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 53) (depositScratch d 1 53)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 54) (depositScratch d 1 54)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 55) (depositScratch d 1 55)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 56) (depositScratch d 1 56)=_
    simp only [depositScratch,show d.big=false from hb,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceSub,true_and,ite_true,ite_false]
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem deposit_storage_gap_eval (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (next : Coord)
    (hb : (nativeDepositData (accounts p) p.input.receipt).big=false) :
    (bitsX 47 10).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,1,16⟩ next) 0 0 pub=
      Fp.ofNat (770-(nativeDepositData (accounts p) p.input.receipt).stor) := by
  rw [eval_frame_bits _ 0 0 pub 47 (770-(nativeDepositData (accounts p) p.input.receipt).stor) 10
    (fun j hj=>by simpa only [receiptPair,ite_true] using deposit_storage_gap_bit accounts constants pub digests tokens fallback p j hj hb)]
  rw [Nat.mod_eq_of_lt (by omega)]

end ZkFormal.NearV3.Assembly.RcptSkeleton
