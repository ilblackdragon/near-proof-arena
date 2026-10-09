import ZkFormal.NearV3.Assembly.RcptDepositAgeScratch
import ZkFormal.NearV3.Assembly.RcptGasBorrowFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def depositAgeAux (previous : ReceiptPlan→Nat) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sDEP ∧ col=r1 then bitCell (row.index==1) else
  if row.state=sDEP ∧ row.index=0 ∧ xb 53≤col ∧ col<xb 66 then
    frameBit (p.receiptIndex-previous p) (col-xb 53)
  else fallback p row col

def depositAgeConstants (previous : ReceiptPlan→Nat) (fallback : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=tprev then Fp.ofNat (previous p) else fallback p col

theorem depositAge_bit_cell (previous : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (j : Nat) (hj : j<13) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous fallback)))
      p ⟨sDEP,0,16⟩ (xb (53+j))=frameBit (p.receiptIndex-previous p) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 53) (frameBit (p.receiptIndex-previous p) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 54) (frameBit (p.receiptIndex-previous p) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 55) (frameBit (p.receiptIndex-previous p) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 56) (frameBit (p.receiptIndex-previous p) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 57) (frameBit (p.receiptIndex-previous p) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 58) (frameBit (p.receiptIndex-previous p) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 59) (frameBit (p.receiptIndex-previous p) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 60) (frameBit (p.receiptIndex-previous p) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 61) (frameBit (p.receiptIndex-previous p) 8)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 62) (frameBit (p.receiptIndex-previous p) 9)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 63) (frameBit (p.receiptIndex-previous p) 10)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 64) (frameBit (p.receiptIndex-previous p) 11)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 65) (frameBit (p.receiptIndex-previous p) 12)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem depositAge_first_r1 (previous : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous fallback)))
      p ⟨sDEP,0,16⟩ r1=0 := rfl

theorem depositAge_eval (previous : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (hp : p.receiptIndex<4481) (next : Coord) :
    (bitsX 53 13).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous fallback)))
      p ⟨sDEP,0,16⟩ next) 0 0 pub=Fp.ofNat (p.receiptIndex-previous p) := by
  rw [eval_frame_bits _ 0 0 pub 53 (p.receiptIndex-previous p) 13
    (fun j hj=>by simpa only [receiptPair,ite_true] using
      depositAge_bit_cell previous constants pub digests tokens fallback p j hj)]
  rw [Nat.mod_eq_of_lt (native_deposit_age_bound _ _ hp)]

theorem depositAge_first_equation (previous : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (hp : p.receiptIndex<4481) (hv : previous p≤p.receiptIndex) (next : Coord) :
    (mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13))).eval
      (receiptPair (booleanConstants (depositAgeConstants previous constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous fallback)))
        p ⟨sDEP,0,16⟩ next) 0 0 pub=0 := by
  rw [eval_mul3,eval_sub,eval_sub,depositAge_eval previous _ pub digests tokens fallback p hp next]
  change (1:Fp)*1*(Fp.ofNat p.receiptIndex-Fp.ofNat (previous p)-Fp.ofNat (p.receiptIndex-previous p))=0
  have hn := congrArg (fun n : Nat=>(n:Fp)) (Nat.sub_add_cancel hv)
  rw [ZkFormal.Near.natCast_add] at hn
  simp only [ZkFormal.Near.natCast_eq] at hn
  grind only

theorem depositAge_first_storage (previous : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (next : Coord) :
    (mul3 (Dsl.not (c big)) (c r1) (sub (k 770) (sum [c (dl 0),smul 256 (c st),bitsX 47 10]))).eval
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous fallback)))
        p ⟨sDEP,0,16⟩ next) 0 0 pub=0 := by
  simp only [eval_mul3,eval_c]
  rw [show (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous fallback)))
      p ⟨sDEP,0,16⟩ next).cell 0 0 r1=0 from
    depositAge_first_r1 previous constants pub digests tokens fallback p]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
