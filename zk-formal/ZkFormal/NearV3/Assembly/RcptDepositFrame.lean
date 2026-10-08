import ZkFormal.NearV3.Assembly.RcptDepositLedger
import ZkFormal.NearV3.Assembly.RcptDepositAgeFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout
open ZkFormal.Near.Render RcptGen RcptP

/-- Native scalar scratch. Version-distance bits are supplied separately on
first DEP; storage-gap bits are used only on second DEP. -/
def depositScratch (d : RD) (i j : Nat) : Fp :=
  if j<8 then frameBit (Seg.aftB d i) j else
  if j=8 then Fp.ofNat (chain (Seg.y1 d) (i+1)) else
  if j<17 then frameBit (Seg.totB d i) (j-9) else
  if j=17 then Fp.ofNat (chain (Seg.y2 d) (i+1)) else
  if j<26 then frameBit (Seg.qB d i) (j-18) else
  if j<38 then frameBit (chain (Seg.y3 d) (i+1)) (j-26) else
  if j<46 then frameBit (Seg.ddv d i) (j-38) else
  if j=46 then Fp.ofNat (Seg.dbr d (i+1)) else
  if j<57 ∧ i=1 ∧ d.big=false then frameBit (770-d.stor) (j-47) else 0

def depositInverse (d : RD) : Fp := (Fp.ofNat (Seg.runA d 15))⁻¹

def depositAux (accounts : ReceiptPlan→Account) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  let d := nativeDepositData (accounts p) p.input.receipt
  if col=r1 then bitCell (row.state==sDEP && row.index==1) else
  if col=st then (if row.state=sDEP then Fp.ofNat (Seg.stB d row.index) else 0) else
  if row.state=sDEP then
    if col=bef then Fp.ofNat (Seg.befB d row.index) else
    if col=lk then Fp.ofNat (Seg.lkB d row.index) else
    if col=c1 then Fp.ofNat (chain (Seg.y1 d) row.index) else
    if col=c2 then Fp.ofNat (chain (Seg.y2 d) row.index) else
    if col=c3 then Fp.ofNat (chain (Seg.y3 d) row.index) else
    if col=c4 then Fp.ofNat (Seg.dbr d row.index) else
    if col=dsum then Fp.ofNat (Seg.runA d row.index) else
    if col=invB then depositInverse d else
    if dl 0≤col ∧ col<dl 7 then Fp.ofNat (byteDelay (Seg.stB d) (col-dl 0) row.index) else
    if xb 0≤col ∧ col<xb 66 then depositScratch d row.index (col-xb 0) else
    fallback p row col
  else fallback p row col

def depositConstants (accounts : ReceiptPlan→Account) (fallback : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=big then bitCell (nativeDepositData (accounts p) p.input.receipt).big else fallback p col

theorem deposit_base_cells (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    let d := nativeDepositData (accounts p) p.input.receipt
    let cell := receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩
    cell bef=Fp.ofNat (Seg.befB d i) ∧ cell lk=Fp.ofNat (Seg.lkB d i) ∧
    cell st=Fp.ofNat (Seg.stB d i) ∧ cell c1=Fp.ofNat (chain (Seg.y1 d) i) ∧
    cell c2=Fp.ofNat (chain (Seg.y2 d) i) ∧ cell c3=Fp.ofNat (chain (Seg.y3 d) i) ∧
    cell c4=Fp.ofNat (Seg.dbr d i) ∧ cell dsum=Fp.ofNat (Seg.runA d i) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem deposit_after_bit (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (xb j)=
      frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 0) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 1) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 2) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 3) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 4) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 5) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 6) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 7) (frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem deposit_after_carry (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ (xb 8)=
      Fp.ofNat (chain (Seg.y1 (nativeDepositData (accounts p) p.input.receipt)) (i+1)) := by
  change boolInput (xb 8) (Fp.ofNat _)=_
  apply boolInput_preserves
  have hh := deposit_c1d_le h (i+1)
  have he : chain (Seg.y1 (nativeDepositData (accounts p) p.input.receipt)) (i+1)=0 ∨
    chain (Seg.y1 (nativeDepositData (accounts p) p.input.receipt)) (i+1)=1 := by omega
  rcases he with he|he
  · rw [he];exact Or.inl rfl
  · rw [he];exact Or.inr rfl

theorem deposit_after_eval (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    aftE.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) := by
  change (bitsX 0 8).eval _ _ _ _=_
  rw [eval_frame_bits _ 0 0 pub 0 (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) 8
    (fun j hj=>by simpa only [Nat.zero_add,receiptPair,ite_true] using deposit_after_bit accounts constants pub digests tokens fallback p i len j hj)]
  exact congrArg Fp.ofNat (Nat.mod_eq_of_lt (leBytes_getD_lt 16 _ i))

theorem deposit_inverse_cell (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,len⟩ invB=
      depositInverse (nativeDepositData (accounts p) p.input.receipt) := by
  have haux (aux : ReceiptPlan→Coord→Nat→Fp) :
      receiptCell (booleanConstants constants) (tokenReceiptAux pub digests tokens (booleanReceiptAux aux))
        p ⟨sDEP,i,len⟩ invB=aux p ⟨sDEP,i,len⟩ invB := rfl
  rw [haux]
  simp only [depositAux,invB,r1,st,sDEP,bef,lk,c1,c2,c3,c4,dsum,
    Nat.reduceEqDiff,ite_true,ite_false]


end ZkFormal.NearV3.Assembly.RcptSkeleton
