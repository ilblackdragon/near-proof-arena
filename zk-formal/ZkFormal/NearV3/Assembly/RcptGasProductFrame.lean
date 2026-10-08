import ZkFormal.NearV3.Assembly.RcptGasProductPrices

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def gasProductAux (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP then
    if col=ramt then Fp.ofNat (gasByte (Params.G*gasSurplusPrice ctx p.input.receipt) row.index) else
    if col=c2 then Fp.ofNat (gasMulCarry (gasBurnPrice ctx p.input.receipt) row.index) else
    if col=c3 then Fp.ofNat (gasMulCarry (gasSurplusPrice ctx p.input.receipt) row.index) else
    if xb 9≤col ∧ col<xb 20 then frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (row.index+1)) (col-xb 9) else
    if xb 20≤col ∧ col<xb 31 then frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (row.index+1)) (col-xb 20) else
    fallback p row col
  else fallback p row col

def candidateGasDelayByte (ctx : ApplyCtx) (r : Receipt) (j i : Nat) : Nat :=
  if j<4 then byteDelay (gasByte (gasBurnPrice ctx r)) j i
  else byteDelay (gasByte (gasSurplusPrice ctx r)) (j-4) i

def candidateGasDelayAux (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP ∧ dl 0≤col ∧ col<dl 8 then
    Fp.ofNat (candidateGasDelayByte ctx p.input.receipt (col-dl 0) row.index)
  else fallback p row col

theorem gasProduct_cells (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    let cell := receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasProductAux ctx fallback))) p ⟨sGP,i,len⟩
    cell ramt=Fp.ofNat (gasByte (Params.G*gasSurplusPrice ctx p.input.receipt) i) ∧
    cell c2=Fp.ofNat (gasMulCarry (gasBurnPrice ctx p.input.receipt) i) ∧
    cell c3=Fp.ofNat (gasMulCarry (gasSurplusPrice ctx p.input.receipt) i) := ⟨rfl,rfl,rfl⟩

theorem gasProduct_burn_bit (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<11) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasProductAux ctx fallback))) p ⟨sGP,i,len⟩ (xb (9+j))=
      frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 9) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 10) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 11) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 12) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 13) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 14) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 15) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 16) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 17) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 8)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 18) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 9)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 19) (frameBit (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) 10)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem gasProduct_surplus_bit (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<11) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasProductAux ctx fallback))) p ⟨sGP,i,len⟩ (xb (20+j))=
      frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) j := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 20) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 0)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 21) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 1)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 22) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 2)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 23) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 3)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 24) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 4)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 25) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 5)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 26) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 6)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 27) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 7)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 28) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 8)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 29) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 9)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)
  · change boolInput (xb 30) (frameBit (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) 10)=_
    exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem candidateGasDelay_cell (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (candidateGasDelayAux ctx fallback)))
      p ⟨sGP,i,len⟩ (dl j)=Fp.ofNat (candidateGasDelayByte ctx p.input.receipt j i) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
