import ZkFormal.NearV3.Assembly.RcptRoutingNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def keyZero (row : Coord) : Bool := row.state==sVL && decide (row.index<2)
def keyAccessA (row : Coord) : Bool := row.state==sT0 || (row.state==sSL && row.index==0) ||
  row.state==sS || row.state==sKT || row.state==sPK || (row.state==sGP && row.index==0)
def keyAccessB (row : Coord) : Bool := row.state==sT0 || (row.state==sSL && row.index==0) ||
  row.state==sS || row.state==sKT || row.state==sPK

def keyGateA (p : ReceiptPlan) (row : Coord) : Bool := row.state==sV || keyZero row ||
  (row.state==sRID && row.index==0) || (systemEqual p.input.receipt && keyAccessA row)
def keyGateB (p : ReceiptPlan) (row : Coord) : Bool := row.state==sV ||
  (systemEqual p.input.receipt && keyAccessB row)
def keyLast (p : ReceiptPlan) (row : Coord) : Bool := (row.state==sRID && row.index==0) ||
  (systemEqual p.input.receipt && row.state==sGP && row.index==0)

def keyPosA (p : ReceiptPlan) (row : Coord) : Nat :=
  if row.state=sV ∨ row.state=sS then 2+2*row.index else
  if row.state=sVL then row.index else
  if row.state=sRID then 2+2*p.input.receipt.receiverId.length else
  if row.state=sSL then 2+2*p.input.receipt.signerId.length else
  if row.state=sKT then 4+2*p.input.receipt.signerId.length else
  if row.state=sPK then 6+2*p.input.receipt.signerId.length+2*row.index else
  if row.state=sGP then 70+2*p.input.receipt.signerId.length+64*p.input.receipt.signerPk.tag else 0

def keyPosB (p : ReceiptPlan) (row : Coord) : Nat :=
  if row.state=sV ∨ row.state=sS then 3+2*row.index else
  if row.state=sT0 then 1 else
  if row.state=sSL then 3+2*p.input.receipt.signerId.length else
  if row.state=sKT then 5+2*p.input.receipt.signerId.length else
  if row.state=sPK then 7+2*p.input.receipt.signerId.length+2*row.index else 0

def keyByte (p : ReceiptPlan) (row : Coord) : Nat :=
  if row.state=sV then (p.input.receipt.receiverId.getD row.index 0).toNat else
  if row.state=sS then (p.input.receipt.signerId.getD row.index 0).toNat else
  if row.state=sPK then (p.input.receipt.signerPk.data.getD row.index 0).toNat else 0

def keySymA (p : ReceiptPlan) (row : Coord) : Nat :=
  if row.state=sV ∨ row.state=sS ∨ row.state=sPK then keyByte p row/16 else
  if row.state=sRID ∨ row.state=sGP then SYM_END else 0

def keySymB (p : ReceiptPlan) (row : Coord) : Nat :=
  if row.state=sV ∨ row.state=sS ∨ row.state=sPK then keyByte p row%16 else
  if row.state=sT0 ∨ row.state=sSL then 2 else
  if row.state=sKT then p.input.receipt.signerPk.tag else 0

/-- Provider identities are explicit inputs. This constructor does not claim
that the eventual account/access-key lookup buses authenticate those IDs. -/
def keyConstants (accountId : ReceiptPlan→Nat) (fallback : ReceiptPlan→Nat→Fp)
    (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=kslot then Fp.ofNat (accountId p) else fallback p col

def keyAux (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if col=tA then Fp.ofNat (keyPosA p row) else
  if col=tB then Fp.ofNat (keyPosB p row) else
  if col=symA then Fp.ofNat (keySymA p row) else
  if col=symB then Fp.ofNat (keySymB p row) else
  if col=lastA then bitCell (keyLast p row) else
  if col=gKA then bitCell (keyGateA p row) else
  if col=gKB then bitCell (keyGateB p row) else
  if col=kz then bitCell (keyZero row) else
  if col=gF then bitCell ((row.state==sPL && row.index==0) || (systemEqual p.input.receipt && row.state==sT0)) else
  if col=fkF then bitCell (row.state==sT0 && (accessId p).isNone) else
  if col=kF then Fp.ofNat (if row.state=sT0 then (accessId p).getD 0 else accountId p) else
  if col=gAK then bitCell (systemEqual p.input.receipt && row.state==sT0 && !(accessId p).isNone) else
  if row.state=sPK ∧ xb 0≤col ∧ col<xb 4 then frameBit (keyByte p row/16) (col-xb 0) else
  if row.state=sPK ∧ xb 4≤col ∧ col<xb 8 then frameBit (keyByte p row%16) (col-xb 4) else fallback p row col

theorem keyByte_lt (p : ReceiptPlan) (row : Coord) : keyByte p row<256 := by
  unfold keyByte
  split <;> first | exact UInt8.toNat_lt _ | skip
  split <;> first | exact UInt8.toNat_lt _ | skip
  split
  · exact UInt8.toNat_lt _
  · decide

theorem keyZero_next (i : Nat) (hi : i+1<4) :
    keyZero ⟨sVL,i+1,4⟩=(i==0) := by
  simp only [keyZero,beq_self_eq_true,Bool.true_and]
  have hh : i+1<2 ↔ i=0 := by omega
  simp only [hh,decide_eq_true_eq,beq_iff_eq]
  exact decide_eq_decide.mpr Iff.rfl

theorem keyByte_nibbles (p : ReceiptPlan) (row : Coord) :
    16*(keyByte p row/16)+keyByte p row%16=keyByte p row ∧
    keyByte p row/16<16 ∧ keyByte p row%16<16 := by
  have h := keyByte_lt p row
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
