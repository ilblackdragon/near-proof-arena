import ZkFormal.NearV3.Assembly.RcptCharLocal
import ZkFormal.Near.Render.Proof.RcptStr

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def characterBytes (x : Input) (s : Nat) : Bytes :=
  if s=sP then x.receipt.predecessorId else if s=sV then x.receipt.receiverId
  else if s=sS then x.receipt.signerId else []

def characterByte (p : ReceiptPlan) (row : Coord) : Nat :=
  ((characterBytes p.input row.state).getD row.index 0).toNat

/-- Shared account-character scratch; all non-string rows use zero character
columns. Registers, token bits, digest requests and native constants are untouched. -/
def characterAux (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if 111≤col ∧ col≤123 then
    if row.state∈[sP,sV,sS] then
      Fp.ofNat (ZkFormal.Near.Render.RcptGen.charCell (characterByte p row) col) else 0
  else fallback p row col

def characterHeaderAux (fallback : ListPlan→Coord→Nat→Fp)
    (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if 111≤col ∧ col≤123 then 0 else fallback p row col

theorem characterBytes_valid (x : Input) (hw : x.receipt.wf=true) (s : Nat)
    (hs : s∈[sP,sV,sS]) : AccountId.valid (characterBytes x s)=true := by
  have hh : AccountId.valid x.receipt.predecessorId=true ∧
      AccountId.valid x.receipt.receiverId=true ∧ AccountId.valid x.receipt.signerId=true := by
    simp only [Receipt.wf,Bool.and_eq_true] at hw
    grind only
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl <;> simpa [characterBytes,sP,sV,sS] using (by first | exact hh.1 | exact hh.2.1 | exact hh.2.2)

theorem characterBytes_length (x : Input) (s : Nat) (hs : s∈[sP,sV,sS]) :
    (characterBytes x s).length=fieldLen x s := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl <;> rfl

theorem characterByte_lt (p : ReceiptPlan) (row : Coord) : characterByte p row<256 :=
  UInt8.toNat_lt _

theorem characterByte_valid (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hs : row.state∈[sP,sV,sS])
    (hi : row.index<fieldLen p.input row.state) :
    ZkFormal.Near.Render.RcptP.vch (characterByte p row)=true := by
  have hv := characterBytes_valid p.input hw row.state hs
  simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hv
  have hh := ZkFormal.Near.Render.RcptP.chars_spec (characterBytes p.input row.state) true hv.2 row.index
    (by rw [characterBytes_length p.input row.state hs];exact hi)
  have he : ((ZkFormal.Near.Render.toNats (characterBytes p.input row.state)).getD row.index 0)=
      ((characterBytes p.input row.state).getD row.index 0).toNat := by
    simp only [ZkFormal.Near.Render.toNats,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases (characterBytes p.input row.state)[row.index]? <;> rfl
  simpa only [he,characterByte] using hh.1

set_option maxRecDepth 4096 in
theorem characterColumns_not_boolean : ∀col,col∈List.range' 111 13→col∉boolCols := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
