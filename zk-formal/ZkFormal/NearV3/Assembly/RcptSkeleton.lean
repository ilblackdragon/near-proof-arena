import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Rcpt.Tables.Rcpt

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Native receipt plus its actual runtime refund decision. No arithmetic witness
or AIR predicate is stored here. Runtime refund semantics are linked separately. -/
structure Input where
  receipt : Receipt
  refund : Bool

def fields (refund : Bool) : List Nat :=
  [sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0] ++
    (if refund then [sXRI] else []) ++ [sXG,sXST,sXL0,sXLH] ++
    (if refund then [sXRH,sXRF,sXRZ] else [])

def fieldLen (x : Input) (s : Nat) : Nat :=
  if s=sCL then 12 else
  if s=sPL then 4 else if s=sP then x.receipt.predecessorId.length else
  if s=sVL then 4 else if s=sV then x.receipt.receiverId.length else
  if s=sRID then 32 else if s=sT0 then 1 else if s=sSL then 4 else
  if s=sS then x.receipt.signerId.length else if s=sKT then 1 else
  if s=sPK then 32+32*x.receipt.signerPk.tag else if s=sGP then 16 else
  if s=sTL then 13 else if s=sDEP then 16 else if s=sXP0 then 4 else
  if s=sXRI then 32 else if s=sXG then 8 else if s=sXST then 5 else
  if s=sXL0 then 4 else if s=sXLH then 32 else if s=sXRH then 16 else
  if s=sXRF then 10 else if s=sXRZ then 16 else 0

structure Coord where
  state : Nat
  index : Nat
  length : Nat
  deriving DecidableEq, Repr

def segment (s len : Nat) : List Coord := (List.range len).map fun i=>⟨s,i,len⟩
def receiptRows (x : Input) : List Coord := (fields x.refund).flatMap fun s=>segment s (fieldLen x s)
def headerRows : List Coord := segment sCL 12

def listRows (xs : List Input) : List Coord := headerRows ++ xs.flatMap receiptRows
/-- Each native source list contributes a header, including empty/repeated lists. -/
def allRows (lists : List (List Input)) : List Coord := lists.flatMap listRows

theorem segment_length (s len : Nat) : (segment s len).length=len := by simp [segment]
theorem segment_member {s len : Nat} {row : Coord} (h : row∈segment s len) :
    row.state=s ∧ row.index<len ∧ row.length=len := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  exact ⟨rfl,List.mem_range.mp hi,rfl⟩

theorem receiptRows_length (x : Input) :
    (receiptRows x).length=176+x.receipt.predecessorId.length+x.receipt.receiverId.length+
      x.receipt.signerId.length+32*x.receipt.signerPk.tag+(if x.refund then 74 else 0) := by
  cases h : x.refund <;>
    simp [receiptRows,fields,h,fieldLen,segment_length,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,
      sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ,sCL] <;> omega

theorem receiptRows_bound (x : Input) (hw : x.receipt.wf=true) :
    (receiptRows x).length≤474 := by
  have hl : x.receipt.predecessorId.length≤64 ∧ x.receipt.receiverId.length≤64 ∧
      x.receipt.signerId.length≤64 ∧ x.receipt.signerPk.tag≤1 := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  rw [receiptRows_length]
  split <;> omega

theorem allRows_bound (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) :
    (allRows lists).length≤12*lists.length+474*(lists.map List.length).sum := by
  have hr (xs : List Input) (hx : ∀x∈xs,x.receipt.wf=true) :
      (xs.flatMap receiptRows).length≤474*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have ha := receiptRows_bound x (hx x (by simp))
      have hb := ih (fun y hy=>hx y (by simp [hy]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  induction lists with
  | nil => simp [allRows]
  | cons xs lists ih =>
    have ha := hr xs (hw xs (by simp))
    have hb := ih (fun ys hy=>hw ys (by simp [hy]))
    simp only [allRows,List.flatMap_cons,List.length_append,listRows,headerRows,segment_length,
      List.length_cons,List.map_cons,List.sum_cons]
    change 12+(xs.flatMap receiptRows).length+(lists.flatMap listRows).length≤_
    change (lists.flatMap listRows).length≤_ at hb
    omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
