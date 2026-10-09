import ZkFormal.NearV3.Assembly.RcptSkeletonIndices

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

def bitCell (b : Bool) : Fp := if b then 1 else 0

def receiptEnd (plan : ReceiptPlan) (row : Coord) : Bool :=
  row.index+1==row.length && (row.state==sXRZ || (row.state==sXLH && !plan.input.refund))

/-- Shared receipt cell assignment. Arithmetic/byte groups supply `aux`; all
bookkeeping columns are fixed here, so those groups cannot choose their offsets
or receipt/list counters independently. -/
def receiptCell (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if col=rf then bitCell (row.state==sPL && row.index==0) else
  if col=rl then bitCell (receiptEnd plan row) else
  if col=lastR then bitCell (receiptEnd plan row && plan.lastInList && plan.lastList) else
  if col=le then bitCell (receiptEnd plan row && plan.lastInList) else
  if col=j then Fp.ofNat plan.listIndex else
  if col=nj then Fp.ofNat plan.listCount else
  if col=r then Fp.ofNat plan.receiptIndex else
  if col=cj then Fp.ofNat plan.withinList else
  if col=o then Fp.ofNat plan.rcOffset else
  if col=oEnd then Fp.ofNat (plan.rcOffset+rcLength plan.input) else
  if col=o2 then Fp.ofNat plan.bodyOffset else
  if col=o2End then Fp.ofNat (plan.bodyOffset+refundLength plan.input) else
  if col=Lp || col=Lv || col=Ls || col=kt || col=hr then shapeCell plan.input col else
  if col≤29 then controlCell row col else if col∈rconsts then constants plan col else aux plan row col

def headerCell (aux : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col=rf || col=rl then 0 else
  if col=lastR then bitCell (row.index+1==12 && plan.inputs.isEmpty && plan.lastList) else
  if col=le then bitCell (row.index+1==12 && plan.inputs.isEmpty) else
  if col=j then Fp.ofNat plan.listIndex else
  if col=nj then Fp.ofNat plan.inputs.length else
  if col=r then Fp.ofNat plan.receiptIndex else
  if col=cj then 0 else
  if col=oEnd then 12 else
  if col=o2 || col=o2End then Fp.ofNat plan.bodyOffset else
  if col≤29 then controlCell row col else aux plan row col

def plannedCell (constants : ReceiptPlan→Nat→Fp) (receiptAux : ReceiptPlan→Coord→Nat→Fp) (headerAux : ListPlan→Coord→Nat→Fp) :
    PlannedRow→Nat→Fp
  | .header plan row=>headerCell headerAux plan row
  | .receipt plan row=>receiptCell constants receiptAux plan row

/-- Padding is zero. The future local theorem must additionally establish the
active row count below the chosen power-of-two trace height. -/
def plannedTrace (lists : List (List Input)) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (receiptAux : ReceiptPlan→Coord→Nat→Fp) (headerAux : ListPlan→Coord→Nat→Fp) : Trace Fp :=
  ⟨fun _=>log,fun _ pos col=>match (plannedRows lists)[pos]? with
    | some row=>plannedCell constants receiptAux headerAux row col
    | none=>0⟩

theorem rconsts_range : ∀c∈rconsts,29<c ∧ c≠le := by decide

theorem receipt_constants_carry (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan)
    (row next : Coord) {col : Nat} (hc : col∈rconsts) :
    receiptCell constants aux plan row col=receiptCell constants aux plan next col := by
  obtain ⟨hlt,hle⟩ := rconsts_range col hc
  have hrf : col≠rf := by unfold rf;omega
  have hrl : col≠rl := by unfold rl;omega
  have hlast : col≠lastR := by unfold lastR;omega
  simp only [receiptCell,if_neg hrf,if_neg hrl,if_neg hlast,if_neg hle,
    if_neg (show ¬col≤29 by omega),if_pos hc]

theorem header_receipt_index (aux : ListPlan→Coord→Nat→Fp) (plan : ListPlan) (row : Coord) :
    headerCell aux plan row r=Fp.ofNat plan.receiptIndex := rfl

theorem receipt_index (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord) :
    receiptCell constants aux plan row r=Fp.ofNat plan.receiptIndex := rfl

theorem receipt_rc_end (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (hw : plan.input.receipt.wf=true) :
    receiptCell constants aux plan row oEnd=Fp.ofNat (plan.rcOffset+plan.input.receipt.encode.length) := by
  rw [rcLength_native plan.input hw]
  rfl

theorem plannedTrace_padding (lists : List (List Input)) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (ra : ReceiptPlan→Coord→Nat→Fp) (ha : ListPlan→Coord→Nat→Fp) (hp : (plannedRows lists).length≤pos) :
    ∀col,(plannedTrace lists log constants ra ha).cell 0 pos col=0 := by
  intro col
  simp only [plannedTrace,List.getElem?_eq_none hp]

end ZkFormal.NearV3.Assembly.RcptSkeleton
