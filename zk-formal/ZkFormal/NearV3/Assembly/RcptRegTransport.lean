import ZkFormal.NearV3.Assembly.RcptHeaderRegLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Register constraints whose evaluation uses only the current and next cells. -/
def ordinaryRegs : List Expr := loadConstraints++[byteHeadConstraint]++shiftConstraints++
  gasTokenConstraints++carryTokenConstraints

def rowExpr : Expr→Bool
  | .const _ | .pub _ | .col _ _=>true
  | .add a b | .mul a b=>rowExpr a && rowExpr b
  | .neg a=>rowExpr a
  | _=>false

set_option maxRecDepth 4096 in
theorem ordinaryRegs_footprint : ordinaryRegs.all rowExpr=true := by decide

theorem cRegs_membership (e : Expr) : e∈cRegs ↔ e∈ordinaryRegs ∨ e∈initialTokenConstraints := by
  rw [cRegs_groups]
  simp only [ordinaryRegs,List.mem_append]
  grind only

theorem rowExpr_eval (tr tr' : Trace Fp) (t r t' r' : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t r c=tr'.cell t' r' c)
    (hn : ∀c,tr.cell t ((r+1)%tr.height t) c=tr'.cell t' ((r'+1)%tr'.height t') c)
    (e : Expr) (he : rowExpr e=true) : e.eval tr t r pub=e.eval tr' t' r' pub := by
  induction e with
  | const => rfl
  | pub => rfl
  | col c nx => cases nx <;> first | exact hc c | exact hn c
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : rowExpr a=true ∧ rowExpr b=true := by simpa only [rowExpr,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : rowExpr a=true ∧ rowExpr b=true := by simpa only [rowExpr,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem plannedTrace_cell (lists : List (List Input)) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (ra : ReceiptPlan→Coord→Nat→Fp)
    (ha : ListPlan→Coord→Nat→Fp) (row : PlannedRow)
    (hr : (plannedRows lists)[pos]?=some row) (col : Nat) :
    (plannedTrace lists log constants ra ha).cell 0 pos col=plannedCell constants ra ha row col := by
  simp only [plannedTrace,hr]

/-- Transfer all ordinary register constraints to their actual physical rows.
The no-wrap condition is a genuine trace-height condition, not a cell premise. -/
theorem planned_ordinaryRegs_transport (lists : List (List Input)) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (ra : ReceiptPlan→Coord→Nat→Fp)
    (ha : ListPlan→Coord→Nat→Fp) (a b : PlannedRow)
    (hcur : (plannedRows lists)[pos]?=some a) (hnxt : (plannedRows lists)[pos+1]?=some b)
    (hheight : pos+1<2^log) (pair : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀c,plannedCell constants ra ha a c=pair.cell t r c)
    (hn : ∀c,plannedCell constants ra ha b c=pair.cell t ((r+1)%pair.height t) c)
    (hl : ∀e∈ordinaryRegs,e.eval pair t r pub=0) :
    ∀e∈ordinaryRegs,e.eval (plannedTrace lists log constants ra ha) 0 pos pub=0 := by
  intro e he
  rw [rowExpr_eval _ pair 0 pos t r pub ?_ ?_ e (List.all_eq_true.mp ordinaryRegs_footprint e he)]
  · exact hl e he
  · intro c
    exact (plannedTrace_cell lists log pos constants ra ha a hcur c).trans (hc c)
  · intro c
    change (plannedTrace lists log constants ra ha).cell 0 ((pos+1)%2^log) c=_
    rw [Nat.mod_eq_of_lt hheight]
    exact (plannedTrace_cell lists log (pos+1) constants ra ha b hnxt c).trans (hn c)

end ZkFormal.NearV3.Assembly.RcptSkeleton
