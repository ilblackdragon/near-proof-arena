import ZkFormal.NearV3.Assembly.RcptSkeletonCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def controlColumn (c : Nat) : Bool := c==0 || (decide (4≤c) && decide (c≤29))

theorem receipt_control_cell (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan)
    (row : Coord) {c : Nat} (hc : controlColumn c=true) :
    receiptCell constants aux plan row c=controlCell row c := by
  have hr : c=0 ∨ (4≤c ∧ c≤29) := by simpa [controlColumn] using hc
  have he : c=0 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨
      c=13 ∨ c=14 ∨ c=15 ∨ c=16 ∨ c=17 ∨ c=18 ∨ c=19 ∨ c=20 ∨ c=21 ∨ c=22 ∨
      c=23 ∨ c=24 ∨ c=25 ∨ c=26 ∨ c=27 ∨ c=28 ∨ c=29 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst c <;> rfl

theorem header_control_cell (aux : ListPlan→Coord→Nat→Fp) (plan : ListPlan)
    (row : Coord) {c : Nat} (hc : controlColumn c=true) :
    headerCell aux plan row c=controlCell row c := by
  have hr : c=0 ∨ (4≤c ∧ c≤29) := by simpa [controlColumn] using hc
  have he : c=0 ∨ c=4 ∨ c=5 ∨ c=6 ∨ c=7 ∨ c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨
      c=13 ∨ c=14 ∨ c=15 ∨ c=16 ∨ c=17 ∨ c=18 ∨ c=19 ∨ c=20 ∨ c=21 ∨ c=22 ∨
      c=23 ∨ c=24 ∨ c=25 ∨ c=26 ∨ c=27 ∨ c=28 ∨ c=29 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst c <;> rfl

def controlExpr : Expr→Bool
  | .const _ | .pub _=>true
  | .col c _=>controlColumn c
  | .add a b | .mul a b=>controlExpr a && controlExpr b
  | .neg a=>controlExpr a
  | _=>false

theorem continuation_footprint : continuationConstraints.all controlExpr=true := by decide

theorem control_eval_agree (tr tr' : Trace Fp) (t r t' r' : Nat) (pub : List Fp)
    (hc : ∀c,controlColumn c=true→tr.cell t r c=tr'.cell t' r' c)
    (hn : ∀c,controlColumn c=true→tr.cell t ((r+1)%tr.height t) c=
      tr'.cell t' ((r'+1)%tr'.height t') c) (e : Expr) (he : controlExpr e=true) :
    e.eval tr t r pub=e.eval tr' t' r' pub := by
  induction e with
  | const => rfl
  | pub => rfl
  | col c nx => cases nx <;> first | exact hc c he | exact hn c he
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hs : controlExpr a=true ∧ controlExpr b=true := by simpa only [controlExpr,Bool.and_eq_true] using he
    simp only [eval_add,ia hs.1,ib hs.2]
  | mul a b ia ib =>
    have hs : controlExpr a=true ∧ controlExpr b=true := by simpa only [controlExpr,Bool.and_eq_true] using he
    simp only [eval_mul,ia hs.1,ib hs.2]
  | neg a ia => simp only [eval_neg,ia he]

def receiptPair (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row next : Coord) : Trace Fp :=
  ⟨fun _=>1,fun _ r=>receiptCell constants aux plan (if r=0 then row else next)⟩

/-- The shared full row assignment preserves all checked continuation equations,
regardless of the arithmetic group's cells outside its owned columns. -/
theorem receipt_continuation (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan)
    (row : Coord) (hs : row.state∈states) (hi : row.index+1<row.length) (pub : List Fp) :
    ∀e∈continuationConstraints,e.eval (receiptPair constants aux plan row (advance row)) 0 0 pub=0 := by
  intro e he
  have hf := List.all_eq_true.mp continuation_footprint e he
  rw [control_eval_agree _ (controlPair row (advance row)) 0 0 0 0 pub
    (fun c hc=>receipt_control_cell constants aux plan row hc)
    (fun c hc=>receipt_control_cell constants aux plan (advance row) hc) e hf]
  exact control_continuation row hs hi pub e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
