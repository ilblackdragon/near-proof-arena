import ZkFormal.NearV3.Assembly.RcptSkeletonRegisters

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def shapeColumn (col : Nat) : Bool := col==Lp || col==Lv || col==Ls || col==kt || col==hr

theorem receipt_shape_cell (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row : Coord) {col : Nat} (hc : shapeColumn col=true) :
    receiptCell constants aux plan row col=shapeCell plan.input col := by
  simp only [shapeColumn,Bool.or_eq_true,beq_iff_eq] at hc
  rcases hc with (((hc|hc)|hc)|hc)|hc <;> subst col <;> rfl

def shapeExpr : Expr→Bool
  | .const _ | .pub _=>true
  | .col c false=>shapeColumn c
  | .add a b | .mul a b=>shapeExpr a && shapeExpr b
  | .neg a=>shapeExpr a
  | _=>false

theorem loads_shape_footprint : (loads.flatMap Prod.snd).all shapeExpr=true := by decide

theorem shape_eval_agree (tr : Trace Fp) (t r : Nat) (x : Input) (pub : List Fp)
    (hc : ∀c,shapeColumn c=true→tr.cell t r c=shapeCell x c)
    (e : Expr) (he : shapeExpr e=true) : e.eval tr t r pub=e.eval (shapeTrace x) 0 0 pub := by
  induction e with
  | const => rfl
  | pub => rfl
  | col c nx => cases nx; exact hc c he; cases he
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hs : shapeExpr a=true ∧ shapeExpr b=true := by simpa only [shapeExpr,Bool.and_eq_true] using he
    simp only [eval_add,ia hs.1,ib hs.2]
  | mul a b ia ib =>
    have hs : shapeExpr a=true ∧ shapeExpr b=true := by simpa only [shapeExpr,Bool.and_eq_true] using he
    simp only [eval_mul,ia hs.1,ib hs.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem receipt_load_expr (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row next : Coord) (pub : List Fp) {state : Nat} {es : List Expr}
    (hm : (state,es)∈loads) {e : Expr} (he : e∈es) :
    e.eval (receiptPair constants aux plan row next) 0 0 pub=
      e.eval (shapeTrace plan.input) 0 0 pub := by
  apply shape_eval_agree _ _ _ _ pub (fun c hc=>receipt_shape_cell constants aux plan row hc)
  exact List.all_eq_true.mp loads_shape_footprint e (List.mem_flatMap.mpr ⟨(state,es),hm,he⟩)

end ZkFormal.NearV3.Assembly.RcptSkeleton
