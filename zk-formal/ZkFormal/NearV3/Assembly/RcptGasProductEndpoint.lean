import ZkFormal.NearV3.Assembly.RcptGasProductReceipt
import ZkFormal.NearV3.Assembly.RcptSystemGasFootprint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasProduct_current_eval_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,gasProductColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (e : Expr) (he : gasProductFootprint e=true) (hcur : currentExpr e=true) :
    e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  induction e with
  | const | pub => rfl
  | col col nx =>
    cases nx
    · exact hc col he
    · cases hcur
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : gasProductFootprint a=true ∧ gasProductFootprint b=true := by simpa only [gasProductFootprint,Bool.and_eq_true] using he
    have hj : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using hcur
    simp only [eval_add,ia hh.1 hj.1,ib hh.2 hj.2]
  | mul a b ia ib =>
    have hh : gasProductFootprint a=true ∧ gasProductFootprint b=true := by simpa only [gasProductFootprint,Bool.and_eq_true] using he
    have hj : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using hcur
    simp only [eval_mul,ia hh.1 hj.1,ib hh.2 hj.2]
  | neg a ia => simp only [eval_neg,ia he hcur]

theorem gasProduct_last_eval_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,gasProductColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (hf : tr'.cell t' pos' fe=1) :
    ∀e∈gasProductConstraints systemSurplus,e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  intro e he
  have hh := List.all_eq_true.mp gasProduct_footprint e he
  change e∈[_,_,_,_,_,_,_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact gasProduct_current_eval_agree tr tr' t pos t' pos' pub hc _ hh (by decide)
    | (simp only [eval_mul3,eval_not,eval_c,hc fe (by decide),hf];grind only)

end ZkFormal.NearV3.Assembly.RcptSkeleton
