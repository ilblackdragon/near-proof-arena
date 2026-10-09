import ZkFormal.NearV3.Assembly.RcptRoutingRid

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

set_option maxRecDepth 4096 in
theorem routing_inactive (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hv : tr.cell t pos sV=0) (hr : tr.cell t pos sRID * tr.cell t pos fs=0)
    (hg : tr.cell t pos gBd=0) : ∀e∈cRoute,e.eval tr t pos pub=0 := by
  intro e he
  simp only [cRoute,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_sub,eval_add,eval_mul,eval_mul3,eval_not,eval_k,rwE,orE,eval_c,hv,hg,hr]
  all_goals grind only

theorem routing_current_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,routingColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (e : Expr) (he : routingFootprint e=true) (hcur : currentExpr e=true) :
    e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  induction e with
  | const | pub => rfl
  | col col nx => cases nx; exact hc col he; cases hcur
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : routingFootprint a=true ∧ routingFootprint b=true := by simpa only [routingFootprint,Bool.and_eq_true] using he
    have hj : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using hcur
    simp only [eval_add,ia hh.1 hj.1,ib hh.2 hj.2]
  | mul a b ia ib =>
    have hh : routingFootprint a=true ∧ routingFootprint b=true := by simpa only [routingFootprint,Bool.and_eq_true] using he
    have hj : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using hcur
    simp only [eval_mul,ia hh.1 hj.1,ib hh.2 hj.2]
  | neg a ia => simp only [eval_neg,ia he hcur]

/- Only the receiver rows inspect next-prefix flags; the end-marker row can
be transported without constraining the unrelated following RID byte. -/
set_option maxRecDepth 4096 in
theorem routing_no_next (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,routingColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (hv : tr.cell t pos sV=0) :
    ∀e∈cRoute,e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  intro e he
  -- Direct polynomial decomposition avoids requiring any next-row equality.
  have hh : ∀col∈[sV,sRID,fs,idx,Lv,b,gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH],
      tr.cell t pos col=tr'.cell t' pos' col := by
    intro col hm
    apply hc
    simp only [routingColumn,hm,decide_true,Bool.true_or]
  have hbits (base : Nat) (hb : base=20 ∨ base=29) :
      (bitsX base 9).eval tr t pos pub=(bitsX base 9).eval tr' t' pos' pub := by
    apply routing_current_agree tr tr' t pos t' pos' pub hc
    all_goals rcases hb with rfl|rfl <;> decide
  simp only [cRoute,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_sub,eval_add,eval_mul,eval_mul3,eval_not,eval_k,rwE,orE,eval_c]
  all_goals try rw [hbits 20 (Or.inl rfl)]
  all_goals try rw [hbits 29 (Or.inr rfl)]
  all_goals simp only [hh sV (by decide),hh sRID (by decide),hh fs (by decide),hh idx (by decide),
    hh Lv (by decide),hh b (by decide),hh gBd (by decide),hh eqL (by decide),hh eqH (by decide),
    hh eL (by decide),hh eH (by decide),hh vB (by decide),hh iB (by decide),hh loB (by decide),
    hh hiB (by decide),hh hnB (by decide),hh iL (by decide),hh iH (by decide),
    hc (xb 28) (by decide),hc (xb 37) (by decide)]
  all_goals try rfl
  all_goals have hv' : tr'.cell t' pos' sV=0 := (hh sV (by decide)).symm.trans hv
  all_goals rw [hv']
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
