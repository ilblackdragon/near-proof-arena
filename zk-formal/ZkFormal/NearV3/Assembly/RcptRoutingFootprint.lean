import ZkFormal.NearV3.Assembly.RcptRoutingAdjusted

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def routingColumn (col : Nat) : Bool :=
  col∈[sV,sRID,fs,idx,Lv,b,gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH] ||
    (decide (xb 20≤col ∧ col<xb 38))

def routingFootprint : Expr→Bool
  | .const _ | .pub _=>true
  | .col col nx=>if nx then col==eqL || col==eqH else routingColumn col
  | .add a b | .mul a b=>routingFootprint a && routingFootprint b
  | .neg a=>routingFootprint a
  | _=>false

theorem routing_footprint : cRoute.all routingFootprint=true := by decide

theorem routing_eval_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,routingColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (hn : ∀col,col=eqL ∨ col=eqH→tr.cell t ((pos+1)%tr.height t) col=
      tr'.cell t' ((pos'+1)%tr'.height t') col)
    (e : Expr) (he : routingFootprint e=true) : e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  induction e with
  | const | pub => rfl
  | col col nx =>
    cases nx
    · exact hc col he
    · apply hn
      simpa only [routingFootprint,ite_true,Bool.or_eq_true,beq_iff_eq] using he
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : routingFootprint a=true ∧ routingFootprint b=true := by simpa only [routingFootprint,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : routingFootprint a=true ∧ routingFootprint b=true := by simpa only [routingFootprint,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem routing_adjusted_transport (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (f : RouteFrame) (hf : f.Ordered) (len : Nat) (rb : Fp)
    (hc : ∀col,routingColumn col=true→tr.cell t pos col=routingAdjustedCell f len rb col)
    (hn : ∀col,col=eqL ∨ col=eqH→tr.cell t ((pos+1)%tr.height t) col=frameNext f col) :
    ∀e∈cRoute,e.eval tr t pos pub=0 := by
  intro e he
  rw [routing_eval_agree tr (routingAdjustedTrace f len rb) t pos 0 0 pub hc hn e
    (List.all_eq_true.mp routing_footprint e he)]
  exact routingAdjusted_local f hf len rb pub e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
