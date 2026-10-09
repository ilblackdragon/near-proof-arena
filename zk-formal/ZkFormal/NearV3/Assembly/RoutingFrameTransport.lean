import ZkFormal.NearV3.Assembly.RoutingNativeFrames

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def routeExpr : Expr→Bool
  | .const _ | .pub _=>true
  | .col c nx=> !nx || c==eqL || c==eqH
  | .add a b | .mul a b=>routeExpr a && routeExpr b
  | .neg a=>routeExpr a
  | _=>false

theorem route_constraints_footprint : cRoute.all routeExpr=true := by decide

theorem route_eval_agree (tr tr' : Trace Fp) (t r t' r' : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t r c=tr'.cell t' r' c)
    (hn : ∀c,c=eqL ∨ c=eqH → tr.cell t ((r+1)%tr.height t) c=
      tr'.cell t' ((r'+1)%tr'.height t') c) (e : Expr) (he : routeExpr e=true) :
    e.eval tr t r pub=e.eval tr' t' r' pub := by
  induction e with
  | const => rfl
  | pub => rfl
  | col c nx =>
    cases nx
    · exact hc c
    · apply hn
      simpa only [routeExpr,Bool.not_true,Bool.false_or,Bool.or_eq_true,beq_iff_eq] using he
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hs : routeExpr a=true ∧ routeExpr b=true := by simpa only [routeExpr,Bool.and_eq_true] using he
    simp only [eval_add,ia hs.1,ib hs.2]
  | mul a b ia ib =>
    have hs : routeExpr a=true ∧ routeExpr b=true := by simpa only [routeExpr,Bool.and_eq_true] using he
    simp only [eval_mul,ia hs.1,ib hs.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem frame_route_transport (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (f : RouteFrame) (hf : f.Ordered)
    (hc : ∀c,tr.cell t r c=frameCell f c)
    (hn : ∀c,c=eqL ∨ c=eqH → tr.cell t ((r+1)%tr.height t) c=frameNext f c) :
    ∀e∈cRoute,e.eval tr t r pub=0 := by
  intro e he
  have hfoot := List.all_eq_true.mp route_constraints_footprint e he
  rw [route_eval_agree tr (frameTrace f) t r 0 0 pub hc hn e hfoot]
  exact frame_route_constraints f hf pub e he

theorem frame_prefix_lower (acct : Bytes) (iv : Option Bytes×Option Bytes) (pos : Nat) :
    frameCell (frameOf acct iv (pos+1)) eqL=frameNext (frameOf acct iv pos) eqL := by
  rw [frame_cell_11,frame_next_lower]
  rfl

theorem frame_prefix_upper (acct : Bytes) (iv : Option Bytes×Option Bytes) (pos : Nat) :
    frameCell (frameOf acct iv (pos+1)) eqH=frameNext (frameOf acct iv pos) eqH := by
  rw [frame_cell_12,frame_next_upper]
  simp only [frameOf,samePrefix,Bool.and_assoc]
  congr 1
  simp only [Bool.and_eq_true,beq_iff_eq]
  grind only

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
