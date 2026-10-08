import ZkFormal.NearV3.Assembly.RoutingSpan
import ZkFormal.NearV3.Assembly.RoutingQCandidate

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def usesQBits : Expr→Bool
  | .col c _=> c==q || (decide (xb 12≤c) && decide (c<xb 19))
  | .add a b | .mul a b=>usesQBits a || usesQBits b
  | .neg a=>usesQBits a
  | _=>false

theorem route_qbits_free : cRoute.all (fun e=> !usesQBits e)=true := by decide

/-- Assignment on routing spans only. Other receipt groups may use these scratch
cells and need their own row assignments when a whole receipt trace is built. -/
def spanQPatch (tr : Trace Fp) (Q : Nat) : Trace Fp :=
  ⟨tr.log,fun t r c=>if c=q then Fp.ofNat Q else
    if xb 12≤c ∧ c<xb 19 then frameBit Q (c-xb 12) else tr.cell t r c⟩

theorem spanQPatch_eval (tr : Trace Fp) (Q t r : Nat) (pub : List Fp)
    (e : Expr) (he : usesQBits e=false) :
    e.eval (spanQPatch tr Q) t r pub=e.eval tr t r pub := by
  induction e with
  | col c nx =>
    have hc : c≠q ∧ ¬(xb 12≤c ∧ c<xb 19) := by simpa [usesQBits] using he
    simp [Expr.eval,Expr.evalWith,rowEnv,spanQPatch,hc.1,hc.2,Trace.height]
  | add a b ia ib =>
    simp only [usesQBits,Bool.or_eq_false_iff] at he
    rw [eval_add,eval_add,ia he.1,ib he.2]
  | mul a b ia ib =>
    simp only [usesQBits,Bool.or_eq_false_iff] at he
    rw [eval_mul,eval_mul,ia he.1,ib he.2]
  | neg a ia => rw [eval_neg,eval_neg,ia he]
  | const => rfl
  | pub => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl

theorem spanQPatch_bit (tr : Trace Fp) (Q t r j : Nat) (hj : j<7) :
    (spanQPatch tr Q).cell t r (xb (12+j))=frameBit Q j := by
  have hne : xb (12+j)≠q := by unfold xb q;omega
  have hrange : xb 12≤xb (12+j) ∧ xb (12+j)<xb 19 := by unfold xb;omega
  have hsub : xb (12+j)-xb 12=j := by unfold xb;omega
  simp only [spanQPatch,if_neg hne,if_pos hrange,hsub]

theorem spanQPatch_bound (tr : Trace Fp) (Q t r : Nat) (hQ : Q<128) (pub : List Fp) :
    RoutingQCandidate.qBound.eval (spanQPatch tr Q) t r pub=0 ∧
      ∀j,j<7 → (spanQPatch tr Q).cell t r (xb (12+j))=0 ∨
        (spanQPatch tr Q).cell t r (xb (12+j))=1 := by
  have hbits := eval_frame_bits (spanQPatch tr Q) t r pub 12 Q 7
    (spanQPatch_bit tr Q t r)
  rw [Nat.mod_eq_of_lt hQ] at hbits
  constructor
  · simp only [RoutingQCandidate.qBound,eval_mul3,eval_sub,eval_c,hbits]
    have hcell : (spanQPatch tr Q).cell t r q=Fp.ofNat Q := by simp only [spanQPatch,ite_true]
    rw [hcell]
    grind only
  · intro j hj
    rw [spanQPatch_bit tr Q t r j hj]
    exact frameBit_boolean Q j

theorem spanQPatch_route (tr : Trace Fp) (Q t r : Nat) (pub : List Fp)
    (hc : ∀e∈cRoute,e.eval tr t r pub=0) :
    ∀e∈cRoute,e.eval (spanQPatch tr Q) t r pub=0 := by
  intro e he
  have hf : usesQBits e=false := by
    simpa using List.all_eq_true.mp route_qbits_free e he
  rw [spanQPatch_eval tr Q t r pub e hf]
  exact hc e he

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
