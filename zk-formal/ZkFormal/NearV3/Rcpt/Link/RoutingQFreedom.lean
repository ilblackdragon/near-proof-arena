import ZkFormal.NearV3.Rcpt.Link.RoutingAlias

namespace ZkFormal.NearV3.RcptLink.RoutingAlias
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

def replaceQ (tr : Trace Fp) (z : Fp) : Trace Fp :=
  ⟨tr.log,fun t r c => if c=q then z else tr.cell t r c⟩

theorem eval_replaceQ {e : Expr} (he : readsQ e=false) (tr : Trace Fp) (z : Fp)
    (t r : Nat) (pub : List Fp) : e.eval (replaceQ tr z) t r pub=e.eval tr t r pub := by
  induction e with
  | const n => rfl
  | pub i => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | col c nx =>
    have hc : c≠q := by simpa only [readsQ,beq_eq_false_iff_ne] using he
    simp [Expr.eval,Expr.evalWith,rowEnv,replaceQ,hc,Trace.height]
  | add a b ia ib =>
    have hh : readsQ a=false ∧ readsQ b=false := by simpa only [readsQ,Bool.or_eq_false_iff] using he
    change a.eval (replaceQ tr z) t r pub + b.eval (replaceQ tr z) t r pub = a.eval tr t r pub + b.eval tr t r pub
    rw [ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : readsQ a=false ∧ readsQ b=false := by simpa only [readsQ,Bool.or_eq_false_iff] using he
    change a.eval (replaceQ tr z) t r pub * b.eval (replaceQ tr z) t r pub = a.eval tr t r pub * b.eval tr t r pub
    rw [ia hh.1,ib hh.2]
  | neg a ia => exact congrArg Neg.neg (ia he)

/-- Every actual receipt local polynomial remains satisfied after replacing q
uniformly with any field element. This rules out an unextracted local q bound;
it does not assert preservation of cross-table bus balances. -/
theorem all_constraints_allow_constant_q {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal table tr t pub) (z : Fp) :
    ∀ r,r<tr.height t → ∀ e∈constraints,e.eval (replaceQ tr z) t r pub=0 := by
  intro r hr e he
  cases hq : readsQ e
  · rw [eval_replaceQ hq]
    exact h.constr r hr e he
  · have hm : e∈constraints.filter readsQ := List.mem_filter.mpr ⟨he,hq⟩
    rw [only_q_constraint] at hm
    obtain rfl := List.mem_singleton.mp hm
    simp [Dsl.mul3,Dsl.sub,Dsl.n,Dsl.c,Expr.eval,Expr.evalWith,rowEnv,replaceQ]
    grind

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem multiplicities_no_q :
    interactions.all (fun it => it.mult.all (fun e => !readsQ e))=true := by decide

/-- Uniform q replacement preserves ALL actual receipt TableLocal obligations,
including multiplicity bits and table-height bounds. Bus messages can change. -/
theorem tableLocal_replaceQ {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal table tr t pub) (z : Fp) : TableLocal table (replaceQ tr z) t pub := by
  refine ⟨h.log_ge,h.log_le,all_constraints_allow_constant_q h z,?_⟩
  intro r hr it hi e he
  have hq := List.all_eq_true.mp (List.all_eq_true.mp multiplicities_no_q it hi) e he
  have hq' : readsQ e=false := by simpa using hq
  rw [eval_replaceQ hq']
  exact h.bits r hr it hi e he

end ZkFormal.NearV3.RcptLink.RoutingAlias
