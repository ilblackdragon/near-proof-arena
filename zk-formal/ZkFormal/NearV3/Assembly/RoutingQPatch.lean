import ZkFormal.NearV3.Assembly.RoutingQFill

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Expression-level scratch noninterference, including cyclic next-row reads. -/
theorem eval_scratch_agree {tr tr' : Trace Fp} {t r : Nat} {pub : List Fp}
    (hh : tr'.height t=tr.height t) (e : Expr)
    (hc : ∀k nx, (¬(xb 12≤k ∧ k≤xb 18) ∨ readsScratch nx e=true) →
      (rowEnv tr' t r pub).col k nx=(rowEnv tr t r pub).col k nx) :
    e.eval tr' t r pub=e.eval tr t r pub := by
  induction e with
  | const => rfl
  | col k nx =>
    exact hc k nx (by
      by_cases h : xb 12≤k ∧ k≤xb 18
      · right; simp [readsScratch,h]
      · exact Or.inl h)
  | pub => rfl
  | isFirst => rfl
  | isLast => simp [Expr.eval,Expr.evalWith,rowEnv,hh]
  | isTransition => simp [Expr.eval,Expr.evalWith,rowEnv,hh]
  | add a b ia ib =>
    simp only [eval_add]
    congr 1
    · apply ia; intro k nx hk; apply hc; rcases hk with hk|hk
      · exact Or.inl hk
      · right; simp only [readsScratch]; simp_all
    · apply ib; intro k nx hk; apply hc; rcases hk with hk|hk
      · exact Or.inl hk
      · right; simp only [readsScratch]; simp_all
  | mul a b ia ib =>
    simp only [eval_mul]
    congr 1
    · apply ia; intro k nx hk; apply hc; rcases hk with hk|hk
      · exact Or.inl hk
      · right; simp only [readsScratch]; simp_all
    · apply ib; intro k nx hk; apply hc; rcases hk with hk|hk
      · exact Or.inl hk
      · right; simp only [readsScratch]; simp_all
  | neg a ia =>
    simp only [eval_neg]
    rw [ia (by simpa only [readsScratch] using hc)]

/-- Replacing receiver-row scratch bits by any boolean bits preserves every
original receipt polynomial. Next-row scratch cells may change as well. -/
theorem receiver_constraints_patch {tr tr' : Trace Fp} {t r : Nat} {pub : List Fp}
    (hh : tr'.height t=tr.height t)
    (hs : ∀k,4≤k → k≤26 → tr.cell t r k=if k=sV then 1 else 0)
    (hs' : ∀k,4≤k → k≤26 → tr'.cell t r k=if k=sV then 1 else 0)
    (hc : ∀k nx, ¬(xb 12≤k ∧ k≤xb 18) →
      (rowEnv tr' t r pub).col k nx=(rowEnv tr t r pub).col k nx)
    (hb : ∀i,i<7 → tr'.cell t r (xb (12+i))=0 ∨ tr'.cell t r (xb (12+i))=1)
    (hold : ∀e∈RcptV3.constraints,e.eval tr t r pub=0) :
    ∀e∈RcptV3.constraints,e.eval tr' t r pub=0 := by
  intro e he
  have hm : atState sV e ∈ RcptV3.constraints.map (atState sV) := List.mem_map.mpr ⟨e,he,rfl⟩
  rw [←atState_eval hs' e]
  by_cases hx : readsScratch false (atState sV e)=true
  · have hf : atState sV e ∈ (RcptV3.constraints.map (atState sV)).filter (readsScratch false) :=
      List.mem_filter.mpr ⟨hm,hx⟩
    rw [receiver_scratch_constraints] at hf
    obtain ⟨i,hi,hei⟩ := List.mem_map.mp hf
    rw [←hei]
    have hb' := hb i (List.mem_range.mp hi)
    simp only [eval_bool,eval_c]
    rcases hb' with hb'|hb' <;> rw [hb'] <;> grind
  · have hn : readsScratch true (atState sV e)=false := by
      have := List.all_eq_true.mp receiver_next_scratch _ hm
      simpa using this
    rw [eval_scratch_agree hh _ (by
      intro k nx hk
      apply hc
      rcases hk with hk|hk
      · exact hk
      · cases nx <;> simp_all),atState_eval hs e]
    exact hold e he

/-- The preceding receiver-length row is unaffected by changing the next row's
seven scratch cells. This includes the cyclic AIR next-row environment. -/
theorem predecessor_constraints_patch {tr tr' : Trace Fp} {t r : Nat} {pub : List Fp}
    (hh : tr'.height t=tr.height t)
    (hs : ∀k,4≤k → k≤26 → tr.cell t r k=if k=sVL then 1 else 0)
    (hs' : ∀k,4≤k → k≤26 → tr'.cell t r k=if k=sVL then 1 else 0)
    (hc : ∀k nx, nx=false ∨ ¬(xb 12≤k ∧ k≤xb 18) →
      (rowEnv tr' t r pub).col k nx=(rowEnv tr t r pub).col k nx)
    (hold : ∀e∈RcptV3.constraints,e.eval tr t r pub=0) :
    ∀e∈RcptV3.constraints,e.eval tr' t r pub=0 := by
  intro e he
  have hm : atState sVL e ∈ RcptV3.constraints.map (atState sVL) := List.mem_map.mpr ⟨e,he,rfl⟩
  have hn : readsScratch true (atState sVL e)=false := by
    have := List.all_eq_true.mp predecessor_next_scratch _ hm
    simpa using this
  rw [←atState_eval hs' e,eval_scratch_agree hh _ (by
    intro k nx hk
    apply hc
    cases nx with
    | false => exact Or.inl rfl
    | true => rcases hk with hk|hk; exact Or.inr hk; simp_all),atState_eval hs e]
  exact hold e he

end ZkFormal.NearV3.Assembly.RoutingQCandidate
