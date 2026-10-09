import ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}

theorem con (h : TableLocal table tr tt pub) {r : Nat} (hr : r<tr.height tt)
    {e : Expr} (he : e∈Acct.constraints) (hne : e≠oldFirst) : e.eval tr tt r pub=0 := by
  have hh := h.constr r hr (replaceFirst e) (List.mem_map.mpr ⟨e,he,rfl⟩)
  simpa only [replaceFirst,if_neg hne] using hh

theorem first_active (h : TableLocal table tr tt pub) (ha : tr.cell tt 0 Acct.act=1) :
    TableLocal AcctV3.table tr tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,h.bits⟩
  intro r hr e he
  by_cases heq : e=oldFirst
  · subst e
    by_cases hz : r=0
    · subst r
      have hh := h.constr 0 hr newFirst (List.mem_map.mpr ⟨oldFirst,
        by simp [oldFirst,Acct.constraints],by simp [replaceFirst]⟩)
      simp only [newFirst,eval_mul,eval_isFirst,eval_sub,eval_c,if_pos rfl,ha] at hh
      simp only [oldFirst,eval_mul,eval_isFirst,eval_not,eval_c,if_pos rfl]
      grind
    · simp only [oldFirst,eval_mul,eval_isFirst,if_neg hz]
      grind
  · exact con h hr he heq

theorem old_local (h : TableLocal AcctV3.table tr tt pub) : TableLocal table tr tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,h.bits⟩
  intro r hr e he
  obtain ⟨e,hold,rfl⟩ := List.mem_map.mp he
  by_cases heq : e=oldFirst
  · subst e
    change newFirst.eval tr tt r pub=0
    by_cases hz : r=0
    · subst r
      have hf := AcctV3Proof.row0 h hr
      have ha := ((AcctV3Proof.rowFacts h hr).1 hf).1
      simp only [newFirst,eval_mul,eval_isFirst,eval_sub,eval_c,if_pos rfl,ha,hf]
      grind
    · simp only [newFirst,eval_mul,eval_isFirst,if_neg hz]
      grind
  · simp only [replaceFirst,if_neg heq]
    exact h.constr r hr e hold

theorem inactive_all (h : TableLocal table tr tt pub) (ha : tr.cell tt 0 Acct.act=0) :
    ∀r,tr.cell tt r Acct.act=0 ∨ tr.height tt≤r := by
  intro r
  induction r with
  | zero => exact Or.inl ha
  | succ r ih =>
    by_cases hr : r+1<tr.height tt
    · have hc : tr.cell tt r Acct.act=0 := ih.resolve_right (by omega)
      have hh := con h (by omega : r<tr.height tt)
        (e:=mul3 .isTransition (Dsl.not (c Acct.act)) (n Acct.act))
        (by simp [Acct.constraints]) (by decide +kernel)
      simp only [eval_mul3,eval_isTransition,eval_not,eval_c,eval_n,
        if_neg (by omega : ¬r+1=tr.height tt),Nat.mod_eq_of_lt hr,hc] at hh
      exact Or.inl (by grind)
    · exact Or.inr (by omega)

theorem inactive_gates (h : TableLocal table tr tt pub) (ha : tr.cell tt 0 Acct.act=0)
    {r : Nat} (hr : r<tr.height tt) :
    tr.cell tt r Acct.act=0 ∧ tr.cell tt r Acct.af=0 ∧ tr.cell tt r Acct.gS=0 := by
  have hc := (inactive_all h ha r).resolve_right (by omega)
  have hf := con h hr (e:=.mul (c Acct.af) (Dsl.not (c Acct.act)))
    (by simp [Acct.constraints]) (by decide +kernel)
  have hg := con h hr (e:=sub (c Acct.gS) (.mul (c Acct.act) (c Acct.lo8)))
    (by simp [Acct.constraints]) (by decide +kernel)
  simp only [eval_mul,eval_not,eval_c,eval_sub,hc] at hf hg
  exact ⟨hc,by grind,by grind⟩

/-- Every candidate trace is either the original nonempty account case, or has
no account emission gates anywhere. No third case is introduced. -/
theorem local_cases (h : TableLocal table tr tt pub) :
    TableLocal AcctV3.table tr tt pub ∨
      ∀r,tr.height tt>r → tr.cell tt r Acct.act=0 ∧ tr.cell tt r Acct.af=0 ∧ tr.cell tt r Acct.gS=0 := by
  have hp : 0<tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have hb := con h hp (e:=Dsl.bool (c Acct.act)) (by simp [Acct.constraints]) (by decide +kernel)
  simp only [eval_bool,eval_c] at hb
  rcases bool_cases hb with hz|ho
  · exact Or.inr (fun r hr => inactive_gates h hz hr)
  · exact Or.inl (first_active h ho)

end ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
