import ZkFormal.NearV3.Candidates.SortEmpty
namespace ZkFormal.NearV3.Candidates.SortEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

private theorem replace_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (h:tr.cell t 0 Sort.act=1) (e : Expr) :
    (replaceFirst e).eval tr t r pub=e.eval tr t r pub := by
  unfold replaceFirst
  split
  · subst e
    by_cases hr:r=0
    · subst r;simp [firstSegment,sub,Dsl.not,c,k,Expr.eval,Expr.evalWith,rowEnv,h];rfl
    · simp [firstSegment,sub,Dsl.not,c,k,Expr.eval,Expr.evalWith,rowEnv,hr];grind
  · split
    · subst e
      by_cases hr:r=0
      · subst r;simp [firstFlag,sub,Dsl.not,c,k,Expr.eval,Expr.evalWith,rowEnv,h];rfl
      · simp [firstFlag,sub,Dsl.not,c,k,Expr.eval,Expr.evalWith,rowEnv,hr];grind
    · rfl

theorem active_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal table tr t pub) (ha:tr.cell t 0 Sort.act=1) :
    TableLocal {Sort.table with maxLog:=18} tr t pub := by
  refine ⟨h.log_ge,h.log_le,?_,h.bits⟩
  intro r hr e he
  have hh:=h.constr r hr (replaceFirst e) (List.mem_map.mpr ⟨e,he,rfl⟩)
  rw [replace_eval tr t r pub ha] at hh
  exact hh


theorem old_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal {Sort.table with maxLog:=18} tr t pub) : TableLocal table tr t pub := by
  refine ⟨h.log_ge,h.log_le,?_,h.bits⟩
  intro r hr e he
  change e∈Sort.constraints.map replaceFirst at he
  obtain ⟨e',hm,heq⟩:=List.mem_map.mp he
  rw [←heq,replace_eval tr t r pub (old_first_active tr t pub h)]
  exact h.constr r hr e' hm

theorem inactive_all (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal table tr t pub) (ha:tr.cell t 0 Sort.act=0) :
    ∀r,r<tr.height t→tr.cell t r Sort.act=0 := by
  intro r
  induction r with
  | zero=>intro _;exact ha
  | succ r ih=>
    intro hr
    have hi:=ih (by omega)
    let e:Expr:=mul3 .isTransition (Dsl.not (c Sort.act)) (n Sort.act)
    have he:e∈table.constraints:=by
      apply List.mem_map.mpr
      refine ⟨e,?_,?_⟩
      · simp [e,Sort.constraints]
      · rfl
    have hh:=h.constr r (by omega) e he
    simp only [e,mul3,Dsl.not,sub,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hi,
      Nat.mod_eq_of_lt hr,show r+1≠tr.height t by omega,ite_false] at hh
    grind

theorem inactive_count (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal table tr t pub) (ha:tr.cell t 0 Sort.act=0)
    (bus : Nat) (sd : Bool) (msg : List Fp) : tableBusCount table.interactions tr t pub bus sd msg=0 := by
  rw [tableBusCount_eq]
  have hz:(List.range (tr.height t)).flatMap (fun r=>rowTraffic table.interactions tr t r pub bus sd)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have ha:=inactive_all tr t pub h ha r (List.mem_range.mp hr)
    simp [table,Sort.table,Sort.interactions,rowTraffic,recv,Interaction.multNat,Interaction.multNat.go,
      c,Expr.eval,Expr.evalWith,rowEnv,ha]
  rw [hz]
  rfl

theorem empty_or_old (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal table tr t pub) :
    (∀bus sd msg,tableBusCount table.interactions tr t pub bus sd msg=0) ∨
      TableLocal {Sort.table with maxLog:=18} tr t pub := by
  have hb:=h.bits 0 (Nat.two_pow_pos _) (recv B_RIDS (c Sort.act) [c Sort.rr,c Sort.i,c Sort.bb])
    (by simp [table,Sort.table,Sort.interactions]) (c Sort.act) (by simp [recv])
  change tr.cell t 0 Sort.act=0 ∨ tr.cell t 0 Sort.act=1 at hb
  rcases hb with hb|hb
  · exact Or.inl (inactive_count tr t pub h hb)
  · exact Or.inr (active_local tr t pub h hb)

end ZkFormal.NearV3.Candidates.SortEmpty
