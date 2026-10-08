import ZkFormal.NearV3.Candidates.ProcPriorRecordTrace
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordConstraints
open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched
open ProcPriorCells ProcPriorRecordRows ProcPriorRecordTrace

theorem value_bound (r : LinkAllowance) (hr:LinkOk r) (j w g : Nat) (hw:w<3) :
    value ⟨j,w,g,r⟩<18446744073709551616 := by
  obtain ⟨hs,hrr,ha⟩:=hr
  unfold value
  split <;> try assumption
  split <;> assumption

theorem constraints (ids : List Nat) (rs : List LinkAllowance)
    (hr:∀r∈rs,LinkOk r) (hc:1+9*rs.length<2^22)
    (tt p : Nat) (hp:p<2^22) (pub : List Fp) (e : Expr)
    (he:e∈ProcPriorRecordTable.constraints) : e.eval (trace ids 0 rs) tt p pub=0 := by
  have hpub:e.pubBound=0:=bounds 0 0 0 0 0 e (List.mem_append_left _ he)
  rw [row_eval ids 0 rs tt p pub e hpub]
  by_cases h0:p=0
  · subst p
    rw [header]
    have hm:(0+1)%2^22=1:=by decide +kernel
    rw [hm]
    simp only [ite_true,show ¬0+1=2^22 by decide +kernel,ite_false]
    cases hfirst:rs[0]? with
    | none =>
      have hn:rs.length=0:=by have hh:=List.getElem?_eq_none_iff.mp hfirst; omega
      rw [padding ids 0 rs 1 (by omega)]
      exact ProcPriorRecordEmpty.empty_constraints ids 0 1 (Or.inr rfl) e he
    | some r =>
      have hs:=active ids 0 rs 0 0 0 r hfirst (by omega) (by omega)
      change cells ids 0 rs 1=_ at hs
      rw [hs]
      exact ProcPriorRecordHeader.start_constraints ids 0 r 1 (Or.inr rfl) e he
  · by_cases hpad:1+9*rs.length≤p
    · rw [padding ids 0 rs p hpad]
      apply ProcPriorRecordPadding.padding_constraints
      · by_cases hl:p+1=2^22
        · left; simp [hl]
        · right
          rw [Nat.mod_eq_of_lt (by omega : p+1<2^22),padding ids 0 rs (p+1) (by omega)]
      · exact he
    · let j:=(p-1)/9
      let w:=((p-1)%9)/3
      let g:=(p-1)%3
      have hj:j<rs.length:=by dsimp [j]; omega
      have hw:w<3:=by dsimp [w]; omega
      have hg:g<3:=by dsimp [g]; omega
      have hplace:p=place j w g:=by dsimp [j,w,g,place]; omega
      clear_value j w g
      have hlast:p+1≠2^22:=by omega
      rw [Nat.mod_eq_of_lt (by omega : p+1<2^22),if_neg h0,if_neg hlast,if_neg hlast]
      let r:=rs[j]
      have hget:rs[j]?=some r:=List.getElem?_eq_getElem hj
      have hv:=value_bound r (hr r (List.getElem_mem hj)) j w g hw
      rw [hplace,active ids 0 rs j w g r hget hw hg]
      by_cases hend:g=2
      · subst g
        by_cases hwEnd:w=2
        · subst w
          have hnext:place j 2 2+1=place (j+1) 0 0:=by unfold place; omega
          rw [hnext]
          cases hn:rs[j+1]? with
          | none =>
            have hlen:rs.length≤j+1:=List.getElem?_eq_none_iff.mp hn
            rw [padding ids 0 rs (place (j+1) 0 0) (by unfold place; omega)]
            exact ProcPriorRecordEnd.end_constraints ids 0 j r hv e he
          | some s =>
            rw [active ids 0 rs (j+1) 0 0 s hn (by omega) (by omega)]
            exact ProcPriorRecordNext.next_constraints ids 0 j r s hv e he
        · have hnext:place j w 2+1=place j (w+1) 0:=by unfold place; omega
          rw [hnext,active ids 0 rs j (w+1) 0 r hget (by omega) (by omega)]
          exact ProcPriorRecordWordEnd.end_constraints ids 0 j w r (by omega) hv e he
      · have hnext:place j w g+1=place j w (g+1):=by unfold place; omega
        rw [hnext,active ids 0 rs j w (g+1) r hget hw (by omega)]
        exact ProcPriorRecordInner.inner_constraints ids 0 j w g r hw (by omega) hv e he

end ZkFormal.NearV3.Candidates.ProcPriorRecordConstraints
