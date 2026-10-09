import ZkFormal.NearV3.Candidates.ProcPriorTrace
namespace ZkFormal.NearV3.Candidates.ProcPriorTraceConstraints
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpec.Bandwidth
open ProcPriorRows ProcPriorCells ProcPriorActive ProcPriorBoundary ProcPriorIndexed ProcPriorTrace

theorem constraints (ids : List Nat) (rs : List LinkAllowance) (hn:ids.length≤64)
    (hc:(rows ids rs).length<2^22) (t tt j : Nat) (hj:j<2^22) (pub : List Fp)
    (e : Expr) (he:e∈ProcPriorMemoryTable.constraints) :
    e.eval (trace (rows ids rs) t) tt j pub=0 := by
  let xs:=rows ids rs
  change xs.length<2^22 at hc
  have hpub:e.pubBound=0:=bounds 0 0 0 e (List.mem_append_left _ he)
  rw [row_eval xs t tt j pub e hpub]
  cases ha:xs[j]? with
  | none =>
    rw [cells_none xs t j ha]
    apply padding_constraints
    by_cases hl:j+1=2^22
    · exact Or.inl (by simp [hl])
    · right
      have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
      have hjn:xs.length≤j:=List.getElem?_eq_none_iff.mp ha
      have hnext:xs[j+1]?=none:=List.getElem?_eq_none_iff.mpr (by omega)
      rw [hm,cells_none xs t (j+1) hnext]
    · exact he
  | some a =>
    have hja:j<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
    have hlast:j+1≠2^22:=by omega
    have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
    have ham:a∈xs:=List.mem_of_getElem? ha
    have hf:(if j=0 then (1:Fp) else 0)=0 ∨ a.before=ProcPriorCarry.zero := by
      by_cases hz:j=0
      · right; exact first_zero ids rs a (by simpa [hz] using ha)
      · left; simp [hz]
    have hq:=query_row ids rs a ham
    rw [hm,cells_some xs t j a ha]
    cases hb:xs[j+1]? with
    | none =>
      rw [cells_none xs t (j+1) hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      exact end_constraints a t _ hf hq e he
    | some b =>
      rw [cells_some xs t (j+1) b hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      obtain ⟨pre,post,hs⟩:=pair_split xs j a b ha hb
      have hsem:=pair_native ids rs pre post a b hs
      exact pair_constraints a b t _ _ _ (row_bound ids rs hn a ham)
        (row_bound ids rs hn b (List.mem_of_getElem? hb)) hf hq hsem.1 hsem.2 e he

end ZkFormal.NearV3.Candidates.ProcPriorTraceConstraints
