import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryFrame
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorCells
theorem constraints (xs : List Tagged)
    (hc:xs.length<2^22) (hchain:Chain xs)
    (hfirst:∀a,xs[0]?=some a→a.row.before=ProcPriorCarry.zero)
    (hqrows:∀a∈xs,a.row.event.query=true→a.row.before=ProcPriorValues.value a.row.event)
    (hbound:∀a∈xs,address a<ZkFormal.Algebra.P)
    (tt j : Nat) (hj:j<2^22) (pub : List Fp)
    (e : Expr) (he:e∈ProcPriorMemoryTable.constraints) :
    e.eval (trace xs) tt j pub=0 := by
  have hpub:e.pubBound=0:=ProcPriorTrace.bounds 0 0 0 e (List.mem_append_left _ he)
  rw [row_eval xs tt j pub e hpub]
  cases ha:xs[j]? with
  | none =>
    rw [cells_none xs j ha]
    apply ProcPriorBoundary.padding_constraints
    by_cases hl:j+1=2^22
    · exact Or.inl (by simp [hl])
    · right
      have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
      have hjn:xs.length≤j:=List.getElem?_eq_none_iff.mp ha
      have hnext:xs[j+1]?=none:=List.getElem?_eq_none_iff.mpr (by omega)
      rw [hm,cells_none xs (j+1) hnext]
    · exact he
  | some a =>
    have hja:j<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
    have hlast:j+1≠2^22:=by omega
    have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
    have ham:a∈xs:=List.mem_of_getElem? ha
    have hf:(if j=0 then (1:Fp) else 0)=0 ∨ a.row.before=ProcPriorCarry.zero := by
      by_cases hz:j=0
      · right; exact hfirst a (by simpa [hz] using ha)
      · left; simp [hz]
    have hq:=hqrows a ham
    rw [hm,cells_some xs j a ha]
    cases hb:xs[j+1]? with
    | none =>
      rw [cells_none xs (j+1) hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      exact ProcPriorBoundary.end_constraints a.row a.tau _ hf hq e he
    | some b =>
      rw [cells_some xs (j+1) b hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      have hsem:=chain_pair xs hchain j a b ha hb
      exact pair_constraints a b _ _ _ (hbound a ham)
        (hbound b (List.mem_of_getElem? hb)) hf hq hsem.1 hsem.2 e he

theorem bits (xs : List Tagged) (hc:xs.length<2^22) (tt j : Nat) (hj:j<2^22) (pub : List Fp)
    (wb rb cb : Nat) (i : Interaction) (hi:i∈ProcPriorMemoryTable.interactions wb rb cb)
    (e : Expr) (he:e∈i.mult) :
    e.eval (trace xs) tt j pub=0 ∨ e.eval (trace xs) tt j pub=1 := by
  have hpub:e.pubBound=0:=ProcPriorTrace.bounds wb rb cb e (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  rw [row_eval xs tt j pub e hpub]
  cases ha:xs[j]? with
  | none =>
    rw [cells_none xs j ha]
    exact Or.inl (ProcPriorCellBits.padding_bits _ _ _ _ wb rb cb i hi e he)
  | some a =>
    have hja:j<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
    have hlast:j+1≠2^22:=by omega
    have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
    rw [hm,cells_some xs j a ha]
    cases hb:xs[j+1]? with
    | none =>
      rw [cells_none xs (j+1) hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      exact ProcPriorCellBits.end_bits a.row a.tau _ wb rb cb i hi e he
    | some b =>
      rw [cells_some xs (j+1) b hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      exact pair_bits a b _ _ _ wb rb cb i hi e he

end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
