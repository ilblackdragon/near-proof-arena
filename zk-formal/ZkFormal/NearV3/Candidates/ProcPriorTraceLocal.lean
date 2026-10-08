import ZkFormal.NearV3.Candidates.ProcPriorTraceConstraints
namespace ZkFormal.NearV3.Candidates.ProcPriorTraceLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpec.Bandwidth
open ProcPriorRows ProcPriorCells ProcPriorActive ProcPriorBoundary ProcPriorIndexed ProcPriorTrace
open ProcPriorCellBits

theorem bits (xs : List Row) (hc:xs.length<2^22) (t tt j : Nat) (hj:j<2^22) (pub : List Fp)
    (wb rb cb : Nat) (i : Interaction) (hi:i∈ProcPriorMemoryTable.interactions wb rb cb)
    (e : Expr) (he:e∈i.mult) :
    e.eval (trace xs t) tt j pub=0 ∨ e.eval (trace xs t) tt j pub=1 := by
  have hpub:e.pubBound=0:=bounds wb rb cb e (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  rw [row_eval xs t tt j pub e hpub]
  cases ha:xs[j]? with
  | none =>
    rw [cells_none xs t j ha]
    exact Or.inl (padding_bits _ _ _ _ wb rb cb i hi e he)
  | some a =>
    have hja:j<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
    have hlast:j+1≠2^22:=by omega
    have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
    rw [hm,cells_some xs t j a ha]
    cases hb:xs[j+1]? with
    | none =>
      rw [cells_none xs t (j+1) hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      exact end_bits a t _ wb rb cb i hi e he
    | some b =>
      rw [cells_some xs t (j+1) b hb]
      simp only [nextSame,nextInverse,hb,ite_false,hlast]
      exact pair_bits a b t _ _ _ wb rb cb i hi e he

/-- Native ID lookup and last-record-wins rows form an honest memory trace.
Only the ordinary row capacity and public-ID count bounds remain parameters. -/
theorem native_local (ids : List Nat) (rs : List LinkAllowance) (hn:ids.length≤64)
    (hc:(rows ids rs).length<2^22) (t tt wb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorMemoryTable.table wb rb cb) (trace (rows ids rs) t) tt pub := by
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro j hj e he
    exact ProcPriorTraceConstraints.constraints ids rs hn hc t tt j hj pub e he
  · intro j hj i hi e he
    exact bits (rows ids rs) hc t tt j hj pub wb rb cb i hi e he

/-- The degree-reduced, horizontally fusible witness is an executable lift. -/
theorem native_gated_local (ids : List Nat) (rs : List LinkAllowance) (hn:ids.length≤64)
    (hc:(rows ids rs).length<2^22) (t tt wb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorMemoryGated.table wb rb cb)
      (ProcPriorMemoryGated.liftTrace (trace (rows ids rs) t) tt pub) tt pub := by
  exact ProcPriorMemoryGated.lift_local wb rb cb _ tt pub
    (native_local ids rs hn hc t tt wb rb cb pub)

end ZkFormal.NearV3.Candidates.ProcPriorTraceLocal
