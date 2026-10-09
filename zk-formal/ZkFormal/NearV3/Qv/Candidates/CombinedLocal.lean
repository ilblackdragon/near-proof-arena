import ZkFormal.NearV3.Qv.Candidates.CombinedTrace

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec ValueGen
variable {F : Type} [Lean.Grind.CommRing F]

/-- Complete local acceptance of the executable mixed queue table. Global bus
balance and arbitrary accepted-trace extraction are separate obligations. -/
theorem mixedTrace_local (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (hv : v.Valid) (d : Walk) (vs : List Record)
    (hvs : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List F)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+recordsSize vs≤2^log)
    (hpub : ∀ r, CombinedTable.kPublic.eval (mixedTrace (F:=F) (plan pre v pres resolve) vs log) 0 r pub =
      @Nat.cast F Lean.Grind.Semiring.natCast pres.length)
    (r : Nat) (hr : r<2^log) :
    ∀ e ∈ CombinedTable.table.allConstraints,
      e.eval (mixedTrace (F:=F) (plan pre v pres resolve) vs log) 0 r pub=0 := by
  let ws := plan pre v pres resolve
  let tr := mixedTrace (F:=F) ws vs log
  let N := (ws.flatMap Walk.rows).length
  have hN : 0<N := by dsimp [N,ws]; rw [plan_rows_length]; omega
  have hheight : tr.height 0=2^log := rfl
  have hfit' : N+recordsSize vs≤tr.height 0 := hfit
  have hc := mixedTrace_prefix (F:=F) ws vs log 0
  have hs (j : Nat) : tr.cell 0 (N+j)=recordsCell vs j := mixedTrace_suffix ws vs log 0 j
  have hs0 : tr.cell 0 N=recordsCell vs 0 := by simpa only [Nat.add_zero] using hs 0
  have hz (j : Nat) (x : Nat) (hx : 37≤x) : tr.cell 0 (N+j) x=0 := by
    rw [hs j]; exact recordsCell_high vs j x hx
  have hfirst := mixedTrace_first (F:=F) pre v pres resolve vs log 0
  have hlen : tr.cell 0 0 ValueTable.len=0 := by
    rw [hfirst,first_main_mode_zero]
    exact Lean.Grind.Semiring.natCast_zero
  have hwrap : tr.cell 0 0 ValueTable.act * (1 + -tr.cell 0 0 ValueTable.vf)=0 := by
    rw [hfirst,hfirst]
    simp [ValueTable.act,ValueTable.vf,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]
  by_cases hin : r<N
  · apply plan_prefix_all_constraints pre v pres resolve hv d tr 0 pub hc (by change N≤tr.height 0; omega) hpub
    · intro _
      change tr.cell 0 N ValueTable.act=0 ∨ tr.cell 0 N ValueTable.vf=1
      rw [hs0]
      exact recordsCell_first_marker vs hvs
    · intro _
      change tr.cell 0 N CombinedTable.walk=0
      rw [hs0]
      exact recordsCell_high vs 0 _ (by decide)
    · exact hin
  · have he : r=N+(r-N) := by omega
    change ∀ e ∈ CombinedTable.table.allConstraints,e.eval tr 0 r pub=0
    rw [he]
    exact combined_records_suffix_local vs hvs tr 0 N hN pub hfit'
      (fun j _ => hs j) (fun j _ x hx => hz j x hx) hwrap hlen (r-N) (by omega)

open ZkFormal.Algebra

theorem mixedTrace_table_local (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (hv : v.Valid) (d : Walk) (vs : List Record)
    (hvs : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List Fp)
    (hlog : 1≤log ∧ log≤CombinedTable.table.maxLog)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+recordsSize vs≤2^log)
    (hpub : ∀ r, CombinedTable.kPublic.eval (mixedTrace (F:=Fp) (plan pre v pres resolve) vs log) 0 r pub =
      @Nat.cast Fp Lean.Grind.Semiring.natCast pres.length) :
    TableLocal CombinedTable.table (mixedTrace (F:=Fp) (plan pre v pres resolve) vs log) 0 pub := by
  have hl := mixedTrace_local pre v pres resolve hv d vs hvs log pub hfit hpub
  refine ⟨hlog.1,hlog.2,?_,?_⟩
  · intro r hr e he
    exact hl r hr e (List.mem_append_left _ he)
  · intro r hr i hi b hb
    have hm : Expr.mul b (.add b (.neg (.const 1))) ∈ CombinedTable.table.allConstraints := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨i,hi,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
    have he := hl r hr _ hm
    simp only [Expr.eval,Expr.evalWith,Lean.Grind.Semiring.natCast_one] at he
    rcases Lean.Grind.Field.of_mul_eq_zero he with hz | ho
    · exact Or.inl hz
    · right
      change b.evalWith (rowEnv (mixedTrace (plan pre v pres resolve) vs log) 0 r pub)=1
      change b.evalWith (rowEnv (mixedTrace (plan pre v pres resolve) vs log) 0 r pub) + -(1 : Fp)=0 at ho
      grind only

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
