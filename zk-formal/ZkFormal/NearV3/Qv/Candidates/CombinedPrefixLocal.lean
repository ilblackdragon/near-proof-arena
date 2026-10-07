import ZkFormal.NearV3.Qv.Candidates.CombinedLocalCompose

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec
open CombinedTable
variable {F : Type} [Lean.Grind.CommRing F]

theorem plan_first_row (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    ((plan pre v pres resolve).flatMap Walk.rows).getD 0 []=
      (mainWalk v pres.length resolve .delayed 0 v.delayed).row 0 7 := by rfl

theorem PrefixCells.parser_marker {tr : Trace F} {t : Nat} {ws : List Walk}
    (h : PrefixCells tr t ws) (d : Walk) (r : Nat) (hr : r<(ws.flatMap Walk.rows).length) :
    tr.cell t r ValueTable.vf=1 := by
  obtain ⟨i,pos,hi,hp,he,hrow⟩ := flat_rows_generated ws d r hr
  rw [h r hr _,hrow]
  simp [ValueTable.vf,Lean.Grind.Semiring.natCast_one]

theorem plan_prefix_first (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (tr : Trace F) (t r : Nat) (pub : List F) (hc : PrefixCells tr t (plan pre v pres resolve)) :
    ∀ e ∈ firstConstraints,e.eval tr t r pub=0 := by
  by_cases hr : r=0
  · subst r
    apply first_main_constraints v pres.length resolve tr t pub
    intro c
    rw [hc 0 (by rw [plan_rows_length]; omega) c,plan_first_row]
  · exact nonfirst_constraints tr t r pub hr

theorem plan_prefix_parser_next (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (d : Walk) (tr : Trace F) (t r : Nat)
    (hc : PrefixCells tr t (plan pre v pres resolve))
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length≤tr.height t)
    (hr : r<((plan pre v pres resolve).flatMap Walk.rows).length)
    (hsuffix : ((plan pre v pres resolve).flatMap Walk.rows).length<tr.height t →
      tr.cell t ((plan pre v pres resolve).flatMap Walk.rows).length ValueTable.act=0 ∨
      tr.cell t ((plan pre v pres resolve).flatMap Walk.rows).length ValueTable.vf=1) :
    tr.cell t ((r+1)%tr.height t) ValueTable.act=0 ∨
      tr.cell t ((r+1)%tr.height t) ValueTable.vf=1 := by
  let N := ((plan pre v pres resolve).flatMap Walk.rows).length
  change N≤tr.height t at hfit
  change r<N at hr
  by_cases hlast : r+1=tr.height t
  · rw [hlast,Nat.mod_self]
    exact Or.inr (hc.parser_marker d 0 (by change 0<N; omega))
  · have hh : r+1<tr.height t := by omega
    rw [Nat.mod_eq_of_lt hh]
    by_cases hp : r+1<N
    · exact Or.inr (hc.parser_marker d (r+1) hp)
    · have he : r+1=N := by omega
      rw [he]
      exact hsuffix (by change N<tr.height t; omega)

/-- Every generated walk-prefix row satisfies the entire candidate table,
including interaction-bit constraints. Only the first parser suffix row's
ordinary marker cells and the public K binding remain external. -/
theorem plan_prefix_all_constraints (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (hv : v.Valid) (d : Walk) (tr : Trace F) (t : Nat) (pub : List F)
    (hcells : PrefixCells tr t (plan pre v pres resolve))
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length≤tr.height t)
    (hpub : ∀ r, kPublic.eval tr t r pub = @Nat.cast F Lean.Grind.Semiring.natCast pres.length)
    (hsuffix : ((plan pre v pres resolve).flatMap Walk.rows).length<tr.height t →
      tr.cell t ((plan pre v pres resolve).flatMap Walk.rows).length ValueTable.act=0 ∨
      tr.cell t ((plan pre v pres resolve).flatMap Walk.rows).length ValueTable.vf=1)
    (hexit : ((plan pre v pres resolve).flatMap Walk.rows).length<tr.height t →
      tr.cell t ((plan pre v pres resolve).flatMap Walk.rows).length walk=0)
    (r : Nat) (hr : r<((plan pre v pres resolve).flatMap Walk.rows).length) :
    ∀ e ∈ table.allConstraints,e.eval tr t r pub=0 := by
  let ws := plan pre v pres resolve
  obtain ⟨i,pos,hi,hp,he,hrow⟩ := flat_rows_generated ws d r hr
  have hc := hcells.at_word d i pos hi hp
  rw [←he] at hc
  have hw : ws.getD i d ∈ ws := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact List.getElem_mem hi
  apply plan_row_all_constraints pre v pres resolve hv (ws.getD i d) hw pos _ tr t r pub hc
  · intro hz
    subst pos
    simp [List.getD_eq_getElem?_getD,List.head?_eq_getElem?,ws]
  · exact plan_prefix_parser_next pre v pres resolve d tr t r hcells hfit hr hsuffix
  · exact hpub r
  · exact plan_prefix_first pre v pres resolve tr t r pub hcells
  · exact plan_trace_physical_last pre v pres resolve d tr t pub hcells hfit r hr
  · exact plan_trace_exit pre v pres resolve d tr t pub hcells hfit hexit r hr
  · exact plan_trace_neighbor_equations pre v pres resolve d tr t pub hcells hfit r hr

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
