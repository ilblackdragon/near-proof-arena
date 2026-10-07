import ZkFormal.NearV3.Qv.Candidates.CombinedRowLayout

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

theorem rowOffset_le (ws : List Walk) (i : Nat) :
    rowOffset ws i≤(ws.flatMap Walk.rows).length := by
  induction ws generalizing i with
  | nil => simp [rowOffset]
  | cons w ws ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [rowOffset_cons,List.flatMap_cons,List.length_append]
      exact Nat.add_le_add_left (ih i) _

theorem row_index_lt (ws : List Walk) (d : Walk) (i pos : Nat)
    (hi : i<ws.length) (hp : pos<(ws.getD i d).kind.bytes.length) :
    rowOffset ws i+pos<(ws.flatMap Walk.rows).length := by
  have hn := rowOffset_next ws d i hi
  have hb := rowOffset_le ws (i+1)
  rw [Walk.rows_length] at hn
  omega

theorem Kind.bytes_pos (k : Kind) : 0<k.bytes.length := by
  cases k <;> simp [Kind.bytes]

variable {F : Type} [Lean.Grind.CommRing F]

/-- Only generated cells are required, not local acceptance or bus balance. -/
def PrefixCells (tr : Trace F) (t : Nat) (ws : List Walk) : Prop :=
  ∀ r<(ws.flatMap Walk.rows).length, ∀ c,
    tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      (((ws.flatMap Walk.rows).getD r []).getD c 0)

theorem PrefixCells.at_word {tr : Trace F} {t : Nat} {ws : List Walk}
    (h : PrefixCells tr t ws) (d : Walk) (i pos : Nat)
    (hi : i<ws.length) (hp : pos<(ws.getD i d).kind.bytes.length) :
    ∀ c, tr.cell t (rowOffset ws i+pos) c = @Nat.cast F Lean.Grind.Semiring.natCast
      (((ws.getD i d).row pos ((ws.getD i d).kind.bytes.getD pos 0)).getD c 0) := by
  intro c
  rw [h _ (row_index_lt ws d i pos hi hp) c,flat_rows_at ws d i pos hi (by simpa [Walk.rows_length] using hp),
    Walk.rows_at _ pos hp]

theorem plan_trace_neighbor_equations (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (d : Walk) (tr : Trace F) (t : Nat) (pub : List F)
    (hcells : PrefixCells tr t (plan pre v pres resolve))
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length≤tr.height t)
    (r : Nat) (hr : r<((plan pre v pres resolve).flatMap Walk.rows).length) :
    ∀ e ∈ insideConstraints ++ startConstraints ++ stepConstraints,e.eval tr t r pub=0 := by
  let ws := plan pre v pres resolve
  change (ws.flatMap Walk.rows).length≤tr.height t at hfit
  change r<(ws.flatMap Walk.rows).length at hr
  obtain ⟨i,pos,hi,hp,he,_⟩ := flat_rows_generated ws d r hr
  let w := ws.getD i d
  have hc := hcells.at_word d i pos hi hp
  have hc' : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos (w.kind.bytes.getD pos 0)).getD c 0) := by simpa only [he] using hc
  by_cases hin : pos+1<w.kind.bytes.length
  · have hb := row_index_lt ws d i (pos+1) hi hin
    have hn := hcells.at_word d i (pos+1) hi hin
    have hmod : (r+1)%tr.height t=rowOffset ws i+(pos+1) := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hn' : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
        ((w.row (pos+1) (w.kind.bytes.getD (pos+1) 0)).getD c 0) := by
      simpa only [hmod] using hn
    exact w.internal_neighbor_constraints pos _ _ tr t r pub hc' hn' (by omega)
  · have hend : pos+1=w.kind.bytes.length := by dsimp [w] at hin ⊢; omega
    by_cases hnext : i+1<ws.length
    · let nw := ws.getD (i+1) d
      have hp0 := nw.kind.bytes_pos
      have hn := hcells.at_word d (i+1) 0 hnext hp0
      have ho := rowOffset_next ws d i hi
      rw [Walk.rows_length] at ho
      have he' : r+1=rowOffset ws (i+1)+0 := by dsimp [w] at hend; omega
      have hb := row_index_lt ws d (i+1) 0 hnext hp0
      have hmod : (r+1)%tr.height t=rowOffset ws (i+1)+0 := by
        rw [Nat.mod_eq_of_lt (by omega),he']
      have hn' : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
          ((nw.row 0 (nw.kind.bytes.getD 0 0)).getD c 0) := by simpa only [hmod] using hn
      exact plan_neighbor_equations pre v pres resolve d i hnext pos _ _ tr t r pub hc' hn' hend
    · have hlast : i+1=ws.length := by omega
      have hf := plan_at_final pre v pres resolve d i hi
      have hf' : w.final=true := by
        change w.final=(i+1==ws.length) at hf
        simpa only [hlast,beq_self_eq_true] using hf
      exact w.final_neighbor_constraints pos _ tr t r pub hc' hend hf'

theorem plan_coordinate_last (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (d : Walk) (i pos : Nat)
    (hi : i<(plan pre v pres resolve).length)
    (hp : pos<((plan pre v pres resolve).getD i d).kind.bytes.length) :
    rowOffset (plan pre v pres resolve) i+pos+1=
      ((plan pre v pres resolve).flatMap Walk.rows).length ↔
    pos+1=((plan pre v pres resolve).getD i d).kind.bytes.length ∧
      ((plan pre v pres resolve).getD i d).final=true := by
  let ws := plan pre v pres resolve
  let w := ws.getD i d
  change i<ws.length at hi
  change pos<w.kind.bytes.length at hp
  change rowOffset ws i+pos+1=(ws.flatMap Walk.rows).length ↔
    pos+1=w.kind.bytes.length ∧ w.final=true
  have ho := rowOffset_next ws d i hi
  rw [Walk.rows_length] at ho
  have hf := plan_at_final pre v pres resolve d i hi
  change w.final=(i+1==ws.length) at hf
  constructor
  · intro he
    have ht : pos+1=w.kind.bytes.length := by
      by_cases hn : pos+1=w.kind.bytes.length
      · exact hn
      · have hb := row_index_lt ws d i (pos+1) hi (by change pos+1<w.kind.bytes.length; omega)
        omega
    have hl : i+1=ws.length := by
      by_cases hn : i+1=ws.length
      · exact hn
      · have hh : i+1<ws.length := by omega
        have hb := row_index_lt ws d (i+1) 0 hh (ws.getD (i+1) d).kind.bytes_pos
        dsimp [w] at ht
        omega
    exact ⟨ht,by simpa only [hl,beq_self_eq_true] using hf⟩
  · rintro ⟨ht,hfinal⟩
    have hl : i+1=ws.length := by rw [hfinal] at hf; exact (beq_iff_eq.mp hf.symm)
    have he := rowOffset_end ws
    rw [← hl] at he
    dsimp [w] at ht
    omega

theorem plan_trace_physical_last (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (d : Walk) (tr : Trace F) (t : Nat) (pub : List F)
    (hcells : PrefixCells tr t (plan pre v pres resolve))
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length≤tr.height t)
    (r : Nat) (hr : r<((plan pre v pres resolve).flatMap Walk.rows).length) :
    (mul3 .isLast (c CombinedTable.walk) (Dsl.not (c CombinedTable.wend))).eval tr t r pub=0 := by
  let ws := plan pre v pres resolve
  obtain ⟨i,pos,hi,hp,he,_⟩ := flat_rows_generated ws d r hr
  have hc := hcells.at_word d i pos hi hp
  rw [← he] at hc
  apply Walk.physical_last_equation _ pos _ tr t r pub hc
  intro hh
  apply (plan_coordinate_last pre v pres resolve d i pos hi hp).mp
  change rowOffset ws i+pos+1=(ws.flatMap Walk.rows).length
  change (ws.flatMap Walk.rows).length≤tr.height t at hfit
  change r<(ws.flatMap Walk.rows).length at hr
  omega

theorem PrefixCells.of_append {tr : Trace F} {t : Nat} (ws : List Walk)
    (suffix : List (List Nat))
    (hc : ∀ r<((ws.flatMap Walk.rows)++suffix).length, ∀ c,
      tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
        ((((ws.flatMap Walk.rows)++suffix).getD r []).getD c 0)) : PrefixCells tr t ws := by
  intro r hr c
  have hb : r<((ws.flatMap Walk.rows)++suffix).length := by simp only [List.length_append]; omega
  rw [hc r hb c]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hr]

theorem plan_trace_exit (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (d : Walk) (tr : Trace F) (t : Nat) (pub : List F)
    (hcells : PrefixCells tr t (plan pre v pres resolve))
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length≤tr.height t)
    (hexit : ((plan pre v pres resolve).flatMap Walk.rows).length<tr.height t →
      tr.cell t ((plan pre v pres resolve).flatMap Walk.rows).length CombinedTable.walk=0)
    (r : Nat) (hr : r<((plan pre v pres resolve).flatMap Walk.rows).length) :
    (mul3 .isTransition (c CombinedTable.wend) (n CombinedTable.walk)).eval tr t r pub=0 := by
  let ws := plan pre v pres resolve
  obtain ⟨i,pos,hi,hp,he,_⟩ := flat_rows_generated ws d r hr
  have hc := hcells.at_word d i pos hi hp
  rw [← he] at hc
  apply Walk.exit_equation _ pos _ tr t r pub hc
  intro hend hfinal
  have hb := (plan_coordinate_last pre v pres resolve d i pos hi hp).mpr ⟨hend,hfinal⟩
  change rowOffset ws i+pos+1=(ws.flatMap Walk.rows).length at hb
  change (ws.flatMap Walk.rows).length≤tr.height t at hfit
  by_cases hh : r+1=tr.height t
  · exact Or.inl hh
  · apply Or.inr
    have hn : r+1=(ws.flatMap Walk.rows).length := by omega
    have hlt : (ws.flatMap Walk.rows).length<tr.height t := by omega
    rw [Nat.mod_eq_of_lt (by omega),hn]
    exact hexit hlt

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
