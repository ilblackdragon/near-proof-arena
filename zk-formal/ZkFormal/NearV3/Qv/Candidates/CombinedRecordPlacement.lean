import ZkFormal.NearV3.Qv.Candidates.CombinedParserLift
import ZkFormal.NearV3.Qv.Candidates.RecordLocal

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

/-- Executable records placed after a nonempty prefix, including padding and
wrap to the prefix's ordinary parser marker. -/
theorem records_suffix_local (vs : List Record) (hv : ∀ v ∈ vs,v.Valid)
    (tr : Trace F) (t off : Nat) (hoff : 0<off)
    (hfit : off+recordsSize vs≤tr.height t)
    (hc : ∀ j, off+j<tr.height t → tr.cell t (off+j)=recordsCell vs j)
    (hwrap : tr.cell t 0 ValueTable.act * (1 + -tr.cell t 0 ValueTable.vf)=0)
    (j : Nat) (hj : off+j<tr.height t) :
    ∀ e ∈ ValueTable.table.allConstraints,e.eval tr t (off+j) []=0 := by
  have hlen := recordsRows_length vs hv
  intro e hem
  rw [Expr.eval,rowEnv_recordEnv]
  change e.evalWith (recordEnv (tr.cell t (off+j))
    (tr.cell t ((off+j+1)%tr.height t))
    (if off+j=0 then 1 else 0) (if off+j+1=tr.height t then 1 else 0)
    (if off+j+1=tr.height t then 0 else 1))=0
  rw [hc j hj]
  by_cases ha : j<(recordsRows vs).length
  · obtain ⟨pre,v,post,i,he,hri,hi⟩ := flatMap_position Record.rows vs j ha
    have hvv : v.Valid := hv v (by rw [he]; simp)
    have hvp : ∀ w ∈ post,w.Valid := by intro w hw; apply hv; rw [he]; simp [hw]
    have hvl := v.rows_length hvv
    have htotal : (recordsRows vs).length=
        (recordsRows pre).length+v.rows.length+(recordsRows post).length := by
      simp [he,recordsRows,List.length_append,Nat.add_assoc]
    change j=(recordsRows pre).length+i at hri
    have hvfit : v.size≤2^(tr.log t) := by change off+recordsSize vs≤2^(tr.log t) at hfit; omega
    have hic : i<v.size := by omega
    have hcur : recordsCell (F:=F) vs j=v.cell i := by
      rw [he,hri]; exact recordsCell_splice pre post v i hi
    rw [hcur]
    apply v.placed_local hvv (tr.log t) hvfit i hic _ _ _ _ ?_ ?_ ?_ e hem
    · intro _
      simp only [show off+j≠0 by omega,ite_false]
    · intro hint
      have hh : off+j+1<tr.height t := by omega
      have hne : off+j+1≠tr.height t := by omega
      refine ⟨?_,by simp [hne],by simp [hne]⟩
      rw [Nat.mod_eq_of_lt hh,show off+j+1=off+(j+1) by omega,hc (j+1) (by omega),he,
        show j+1=(recordsRows pre).length+(i+1) by omega]
      exact recordsCell_splice pre post v (i+1) (by omega)
    · intro hend
      by_cases hh : off+j+1=tr.height t
      · rw [hh,Nat.mod_self]; exact hwrap
      · have hlt : off+j+1<tr.height t := by omega
        rw [Nat.mod_eq_of_lt hlt,show off+j+1=off+(j+1) by omega,hc (j+1) (by omega),he,
          show j+1=(recordsRows pre).length+v.rows.length by omega,recordsCell_after]
        exact recordsCell_first post hvp
  · rw [recordsCell_padding vs j (by omega)]
    apply padding_record_local _ _ _ _ ?_ e hem
    by_cases hh : off+j+1=tr.height t
    · simp [hh,Lean.Grind.Semiring.zero_mul]
    · have hlt : off+j+1<tr.height t := by omega
      rw [Nat.mod_eq_of_lt hlt,show off+j+1=off+(j+1) by omega,hc (j+1) (by omega),
        recordsCell_padding vs (j+1) (by omega)]
      simp [Lean.Grind.Semiring.mul_zero]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem parser_public_independent (tr : Trace F) (t r : Nat) (pub : List F) :
    ∀ e ∈ ValueTable.table.allConstraints,e.eval tr t r pub=e.eval tr t r [] := by
  simp [ValueTable.table,Table.allConstraints,Table.bitConstraints,
    ValueTable.constraints,ValueTable.interactions,ValueTable.modes,ValueTable.phases,
    ValueTable.selectors,ValueTable.subpos,ValueTable.wordEnd,ValueTable.headerEnd,
    ValueTable.entryEnd,ValueTable.mode,ValueTable.counterBytes,ValueTable.same,
    ZkFormal.Near.Dsl.send,ZkFormal.Near.Dsl.recv,Expr.eval,Expr.evalWith,rowEnv,
    ZkFormal.Near.Dsl.c,ZkFormal.Near.Dsl.n,ZkFormal.Near.Dsl.k,ZkFormal.Near.Dsl.bool,
    ZkFormal.Near.Dsl.sub,ZkFormal.Near.Dsl.sum,ZkFormal.Near.Dsl.smul,
    ZkFormal.Near.Dsl.mul3,ZkFormal.Near.Dsl.eqG,ZkFormal.Near.Dsl.not,List.range_succ]

theorem combined_records_suffix_local (vs : List Record) (hv : ∀ v ∈ vs,v.Valid)
    (tr : Trace F) (t off : Nat) (hoff : 0<off) (pub : List F)
    (hfit : off+recordsSize vs≤tr.height t)
    (hc : ∀ j, off+j<tr.height t → tr.cell t (off+j)=recordsCell vs j)
    (hz : ∀ j, off+j<tr.height t → ∀ x,37≤x → tr.cell t (off+j) x=0)
    (hwrap : tr.cell t 0 ValueTable.act * (1 + -tr.cell t 0 ValueTable.vf)=0)
    (hlen : tr.cell t 0 ValueTable.len=0)
    (j : Nat) (hj : off+j<tr.height t) :
    ∀ e ∈ CombinedTable.table.allConstraints,e.eval tr t (off+j) pub=0 := by
  have hn : off+j+1=tr.height t ∨ tr.cell t ((off+j+1)%tr.height t) CombinedTable.walk=0 := by
    by_cases hh : off+j+1=tr.height t
    · exact Or.inl hh
    · right
      have hl : off+j+1<tr.height t := by omega
      rw [Nat.mod_eq_of_lt hl,show off+j+1=off+(j+1) by omega]
      exact hz (j+1) (by omega) _ (by decide)
  apply CombinedTable.parser_row_all_constraints tr t (off+j) pub (hz j hj) (by omega) hn
  · rcases hn with hh | hn
    · right
      simpa only [hh,Nat.mod_self] using hlen
    · exact Or.inl hn
  · intro e he
    rw [parser_public_independent tr t (off+j) pub e he]
    exact records_suffix_local vs hv tr t off hoff hfit hc hwrap j hj e he

end ZkFormal.NearV3.Qv.Candidates.ValueGen
