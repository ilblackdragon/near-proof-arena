import ZkFormal.NearV3.Qv.Candidates.RecordList

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

theorem recordsCell_splice (pre post : List Record) (v : Record) (i : Nat)
    (hi : i<v.rows.length) :
    recordsCell (F:=F) (pre++v::post) ((recordsRows pre).length+i) = v.cell i := by
  funext c
  simp only [recordsCell,recordsRows,List.flatMap_append,List.flatMap_cons,
    append_getD_offset,append_getD_left _ _ i [] hi,Record.cell]

theorem recordsCell_after (pre post : List Record) (v : Record) :
    recordsCell (F:=F) (pre++v::post) ((recordsRows pre).length+v.rows.length) =
      recordsCell post 0 := by
  funext c
  simp only [recordsCell,recordsRows,List.flatMap_append,List.flatMap_cons,
    append_getD_offset]
  rw [show v.rows.length=v.rows.length+0 by omega,append_getD_offset]

theorem recordsCell_padding (vs : List Record) (r : Nat)
    (hr : (recordsRows vs).length≤r) : recordsCell (F:=F) vs r = fun _ => 0 := by
  funext c
  simp [recordsCell,List.getD_eq_getElem?_getD,List.getElem?_eq_none hr,
    Lean.Grind.Semiring.natCast_zero]

/-- All local constraints of a concatenation of executable queue records,
including cross-record transitions, padding, and cyclic physical boundaries.
The total-row fit remains explicit; no global queue capacity is assumed proved. -/
theorem recordsTrace_local (vs : List Record) (hv : ∀ v ∈ vs, v.Valid)
    (log : Nat) (hb : recordsSize vs≤2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (recordsTrace (F:=F) vs log) 0 r []=0 := by
  have hlen := recordsRows_length vs hv
  have hfit : (recordsRows vs).length≤2^log := by omega
  intro e hem
  rw [Expr.eval,rowEnv_recordEnv]
  change e.evalWith (recordEnv (recordsCell vs r) (recordsCell vs ((r+1)%2^log))
    (if r=0 then 1 else 0) (if r+1=2^log then 1 else 0)
    (if r+1=2^log then 0 else 1))=0
  by_cases ha : r<(recordsRows vs).length
  · obtain ⟨pre,v,post,i,he,hri,hi⟩ := flatMap_position Record.rows vs r ha
    have hvv : v.Valid := hv v (by rw [he]; simp)
    have hvp : ∀ w ∈ post, w.Valid := by intro w hw; apply hv; rw [he]; simp [hw]
    have hvl := v.rows_length hvv
    have htotal : (recordsRows vs).length =
        (recordsRows pre).length+v.rows.length+(recordsRows post).length := by
      simp [he,recordsRows,List.length_append,Nat.add_assoc]
    change r=(recordsRows pre).length+i at hri
    have hvfit : v.size≤2^log := by omega
    have hic : i<v.size := by omega
    have hcur : recordsCell (F:=F) vs r=v.cell i := by
      rw [he,hri]; exact recordsCell_splice pre post v i hi
    rw [hcur]
    apply v.placed_local hvv log hvfit i hic _ _ _ _ ?_ ?_ ?_ e hem
    · intro h0
      have hn : r≠0 := by omega
      simp [hn]
    · intro hint
      have hh : r+1<2^log := by omega
      have hne : ¬r+1=2^log := by omega
      refine ⟨?_,by simp [hne],by simp [hne]⟩
      rw [Nat.mod_eq_of_lt hh,he,show r+1=(recordsRows pre).length+(i+1) by omega]
      exact recordsCell_splice pre post v (i+1) (by omega)
    · intro hend
      by_cases hh : r+1=2^log
      · rw [hh,Nat.mod_self]
        exact recordsCell_first vs hv
      · have hlt : r+1<2^log := by omega
        rw [Nat.mod_eq_of_lt hlt,he,
          show r+1=(recordsRows pre).length+v.rows.length by omega,
          recordsCell_after]
        exact recordsCell_first post hvp
  · have hp : (recordsRows vs).length≤r := by omega
    rw [recordsCell_padding vs r hp]
    apply padding_record_local _ _ _ _ ?_ e hem
    by_cases hh : r+1=2^log
    · simp [hh,Lean.Grind.Semiring.zero_mul]
    · have hlt : r+1<2^log := by omega
      rw [Nat.mod_eq_of_lt hlt,recordsCell_padding vs (r+1) (by omega)]
      simp [Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
