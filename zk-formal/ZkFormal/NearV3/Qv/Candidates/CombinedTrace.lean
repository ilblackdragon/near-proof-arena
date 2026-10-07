import ZkFormal.NearV3.Qv.Candidates.CombinedRecordPlacement

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air

theorem Record.rows_width (v : Record) : ∀ row ∈ v.rows,row.length=37 := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index => simp [Record.rows,emptyRows,wordRows,List.forall_mem_append,row_width,ValueTable.width] <;> grind [row_width,ValueTable.width]
    | buffer es => simp [Record.rows,bufferRows,wordRows,List.forall_mem_append,List.forall_mem_flatMap,row_width,ValueTable.width] <;> grind [row_width,ValueTable.width]
    | raw bytes =>
      by_cases hb : bytes.isEmpty
      all_goals simp [Record.rows,rawRows,hb,row_width,ValueTable.width] <;> grind [row_width,ValueTable.width]

theorem recordsCell_high {F : Type} [Lean.Grind.CommRing F]
    (vs : List Record) (r c : Nat) (hc : 37≤c) : recordsCell (F:=F) vs r c=0 := by
  have hw : ((recordsRows vs).getD r []).length≤37 := by
    by_cases hr : r<(recordsRows vs).length
    · have hm : (recordsRows vs).getD r [] ∈ recordsRows vs := by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr,Option.getD_some]
        exact List.getElem_mem hr
      obtain ⟨v,hv,hrow⟩ := List.mem_flatMap.mp hm
      exact Nat.le_of_eq (v.rows_width _ hrow)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (recordsRows vs).length≤r)]
  have h : ((recordsRows vs)[r]?.getD []).length≤c := by
    change ((recordsRows vs).getD r []).length≤c
    omega
  simp only [recordsCell,List.getD_eq_getElem?_getD,List.getElem?_eq_none h,Option.getD_none,
    Lean.Grind.Semiring.natCast_zero]

theorem recordsCell_first_marker {F : Type} [Lean.Grind.CommRing F]
    (vs : List Record) (hv : ∀ v ∈ vs,v.Valid) :
    recordsCell (F:=F) vs 0 ValueTable.act=0 ∨ recordsCell (F:=F) vs 0 ValueTable.vf=1 := by
  cases vs with
  | nil => left; simp [recordsCell,recordsRows,Lean.Grind.Semiring.natCast_zero]
  | cons v vs =>
    right
    have hvv := hv v (by simp)
    have hp : 0<v.rows.length := by rw [v.rows_length hvv]; exact v.size_pos
    simp only [recordsCell,recordsRows,List.flatMap_cons,append_getD_left _ _ 0 [] hp]
    have hm := v.markers hvv 0 v.size_pos
    rw [hm.2.1]
    exact Lean.Grind.Semiring.natCast_one

end ZkFormal.NearV3.Qv.Candidates.ValueGen

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air NearSpec ValueGen
variable {F : Type} [Lean.Grind.CommRing F]

def mixedRows (ws : List Walk) (vs : List Record) : List (List Nat) :=
  ws.flatMap Walk.rows ++ recordsRows vs

def mixedTrace (ws : List Walk) (vs : List Record) (log : Nat) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast (((mixedRows ws vs).getD r []).getD c 0) }

theorem mixedTrace_prefix (ws : List Walk) (vs : List Record) (log t : Nat) :
    PrefixCells (mixedTrace (F:=F) ws vs log) t ws := by
  apply PrefixCells.of_append ws (recordsRows vs)
  intro r _ c
  rfl

theorem mixedTrace_suffix (ws : List Walk) (vs : List Record) (log t j : Nat) :
    (mixedTrace (F:=F) ws vs log).cell t ((ws.flatMap Walk.rows).length+j)=recordsCell vs j := by
  funext c
  simp only [mixedTrace,mixedRows,append_getD_offset,recordsCell]

theorem mixedTrace_first (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (vs : List Record) (log t : Nat) :
    ∀ c, (mixedTrace (F:=F) (plan pre v pres resolve) vs log).cell t 0 c =
      @Nat.cast F Lean.Grind.Semiring.natCast
        (((mainWalk v pres.length resolve .delayed 0 v.delayed).row 0 7).getD c 0) := by
  intro c
  rw [mixedTrace_prefix _ _ _ _ 0 (by rw [plan_rows_length]; omega) c,plan_first_row]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
