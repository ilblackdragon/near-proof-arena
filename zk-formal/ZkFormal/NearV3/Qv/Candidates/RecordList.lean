import ZkFormal.NearV3.Qv.Candidates.RecordPlaced

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air

theorem append_getD_offset {α : Type} (xs ys : List α) (i : Nat) (d : α) :
    (xs++ys).getD (xs.length+i) d = ys.getD i d := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : xs.length≤xs.length+i)]

theorem append_getD_left {α : Type} (xs ys : List α) (i : Nat) (d : α)
    (hi : i<xs.length) : (xs++ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem flatMap_position {α β : Type} (f : α → List β) (xs : List α) (r : Nat)
    (hr : r<(xs.flatMap f).length) :
    ∃ pre v post i, xs=pre++v::post ∧ r=(pre.flatMap f).length+i ∧ i<(f v).length := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons v vs ih =>
    by_cases h : r<(f v).length
    · exact ⟨[],v,vs,r,by simp,by simp,h⟩
    · have ht : r-(f v).length<(vs.flatMap f).length := by
        simp only [List.flatMap_cons,List.length_append] at hr; omega
      obtain ⟨pre,w,post,i,he,hi,hb⟩ := ih (r-(f v).length) ht
      refine ⟨v::pre,w,post,i,?_,?_,hb⟩
      · simp [he]
      · simp only [List.flatMap_cons,List.length_append]; omega

def recordsRows (vs : List Record) : List (List Nat) := vs.flatMap Record.rows

def recordsSize (vs : List Record) : Nat := (vs.map Record.size).sum

theorem recordsRows_length (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    (recordsRows vs).length=recordsSize vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [recordsRows,List.flatMap_cons,List.length_append,recordsSize,List.map_cons,List.sum_cons]
    rw [v.rows_length (hv v (by simp))]
    have hi := ih (by intro w hw; exact hv w (by simp [hw]))
    simpa only [recordsRows,recordsSize] using congrArg (fun n => v.size+n) hi

theorem recordsRows_first (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    ((recordsRows vs).getD 0 []).getD ValueTable.act 0 =
      ((recordsRows vs).getD 0 []).getD ValueTable.vf 0 := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    have h := hv v (by simp)
    have hp : 0<v.rows.length := by rw [v.rows_length h]; exact v.size_pos
    simp only [recordsRows,List.flatMap_cons,append_getD_left _ _ 0 [] hp]
    have hm := v.markers h 0 v.size_pos
    rw [hm.1,hm.2.1]
    rfl

variable {F : Type} [Lean.Grind.CommRing F]

def recordsCell (vs : List Record) (r c : Nat) : F :=
  @Nat.cast F Lean.Grind.Semiring.natCast (((recordsRows vs).getD r []).getD c 0)

def recordsTrace (vs : List Record) (log : Nat) : Trace F :=
  { log := fun _ => log, cell := fun _ r c => recordsCell vs r c }

theorem recordsCell_first (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    recordsCell (F:=F) vs 0 ValueTable.act *
      (1 + -recordsCell vs 0 ValueTable.vf)=0 := by
  cases vs with
  | nil => simp [recordsCell,recordsRows,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.zero_mul]
  | cons v vs =>
    have h := hv v (by simp)
    have hp : 0<v.rows.length := by rw [v.rows_length h]; exact v.size_pos
    simp only [recordsCell,recordsRows,List.flatMap_cons,append_getD_left _ _ 0 [] hp]
    have hm := v.markers h 0 v.size_pos
    simp only [hm.1,hm.2.1]
    simp [Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
      Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
