import ZkFormal.NearV3.Candidates.ProcHeightBits
namespace ZkFormal.NearV3.Candidates.ProcNativeRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def atRow (R : Run) (r : Nat) : PV :=
  if h : r<(procVs R).length then (procVs R)[r]
  else if r=(procVs R).length then tailV R else padPV

theorem rows_length (R : Run) : (Gen.Proc.rows R).size=(procVs R).length := by
  simpa using (proc_rows_rel R).length

theorem cell (R : Run) (r c : Nat) :
    natCell (Gen.Proc.rows R) (ProcHeightBits.pad R) r c=(atRow R r).cell c := by
  by_cases hr : r<(procVs R).length
  · have hs : r<(Gen.Proc.rows R).size := by rw [rows_length]; exact hr
    rw [atRow,dif_pos hr,natCell,natRow_lt _ _ hs]
    have h := ((proc_rows_rel R).get r (by simpa using hs) hr).cell c
    simpa using h
  · rw [atRow,dif_neg hr,natCell,natRow_ge _ _ (by rw [rows_length]; omega),ProcHeightBits.pad,rows_length]
    by_cases he : r=(procVs R).length
    · rw [if_pos he,if_pos he]; exact (tail_rel R).cell c
    · rw [if_neg he,if_neg he]; exact pad_rel.cell c

theorem active_records (R : Run) : ∀ V ∈ procVs R,
    V.act=1 ∧ V.act=V.kK+V.kH+V.kE := by
  intro V hv
  simp only [procVs,List.mem_append] at hv
  rcases hv with hv | hv
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
    exact ⟨rfl,rfl⟩
  · obtain ⟨rd,hrd,hv⟩ := List.mem_flatMap.1 hv
    simp only [roundVs,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨rfl,rfl⟩
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.1 hv
      exact ⟨rfl,rfl⟩

theorem act (R : Run) (r : Nat) :
    (atRow R r).act=if r<(procVs R).length then 1 else 0 := by
  unfold atRow
  split
  · rename_i h
    exact (active_records R _ (List.getElem_mem h)).1
  · split <;> rfl

theorem shape (R : Run) (r : Nat) :
    (atRow R r).act=(atRow R r).kK+(atRow R r).kH+(atRow R r).kE := by
  unfold atRow
  split
  · rename_i h
    exact (active_records R _ (List.getElem_mem h)).2
  · split <;> rfl

theorem first (R : Run) : atRow R 0=keyV R 0 := by
  rw [atRow,dif_pos (by rw [procVs_length]; omega)]
  rfl
end ZkFormal.NearV3.Candidates.ProcNativeRows
