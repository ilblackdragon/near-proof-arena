import ZkFormal.NearV3.Candidates.ProcPositionCases
import ZkFormal.NearV3.Candidates.ProcKindHeight
namespace ZkFormal.NearV3.Candidates.ProcConcatGeometry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def rows (rs : List Run) : List PV := rs.flatMap procVs
def tail (rs : List Run) : PV := match rs.getLast? with | none=>padPV | some R=>tailV R
def atRow (rs : List Run) (r : Nat) : PV :=
  if h:r<(rows rs).length then (rows rs)[r] else if r=(rows rs).length then tail rs else padPV
def trace (rs : List Run) : Trace Fp := ⟨fun _=>22,fun _ r c=>Fp.ofNat ((atRow rs r).cell c)⟩
def start (pre : List Run) : Nat := (rows pre).length

theorem row_length (R : Run) : 16≤(procVs R).length := by rw [procVs_length]; omega

theorem block_lt (rs pre post : List Run) (R : Run) (he : rs=pre++R::post)
    (i : Nat) (hi : i<(procVs R).length) : start pre+i<(rows rs).length := by
  simp [start,rows,he,List.flatMap_append]
  omega

theorem block_lookup (rs pre post : List Run) (R : Run) (he : rs=pre++R::post)
    (i : Nat) (hi : i<(procVs R).length) : atRow rs (start pre+i)=ProcNativeRows.atRow R i := by
  have hlt := block_lt rs pre post R he i hi
  rw [atRow,dif_pos hlt,ProcNativeRows.atRow,dif_pos hi]
  unfold start rows
  simp only [he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left hi]

theorem tail_lookup (rs : List Run) : atRow rs (rows rs).length=tail rs := by simp [atRow]

theorem after_block (rs pre post : List Run) (R : Run) (he : rs=pre++R::post) :
    atRow rs (start pre+(procVs R).length)=
      match post with | []=>tailV R | S::_=>keyV S 0 := by
  cases post with
  | nil =>
    have hl : start pre+(procVs R).length=(rows rs).length := by simp [start,rows,he,List.flatMap_append]
    rw [hl,tail_lookup]
    simp [tail,he]
  | cons S rest =>
    have hs : rs=(pre++[R])++S::rest := by simpa [List.append_assoc] using he
    have h := block_lookup rs (pre++[R]) rest S hs 0 (by have := row_length S; omega)
    have hl : start (pre++[R])=start pre+(procVs R).length := by simp [start,rows,List.flatMap_append]
    simpa [hl,ProcNativeRows.first] using h

theorem active_cases (rs : List Run) (r : Nat) (hr : r<(rows rs).length) :
    ∃ pre R post i,rs=pre++R::post ∧ i<(procVs R).length ∧ r=start pre+i :=
  ProcPositionCases.flat_position procVs rs r hr
end ZkFormal.NearV3.Candidates.ProcConcatGeometry
