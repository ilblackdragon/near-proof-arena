import ZkFormal.NearV3.Candidates.MemNativeCells
namespace ZkFormal.NearV3.Candidates.MemConcatCells
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def rows (rs : List Run) : Array (Array Nat) :=(rs.flatMap (fun R=>(Gen.Mem.rows R).toList)).toArray
def records (rs : List Run) : List MV :=rs.flatMap (fun R=>memVs R.segs)
def trace (rs : List Run) :=SchedHeight.trace (rows rs) memPad

theorem relation (rs : List Run) : RRel (rows rs).toList (records rs) := by
  change RRel ((rs.flatMap (fun R=>(Gen.Mem.rows R).toList)).toArray.toList) (records rs)
  rw [List.toList_toArray]
  induction rs with
  | nil=>exact .nil
  | cons R rs ih=>
    exact (MemNativeCells.rows R).append ih

theorem length (rs : List Run) : (rows rs).size=(records rs).length := by
  simpa only [Array.length_toList] using (relation rs).length

theorem cell (rs : List Run) (r c : Nat) :
    natCell (rows rs) memPad r c=((records rs).getD r padV).cell c := by
  by_cases hr:r<(records rs).length
  · have hs:r<(rows rs).size:=by rw [length];exact hr
    rw [natCell,natRow_lt _ _ hs]
    have he:(records rs).getD r padV=(records rs)[r] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr]
    rw [he]
    exact ((relation rs).get r (by simpa using hs) hr).cell c
  · rw [natCell,natRow_ge _ _ (by rw [length];omega)]
    have he:(records rs).getD r padV=padV := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (records rs).length≤r)]
    rw [he]
    simp [memPad,gd_zrow,padV,MV.cell]
end ZkFormal.NearV3.Candidates.MemConcatCells
