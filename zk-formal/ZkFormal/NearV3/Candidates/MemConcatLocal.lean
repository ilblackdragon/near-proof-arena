import ZkFormal.Near.Extract.Common
import ZkFormal.NearV3.Candidates.MemConcatCells
import ZkFormal.NearV3.Candidates.MemHeight
namespace ZkFormal.NearV3.Candidates.MemConcatLocal
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def flatten (base : Run) (rs : List Run) : Run := {base with segs:=rs.flatMap Run.segs}

theorem fold_rows (gs : List Gen.Seg) (acc : Array (Array Nat)) :
    (gs.foldl (fun a g=>a++Gen.Mem.segRows g) acc).toList=
      acc.toList++gs.flatMap (fun g=>(Gen.Mem.segRows g).toList) := by
  induction gs generalizing acc with
  | nil=>simp
  | cons g gs ih=>simp only [List.foldl_cons,ih,Array.toList_append,List.flatMap_cons,List.append_assoc]

theorem rows (R : Run) : (Gen.Mem.rows R).toList=R.segs.flatMap (fun g=>(Gen.Mem.segRows g).toList) := by
  simpa only [Gen.Mem.rows,Array.toList_empty,List.nil_append] using fold_rows R.segs #[]

theorem flattened_rows (base : Run) (rs : List Run) :
    Gen.Mem.rows (flatten base rs)=MemConcatCells.rows rs := by
  apply Array.toList_inj.mp
  simp only [rows,flatten,MemConcatCells.rows,List.toList_toArray,List.flatMap_assoc]

theorem flattened_trace (base : Run) (rs : List Run) :
    MemHeight.trace (flatten base rs)=MemConcatCells.trace rs := by
  unfold MemHeight.trace MemConcatCells.trace
  rw [flattened_rows]

theorem table (base : Run) (rs : List Run)
    (hg:∀R∈rs,∀g∈R.segs,SegOk g)
    (hcap:(MemConcatCells.rows rs).size+1≤2^22) (t : Nat) (pub : List Fp) :
    TableLocal Mem.table (MemConcatCells.trace rs) t pub := by
  have hgs:∀g∈(flatten base rs).segs,SegOk g := by
    intro g h
    obtain ⟨R,hR,hg'⟩:=List.mem_flatMap.mp h
    exact hg R hR g hg'
  have hrows:(memVs (flatten base rs).segs).length+1≤2^22 := by
    have he: (Gen.Mem.rows (flatten base rs)).size=(memVs (flatten base rs).segs).length :=
      by simpa only [Array.length_toList] using (MemNativeCells.rows (flatten base rs)).length
    rw [←he,flattened_rows];exact hcap
  rw [←flattened_trace base rs]
  refine ⟨by change 1≤22;decide,by change 22≤22;decide,?_,?_⟩
  · exact MemHeight.mem_constraints _ hgs hrows t pub
  · intro r hr;exact MemHeight.mem_bits _ hgs t r pub hr
end ZkFormal.NearV3.Candidates.MemConcatLocal
