import ZkFormal.NearV3.Candidates.ProcRecordSelectedTraffic
import ZkFormal.NearV3.Candidates.ProcPriorRecordTrace
namespace ZkFormal.NearV3.Candidates.ProcRecordConcatCells
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcRecordConcatTraffic

def blockLength (b : NativeBlock) := 1+9*b.old.links.length
def blockCell (ids : List Nat) (b : NativeBlock) (i : Nat) :=
  ProcPriorRecordTrace.cells ids b.run.tau b.old.links i

theorem record_cells (ids : List Nat) (b : NativeBlock) (j : Nat) (hj:j<b.old.links.length) :
    (List.range 9).map (fun g=>blockCell ids b (1+9*j+g))=
    (ProcPriorRecordRows.rowsFor (b.old.links.getD j ⟨0,0,0⟩) j).map
      (ProcPriorRecordCells.cell ids b.run.tau) := by
  have hr:b.old.links[j]?=some (b.old.links.getD j ⟨0,0,0⟩):=by
    simp [List.getD,List.getElem?_eq_getElem hj]
  have hcell (g : Nat) (hg:g<9) : blockCell ids b (1+9*j+g)=
      ProcPriorRecordCells.cell ids b.run.tau ⟨j,g/3,g%3,b.old.links.getD j ⟨0,0,0⟩⟩ := by
    unfold blockCell
    rw [show 1+9*j+g=ProcPriorRecordTrace.place j (g/3) (g%3) by
      unfold ProcPriorRecordTrace.place; omega]
    exact ProcPriorRecordTrace.active ids b.run.tau b.old.links j (g/3) (g%3) _ hr (by omega) (by omega)
  have hm:(List.range 9).map (fun g=>blockCell ids b (1+9*j+g))=
      (List.range 9).map (fun g=>ProcPriorRecordCells.cell ids b.run.tau
        ⟨j,g/3,g%3,b.old.links.getD j ⟨0,0,0⟩⟩) :=
    List.map_congr_left (fun g hg=>hcell g (List.mem_range.mp hg))
  rw [hm]
  simp [List.range_succ,ProcPriorRecordRows.rowsFor]

theorem block_rows (ids : List Nat) (b : NativeBlock) :
    blockRows ids b=(List.range (blockLength b)).map (blockCell ids b) := by
  have he:blockLength b=1+9*b.old.links.length:=rfl
  rw [he,List.range_add,List.map_append,List.map_map]
  simp only [List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,
    Nat.zero_add,List.singleton_append]
  have hh:blockCell ids b 0=ProcPriorRecordCells.header ids b.run.tau :=
    ProcPriorRecordTrace.header _ _ _
  rw [hh]
  unfold blockRows
  congr 1
  have hg:=ProcRawRecordPhysical.range_groups b.old.links.length 9 (fun i=>[blockCell ids b (1+i)])
  simp only [←List.map_eq_flatMap] at hg
  simp only [Function.comp_def]
  rw [hg]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  simpa only [Nat.add_assoc] using (record_cells ids b j (List.mem_range.mp hj)).symm
end ZkFormal.NearV3.Candidates.ProcRecordConcatCells
