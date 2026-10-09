import ZkFormal.NearV3.Candidates.ProcComparisonRows
namespace ZkFormal.NearV3.Candidates.ProcComparisonPhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ProcConcatGeometry

theorem row (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub B_SCMP true=
      ProcComparisonRows.messages (atRow rs r) := by
  simp [ProcComparisonRows.messages,ProcBoundaryRepair.table,Proc.table,Proc.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,trace,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC]

theorem padding (rs : List Run) (r : Nat) (hr:(rows rs).length≤r) :
    ProcComparisonRows.messages (atRow rs r)=[] := by
  rw [atRow,dif_neg (by omega)]
  split
  · unfold tail
    split
    · exact ProcComparisonRows.pad
    · exact ProcComparisonRows.tail _
  · exact ProcComparisonRows.pad

theorem range_flatMap {α β : Type} (xs : List α) (d : α) (f : α→List β) :
    (List.range xs.length).flatMap (fun i=>f (xs.getD i d))=xs.flatMap f := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    rw [List.length_cons,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,List.getD_cons_zero,List.getD_cons_succ]
    rw [ih]

theorem physical (rs : List Run) (hcap:(rows rs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcBoundaryRepair.table.interactions
      (trace rs) t r pub B_SCMP true)=
      (rs.flatMap (fun R=>R.rounds.flatMap ProcActualRoundComparisonInventory.requests)).map cmpMsg := by
  simp only [row]
  rw [show 2^22=(rows rs).length+(2^22-(rows rs).length) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(rows rs).length)).flatMap
      (fun j=>ProcComparisonRows.messages (atRow rs ((rows rs).length+j)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    exact padding rs _ (by omega)
  rw [hz,List.append_nil]
  have ha:(List.range (rows rs).length).flatMap (fun r=>ProcComparisonRows.messages (atRow rs r))=
      (rows rs).flatMap ProcComparisonRows.messages := by
    rw [←range_flatMap (rows rs) padPV ProcComparisonRows.messages]
    apply ZkFormal.Near.flatMap_congr'
    intro r hr
    have hi:=List.mem_range.mp hr
    simp [atRow,hi,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  rw [ha]
  simp only [rows,List.flatMap_assoc,List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro R _
  simpa only [List.map_flatMap] using ProcComparisonRows.run R

theorem count (rs : List Run) (hcap:(rows rs).length≤2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcBoundaryRepair.table.interactions (trace rs) t pub B_SCMP true msg=
      ((rs.flatMap (fun R=>R.rounds.flatMap ProcActualRoundComparisonInventory.requests)).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical rs hcap t pub)
end ZkFormal.NearV3.Candidates.ProcComparisonPhysical
