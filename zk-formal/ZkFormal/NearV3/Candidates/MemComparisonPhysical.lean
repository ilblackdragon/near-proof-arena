import ZkFormal.NearV3.Candidates.MemComparisonRows
import ZkFormal.NearV3.Candidates.MemConcatCells
import ZkFormal.NearV3.Candidates.ProcComparisonPhysical
namespace ZkFormal.NearV3.Candidates.MemComparisonPhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete MemConcatCells

theorem row (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic Mem.interactions (trace rs) t r pub B_SCMP true=
      MemComparisonRows.messages ((records rs).getD r padV) := by
  simp [MemComparisonRows.messages,Mem.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    trace,SchedHeight.trace,cell,B_SCMP,B_SOP,B_SFIN]

theorem physical (rs : List Run) (hcap:(rows rs).size≤2^22)
    (hg:∀R∈rs,∀g∈R.segs,ProcActualMemoryTagSegments.SegTag g) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic Mem.interactions (trace rs) t r pub B_SCMP true)=
      (rs.flatMap (fun R=>R.segs.flatMap (fun g=>ProcActualMemoryComparisonInventory.requests 0 g.ops))).map cmpMsg := by
  have hc:(records rs).length≤2^22:=by rw [←length];exact hcap
  simp only [row]
  rw [show 2^22=(records rs).length+(2^22-(records rs).length) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(records rs).length)).flatMap
      (fun j=>MemComparisonRows.messages ((records rs).getD ((records rs).length+j) padV))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    have he:(records rs).getD ((records rs).length+j) padV=padV := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (records rs).length≤(records rs).length+j)]
    rw [he,MemComparisonRows.pad]
  rw [hz,List.append_nil,ProcComparisonPhysical.range_flatMap]
  simp only [records,memVs,List.flatMap_assoc,List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro R hR
  apply ZkFormal.Near.flatMap_congr'
  intro g hg'
  exact MemComparisonRows.segment g (hg R hR g hg')

theorem count (rs : List Run) (hcap:(rows rs).size≤2^22)
    (hg:∀R∈rs,∀g∈R.segs,ProcActualMemoryTagSegments.SegTag g) (t : Nat) (pub msg : List Fp) :
    tableBusCount Mem.interactions (trace rs) t pub B_SCMP true msg=
      ((rs.flatMap (fun R=>R.segs.flatMap (fun g=>ProcActualMemoryComparisonInventory.requests 0 g.ops))).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical rs hcap hg t pub)
end ZkFormal.NearV3.Candidates.MemComparisonPhysical
