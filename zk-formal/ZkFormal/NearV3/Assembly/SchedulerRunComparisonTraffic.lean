import ZkFormal.NearV3.Assembly.SchedulerRunCodecComparisons
import ZkFormal.NearV3.Candidates.MemComparisonPhysical
import ZkFormal.NearV3.Candidates.ProcActualMemoryRowBudget
import ZkFormal.NearV3.Candidates.ProcActualRunComparisonBudget
import ZkFormal.NearV3.Candidates.ProcActualNativeBudget
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem prior_run_data {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) :
    ∀R∈bs.map NativeBlock.run,∃sp prev,SchedPubOk sp ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) R.tau=.ok R ∧ R.conv.length≤4096 := by
  intro R hR
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hR
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
  have hidx:=hc.indexed i b hi
  have hs:=prepD0_sched hp b.pub (List.mem_iff_getElem?.mpr ⟨i,hidx.1.1⟩)
  have hr:ActualRun.run (ProcPreparedSequence.input b.pub b.old) b.run.tau=.ok b.run :=by rw [hidx.2.1];exact hidx.1.2
  have hconv:=ProcActualRequestCount.run_count _ _ _ hr
  have hraw:=(ProcPreparedSequence.input_bounds b.pub b.old hs).2.2
  exact ⟨b.pub,b.old,hs,hr,by omega⟩

theorem memory_rows_bound (rs : List Run) (N : Nat) (h:∀R∈rs,(Gen.Mem.rows R).size≤N) :
    (MemConcatCells.rows rs).size≤N*rs.length := by
  change (rs.flatMap (fun R=>(Gen.Mem.rows R).toList)).toArray.size≤_
  simp only [List.size_toArray]
  induction rs with
  | nil=>simp
  | cons R rs ih=>
    have hh:=h R (by simp)
    have ht:=ih (fun S hs=>h S (by simp [hs]))
    simp only [List.flatMap_cons,List.length_append,Array.length_toList,List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

theorem prior_run_capacities {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) :
    (MemConcatCells.rows (bs.map NativeBlock.run)).size≤2^22 ∧
    (ProcConcatGeometry.rows (bs.map NativeBlock.run)).length+1≤2^22 := by
  have hd:=prior_run_data hp B bs hc
  constructor
  · have hh:=memory_rows_bound (bs.map NativeBlock.run) 67200 (by
      intro R hR
      obtain ⟨sp,prev,hs,hr,_⟩:=hd R hR
      exact ProcActualMemoryRowBudget.run _ _ R hr hs.n64
        (ProcActualRunComparisonBudget.prepared_cost sp hs prev R.tau R hr))
    simp only [List.length_map] at hh
    have hn:=hc.length
    omega
  · apply ProcActualNativeBudget.native_capacity _ (by simpa using Nat.le_trans hc.length (by decide : 32≤33))
    intro R hR
    obtain ⟨sp,prev,hs,hr,hconv⟩:=hd R hR
    exact ⟨ProcPreparedSequence.input sp prev,hs.params,hr,hs.n64,hconv⟩

theorem flat_count_split {α β : Type} [BEq β] (xs : List α) (f g h : α→List β)
    (he:∀a∈xs,h a=f a++g a) (msg : β) :
    (xs.flatMap f).count msg+(xs.flatMap g).count msg=(xs.flatMap h).count msg := by
  induction xs with
  | nil=>simp
  | cons a xs ih=>
    have ha:=he a (by simp)
    have ht:=ih (fun b hb=>he b (by simp [hb]))
    simp only [List.flatMap_cons,List.count_append,ha,List.count_append] at *
    omega

theorem prior_run_comparison_count {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) (tm tp : Nat) (pub msg : List Fp) :
    tableBusCount Mem.interactions (MemConcatCells.trace (bs.map NativeBlock.run)) tm pub B_SCMP true msg+
    tableBusCount ProcBoundaryRepair.table.interactions (ProcConcatGeometry.trace (bs.map NativeBlock.run)) tp pub B_SCMP true msg=
      ((bs.flatMap (fun b=>b.run.cmps)).map cmpMsg).count msg := by
  have hd:=prior_run_data hp B bs hc
  have hcap:=prior_run_capacities hp B bs hc
  have ht:∀R∈bs.map NativeBlock.run,∀g∈R.segs,ProcActualMemoryTagSegments.SegTag g := by
    intro R hR
    obtain ⟨sp,prev,hs,hr,_⟩:=hd R hR
    exact ProcActualMemoryTagSegments.run _ _ R hr
  rw [MemComparisonPhysical.count _ hcap.1 ht,ProcComparisonPhysical.count _ (by omega)]
  simp only [List.map_flatMap]
  have hh:=flat_count_split (bs.map NativeBlock.run)
    (fun R=>(R.segs.flatMap (fun g=>ProcActualMemoryComparisonInventory.requests 0 g.ops)).map cmpMsg)
    (fun R=>(R.rounds.flatMap ProcActualRoundComparisonInventory.requests).map cmpMsg)
    (fun R=>R.cmps.map cmpMsg) (by
      intro R hR
      obtain ⟨sp,prev,hs,hr,_⟩:=hd R hR
      rw [ProcActualRunComparisonInventory.run _ _ R hr,List.map_append]) msg
  simpa only [List.flatMap_map,List.map_flatMap] using hh
end ZkFormal.NearV3.Assembly.CodecDigest
