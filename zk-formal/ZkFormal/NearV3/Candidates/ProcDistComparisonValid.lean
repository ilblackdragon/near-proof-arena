import ZkFormal.NearV3.Candidates.ProcDistCellValid
import ZkFormal.NearV3.Candidates.ProcActualFinalBudgets
import ZkFormal.NearV3.Candidates.ProcNativeOldComparisonCapacity
namespace ZkFormal.NearV3.Candidates.ProcDistComparisonValid
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistGeneratorFactor ProcDistShardValid ProcDistCellBridge

def Inv (a:GridAcc) := CmpsOk a.2.1 ∧ ProcDistCellValid.Endpoints a.2.2.2
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem grid_step (I:Input)(R:Run)(hb:Budget R)(i:Nat)(a:GridAcc)(ha:Inv a)(out:ForInStep GridAcc)
    (h:gridStep I R i a=.ok out) : ExceptLoop.StepInv Inv out := by
  unfold gridStep at h
  obtain ⟨u,hu,h⟩:=bind_ok h
  cases h
  have hi:=ProcDistCellValid.loop_valid I R i (List.range R.n) _ u
    ⟨ha.1,hb.1 _,ha.2⟩ hu
  exact ⟨hi.1,hi.2.2⟩

theorem initial (I:Input)(R:Run)(hb:Budget R) :
    ProcDistCellValid.Endpoints ((List.range R.n).toArray.map
      (fun r=>(cntR R.n I.allowed r,R.fin.rb[r]!))) := by
  intro i
  by_cases hi:i<R.n
  · rw [List.map_toArray,getElem!_toArray_map_range R.n _ hi]
    exact hb.2 i
  · rw [getElem!_neg _ _ (by simp only [Array.size_map,List.size_toArray,List.length_range];omega)]
    exact Nat.zero_le _

theorem generated (I:Input)(R:Run)(hn:R.n≤64)(hb:Budget R)(d:DistOut)
    (h:distRows I R=.ok d) : CmpsOk d.cmps := by
  rw [native_eq] at h
  unfold build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  have hca:=ExceptLoop.invariant [0,1] (shardSide I R) (fun a=>CmpsOk a.2)
    (fun sd _ a h out ho=>ProcDistShardValid.side_valid I R sd hn hb a h out ho)
    (#[],[]) a (by intro q h;simp at h) ha
  obtain ⟨b,hbld,h⟩:=bind_ok h
  cases h
  have hcb:=ExceptLoop.invariant (List.range R.n) (gridStep I R) Inv
    (fun i _ a h out ho=>grid_step I R hb i a h out ho) _ b ⟨hca,initial I R hb⟩ hbld
  exact hcb.1

theorem prepared (sp:SchedPub)(hs:SchedPubOk sp)(prev:NearSpec.Bandwidth.State)(tau:Nat)(R:Run)
    (hr:ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)(d:DistOut)
    (hd:distRows (ProcPreparedSequence.input sp prev) R=.ok d) : CmpsOk d.cmps := by
  have hb:=ProcActualFinalBudgets.run _ tau R hr
  change ProcActualFinalBudgets.Bound sp.params.maxShardBandwidth R.fin at hb
  rw [pv86_maxShard hs.params] at hb
  have hn:=(ProcActualRunProjection.run_fields _ tau R hr).2.1
  apply generated _ R (by rw [hn];exact hs.n64) hb d hd

open ZkFormal.NearV3.Assembly.CodecDigest in
theorem prior_core {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs) :
    ∀b∈bs,CmpsOk (ProcNativeOldComparisonCapacity.distribution b).cmps := by
  intro b hb
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
  have hr:=(hc.indexed i b hi).1
  have hs:=prepD0_sched hp b.pub (List.mem_iff_getElem?.mpr ⟨i,hr.1⟩)
  exact prepared b.pub hs b.old i b.run hr.2 _
    (ProcNativeOldComparisonCapacity.distribution_eq b (hc.valid b hb).2)
end ZkFormal.NearV3.Candidates.ProcDistComparisonValid
