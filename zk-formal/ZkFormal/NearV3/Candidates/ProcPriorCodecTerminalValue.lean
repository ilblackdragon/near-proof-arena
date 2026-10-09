import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorAdjacent
import ZkFormal.NearV3.Candidates.ProcActualAllowanceBound
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalValue
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
open ProcPriorCodecRecordStep

/-- The actual native scheduler run discharges the low24 range condition; the
terminal serialized accumulator equals the full final allowance. -/
theorem native (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (present : Bool) (gb : Array Nat) (fwd inst : List (Nat×Nat)) (k : Nat)
    (rows : Array (Array Nat)) (cmps : List (Nat×Nat×Nat)) (mid out : State)
    (hk : k<R.n*R.n) (hi : k<sp.ids.length*sp.ids.length)
    (hp : forIn (List.range 7) (rows,cmps,0,0,0,0)
      (fun g s=>step (ProcPreparedSequence.input sp prev) R present gb fwd inst k 2 g s)=.ok mid)
    (ht : step (ProcPreparedSequence.input sp prev) R present gb fwd inst k 2 7 mid=.ok (.yield out)) :
    ∃row,out.1=mid.1.push row ∧ row[Codec.ap]! =0 ∧
      row[Codec.apost]! =(R.segs.getD k default).vfin ∧ row[Codec.big]! =0 := by
  have hb := ProcActualAllowanceBound.successful_run sp hs prev tau R hr k hi
  simpa only [Nat.mod_eq_of_lt hb] using
    ProcPriorCodecAccumulatorAdjacent.terminal (ProcPreparedSequence.input sp prev) R present gb fwd inst k rows cmps mid out hk hp ht
end ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalValue
