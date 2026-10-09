import ZkFormal.NearV3.Candidates.ProcReplayAllowance
import ZkFormal.NearV3.Candidates.ProcReplayMetadata
namespace ZkFormal.NearV3.Candidates.ProcReplayEntries
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem maxAllowance_lt (I : Input)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p) :
    I.p.maxAllowance<P := by
  rw [pv86_calc hp]
  change 4500000<P
  decide

/-- All entry/count/index clauses of RunData follow from the executed generator
under the actual PV86 parameters, without any native memory-bound assumption. -/
theorem run_entries (I : Input) (tau : Nat) (R : Run)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h : Gen.run I tau=.ok R) :
    ∀rd∈R.rounds,0<rd.entries.toArray.size ∧ rd.Lr=rd.entries.toArray.size ∧
      ∀i,i<rd.entries.toArray.size →
        ProcEntryScalar.EntryOk rd.z rd.entries.toArray[i]! ∧ rd.entries.toArray[i]!.x=i := by
  intro rd hrd
  have hs := ProcReplayShape.run_shapes I tau R h rd hrd
  have hd := ProcReplayDecisions.run_decisions I tau R h rd hrd
  have ha := ProcReplayAllowance.run_allowances I tau R h rd hrd
  refine ⟨by rw [hs.2.1]; exact hs.1,hs.2.1.symm,?_⟩
  intro i hi
  have hm : rd.entries.toArray[i]!∈rd.entries := by
    rw [getElem!_pos rd.entries.toArray i hi]
    simpa using Array.getElem_mem_toList hi
  have hh := hd _ hm
  refine ⟨⟨hh.1,Nat.lt_of_le_of_lt (ha _ hm) (maxAllowance_lt I hp),hh.2⟩,hs.2.2 i hi⟩

/-- Native round-key/zero-ordinal sequencing is the sole remaining per-round
premise after replay metadata and all entry laws have been discharged. -/
theorem runData_of_roundOrder (I : Input) (tau : Nat) (R : Run)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h : Gen.run I tau=.ok R)
    (ho : ∀rd∈R.rounds,ProcHeader.RoundOk rd) : ProcData.RunData R := by
  have hm := ProcReplayMetadata.run_metadata I tau R h
  exact ⟨hm.1,fun rd hrd=>⟨ho rd hrd,run_entries I tau R hp h rd hrd⟩,hm.2⟩
end ZkFormal.NearV3.Candidates.ProcReplayEntries
