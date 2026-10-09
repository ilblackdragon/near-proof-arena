import ZkFormal.NearV3.Candidates.ProcHeaderContinue
import ZkFormal.NearV3.Candidates.ProcHeaderKeys
namespace ZkFormal.NearV3.Candidates.ProcData
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Native replay data laws; no AIR expressions or field evaluations occur here. -/
def RoundData (rd : RoundD) : Prop :=
  ProcHeader.RoundOk rd ∧ 0<rd.entries.toArray.size ∧ rd.Lr=rd.entries.toArray.size ∧
  ∀ i,i<rd.entries.toArray.size →
    ProcEntryScalar.EntryOk rd.z rd.entries.toArray[i]! ∧ rd.entries.toArray[i]!.x=i

def RunData (R : Run) : Prop :=
  (∀ rd rest,R.rounds=rd::rest → ProcHeaderKeys.Initial rd) ∧
  (∀ rd∈R.rounds,RoundData rd) ∧
  (∀ pre rd next rest,R.rounds=pre++rd::next::rest → ProcHeaderContinue.Follows rd next)
end ZkFormal.NearV3.Candidates.ProcData
