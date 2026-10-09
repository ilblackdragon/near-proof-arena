import ZkFormal.NearV3.Candidates.ProcEntryPosition
import ZkFormal.NearV3.Candidates.ProcEntryAdjacent
import ZkFormal.NearV3.Candidates.ProcKindHeight
namespace ZkFormal.NearV3.Candidates.ProcEntryNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcEntryPosition ProcHeightBits ProcNativeRows ProcKindHeight

theorem entry_index_lt (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) (i : Nat) (hi : i<rd.entries.toArray.size) :
    roundStart R pre+1+i<(procVs R).length := by
  simp only [List.size_toArray] at hi
  simp [roundStart,procVs,he,List.flatMap_append,roundVs]
  omega

/-- Physical adjacency is derived from the actual native row sequence. -/
theorem native_entry (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) (hlen : rd.Lr=rd.entries.toArray.size)
    (hok : ∀ i,i<rd.entries.toArray.size →
      ProcEntryScalar.EntryOk rd.z rd.entries.toArray[i]! ∧ rd.entries.toArray[i]!.x=i)
    (hrows : (procVs R).length+1≤2^22) (i : Nat) (hi : i<rd.entries.toArray.size)
    (t : Nat) (pub : List Fp) :
    ∀ e ∈ Proc.cEnt,e.eval (trace R) t (roundStart R pre+1+i) pub=0 := by
  have hc (c : Nat) : (trace R).cell t (roundStart R pre+1+i) c=
      Fp.ofNat ((entV R rd rd.entries.toArray i).cell c) := by
    rw [cell_cast,entry_lookup R pre post rd he i hi]
  apply ProcEntryAdjacent.entry_constraints R rd rd.entries.toArray i (hok i hi).1 hlen
    (hok i hi).2 (trace R) t _ pub hc
  · intro hn
    have his : i+1<rd.entries.toArray.size := by omega
    have hb := entry_index_lt R pre post rd he (i+1) his
    have hmod : (roundStart R pre+1+i+1)%(trace R).height t=roundStart R pre+1+(i+1) := by
      change _ % (2^22)=_
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hmod,cell_cast,entry_lookup R pre post rd he (i+1) his]
    change Fp.ofNat rd.entries.toArray[i+1]!.x=Fp.ofNat (i+1)
    rw [(hok (i+1) his).2]
  · intro hn
    have his : i+1<rd.entries.toArray.size := by omega
    have hb := entry_index_lt R pre post rd he (i+1) his
    have hmod : (roundStart R pre+1+i+1)%(trace R).height t=roundStart R pre+1+(i+1) := by
      change _ % (2^22)=_
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hmod,cell_cast,entry_lookup R pre post rd he (i+1) his]
    simp [PV.cell,Proc.ts,entV]
end ZkFormal.NearV3.Candidates.ProcEntryNative
