import ZkFormal.NearV3.Candidates.ProcEntryNative
import ZkFormal.NearV3.Candidates.ProcHeader
namespace ZkFormal.NearV3.Candidates.ProcHeaderNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcEntryPosition ProcHeightBits ProcNativeRows ProcKindHeight

theorem native_header (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post) (hrd : ProcHeader.RoundOk rd)
    (hne : 0<rd.entries.toArray.size) (hx : rd.entries.toArray[0]!.x=0)
    (hrows : (procVs R).length+1≤2^22) (t : Nat) (pub : List Fp) :
    ∀ e ∈ Proc.cHdr,e.eval (trace R) t (roundStart R pre) pub=0 := by
  apply ProcHeader.header_constraints R rd rd.entries.toArray hrd hx (trace R) t _ pub
  · intro c
    rw [cell_cast,header_lookup R pre post rd he]
  · intro c
    have hb := ProcEntryNative.entry_index_lt R pre post rd he 0 hne
    have hmod : (roundStart R pre+1)%(trace R).height t=roundStart R pre+1 := by
      change _ % (2^22)=_
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod,cell_cast]
    have h := entry_lookup R pre post rd he 0 hne
    simp only [Nat.add_zero] at h
    rw [h]
end ZkFormal.NearV3.Candidates.ProcHeaderNative
