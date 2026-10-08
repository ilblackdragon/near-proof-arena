import ZkFormal.NearV3.Candidates.ProcRoundBoundary
import ZkFormal.NearV3.Candidates.ProcEntryNative
import ZkFormal.NearV3.Candidates.ProcHeaderContinue
namespace ZkFormal.NearV3.Candidates.ProcEntryHeaderNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcEntryPosition ProcHeightBits ProcNativeRows ProcKindHeight ProcRoundBoundary

theorem native_entry_header (R : Run) (pre post : List RoundD) (rd : RoundD)
    (he : R.rounds=pre++rd::post)
    (hf : ∀ next rest,post=next::rest → ProcHeaderContinue.Follows rd next)
    (hrows : (procVs R).length+1≤2^22) (i : Nat) (hi : i<rd.entries.toArray.size)
    (t : Nat) (pub : List Fp) :
    ∀ e ∈ Proc.cHdr,e.eval (trace R) t (roundStart R pre+1+i) pub=0 := by
  have hc (c : Nat) : (trace R).cell t (roundStart R pre+1+i) c=
      Fp.ofNat ((entV R rd rd.entries.toArray i).cell c) := by
    rw [cell_cast,entry_lookup R pre post rd he i hi]
  have hb := ProcEntryNative.entry_index_lt R pre post rd he i hi
  have hmod : (roundStart R pre+1+i+1)%(trace R).height t=roundStart R pre+1+(i+1) := by
    change _ % (2^22)=_
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  by_cases hl : i+1=rd.entries.toArray.size
  · have hn (c : Nat) : (trace R).cell t ((roundStart R pre+1+i+1)%(trace R).height t) c=
        Fp.ofNat ((match post with | []=>tailV R | next::_=>hdrV R next).cell c) := by
      rw [hmod,hl,cell_cast,after_round R pre post rd he]
      cases post <;> rfl
    cases post with
    | nil =>
      exact ProcHeaderContinue.entry_to_tail R rd rd.entries.toArray i hl
        (last_round R pre rd he) (trace R) t _ pub hc hn
    | cons next rest =>
      exact ProcHeaderContinue.entry_to_header R rd next rd.entries.toArray i hl
        (hf next rest rfl) (trace R) t _ pub hc hn
  · apply ProcHeaderContinue.entry_to_entry R rd rd.entries.toArray i (i+1) hl (trace R) t _ pub hc
    intro c
    rw [hmod,cell_cast,entry_lookup R pre post rd he (i+1) (by omega)]
end ZkFormal.NearV3.Candidates.ProcEntryHeaderNative
