import ZkFormal.NearV3.Candidates.ProcActualMemoryCanonical
import ZkFormal.NearV3.Candidates.ProcActualProcessFacts
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryMetadata
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete NearSpecV3.Scheduler

theorem make (sp : SchedPub) (hs:SchedPubOk sp)
    (ha:sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (ht:tau≤32) (cv : Array CReq) (rs : List Round) (s : ProcActualReplayRound.Acc)
    (st : PState)
    (hcv:forIn (ProcPreparedSequence.input sp prev).raw #[] (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hp:ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hr:ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s)
    (kind i : Nat) (hk:kind≤2) (hi:i<(if kind=0 then sp.ids.length*sp.ids.length else sp.ids.length)) :
    let g:=ProcActualSegments.make (ProcPreparedSequence.input sp prev) tau s kind i
    g.vin0=b2n g.al ∧ g.addr<P ∧ g.vin0<P ∧ g.v0<P ∧ g.wfin<P := by
  let I:=ProcPreparedSequence.input sp prev
  have hc:=ProcActualMemoryChainSegments.make I tau s
    (ProcActualMemoryChainReplay.replay I cv rs s hr) kind i
  have hb:=ProcActualMemoryValues.initial_values I #[] #[] hs.params (ProcActualMemoryValues.empty_values _ 0)
  have hn:sp.ids.length*sp.ids.length≤4096:=Nat.mul_le_mul hs.n64 hs.n64
  have hsize:sp.ids.length≤64:=hs.n64
  have hidx:i<4096:=by split at hi <;> omega
  have haddr:addrOf tau kind i<P:=by unfold addrOf;change _<2013265921;omega
  have hP:2^29<P:=by decide
  dsimp only
  unfold ProcActualSegments.make
  split
  · rename_i hz
    subst kind
    have hbi:=hb.2.2.1 i
    have hf:=ProcActualMemoryFinal.prepared_link_final sp hs prev tau cv rs s st i (by simpa using hi) hcv hp hr
    have hg:st.g[i]!≤4500000:=by
      have hg:=(ProcActualProcessFacts.prepared_facts sp hs ha prev st rs hp).1 i
      change st.g[i]!+st.sb[i/sp.ids.length]!≤sp.params.maxShardBandwidth at hg
      rw [pv86_maxShard hs.params] at hg
      omega
    have hsmall: (ProcActualSegments.make I tau s 0 i).wfin<P:=by rw [hf.2];change _<2013265921;omega
    refine ⟨rfl,haddr,?_,?_,?_⟩
    · have hh:=b2n_le sp.allowed[i]!;change b2n sp.allowed[i]!<2013265921;omega
    · exact Nat.lt_of_le_of_lt hbi (by decide : 2^29-1<P)
    · simpa [ProcActualSegments.make,I] using hsmall
  · rename_i hzero
    split
    · rename_i hone
      subst kind
      refine ⟨rfl,haddr,by change 0<P;decide,?_,?_⟩
      · have hh:=hb.1 i;exact Nat.lt_of_le_of_lt hh (by decide : 2^29-1<P)
      · have hw:=ProcActualMemoryChainEntry.budget_last _ (by simp only [ProcActualSegments.make,ite_false,ite_true];rfl) _ _ _ hc
        change (ProcActualSegments.make I tau s 1 i).wfin<P
        rw [show (ProcActualSegments.make I tau s 1 i).wfin=0 from hw]
        decide
    · rename_i hone
      have he:kind=2:=by omega
      subst kind
      refine ⟨rfl,haddr,by change 0<P;decide,?_,?_⟩
      · have hh:=hb.2.1 i;exact Nat.lt_of_le_of_lt hh (by decide : 2^29-1<P)
      · have hw:=ProcActualMemoryChainEntry.budget_last _ (by simp only [ProcActualSegments.make,ite_false,ite_true];rfl) _ _ _ hc
        change (ProcActualSegments.make I tau s 2 i).wfin<P
        rw [show (ProcActualSegments.make I tau s 2 i).wfin=0 from hw]
        decide
end ZkFormal.NearV3.Candidates.ProcActualMemoryMetadata
