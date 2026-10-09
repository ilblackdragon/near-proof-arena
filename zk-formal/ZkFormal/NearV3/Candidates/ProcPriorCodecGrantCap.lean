import ZkFormal.NearV3.Candidates.ProcActualSegmentGrant
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGrantCap
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

theorem distribution (n M : Nat) (hn : 0<n) (hM : M≤u64Max)
    (allowed : Array Bool) (st : St) (hinv : GInv n M st)
    (hs : st.senderBudget.size=n) (hr : st.receiverBudget.size=n)
    (ha : allowed.size=n*n) (hg : st.granted.size=n*n)
    (k : Nat) (hk : k<n*n) :
    (distribute n allowed st).granted[k]! ≤M := by
  rw [ProcDistGrantBounds.granted_eq_add n M hn hM allowed st hinv hs hr ha hg k hk]
  have hb := (ProcDistGrantBounds.grid_bound n hn allowed st.senderBudget st.receiverBudget).1 k
  have hi := hinv k
  omega

/-- The actual process+distribution witness bounds every combined codec grant
by the PV86 bandwidth budget, rather than by an assumed comparator range. -/
theorem native (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (k : Nat) (hk : k<sp.ids.length*sp.ids.length) :
    (R.segs.getD k default).wfin+gd[k]! ≤4500000 := by
  rw [ProcActualSegmentGrant.total_grant sp hs ha prev tauV cv rs st ev R gd sord rord hprefix hr hg k hk]
  have hp := (ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev hprefix).2
  obtain ⟨hinv,hshape⟩ := ProcActualProcessFacts.prepared_facts sp hs ha prev st rs hp
  have hb := distribution sp.ids.length sp.params.maxShardBandwidth hs.n1
    (by rw [pv86_maxShard hs.params]; decide) sp.allowed (ProcNativeGrant.native st) hinv
    hshape.1 hshape.2.1 ha hshape.2.2 k hk
  simpa only [pv86_maxShard hs.params] using hb
end ZkFormal.NearV3.Candidates.ProcPriorCodecGrantCap
