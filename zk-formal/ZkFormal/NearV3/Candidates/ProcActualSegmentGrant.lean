import ZkFormal.NearV3.Candidates.ProcActualMemoryFinal
import ZkFormal.NearV3.Candidates.ProcActualOutputAgreement
import ZkFormal.NearV3.Candidates.ProcNativeGrantLookup
namespace ZkFormal.NearV3.Candidates.ProcActualSegmentGrant
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

/-- The codec's process-memory endpoint plus distribution grant equals the
native final grant, with saturation discharged by the native budget invariant. -/
theorem total_grant (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (k : Nat) (hk : k<sp.ids.length*sp.ids.length) :
    (R.segs.getD k default).wfin+gd[k]! =
      (distribute sp.ids.length sp.allowed (ProcNativeGrant.native st)).granted[k]! := by
  obtain ⟨_,hp⟩ := ProcActualAfterMemoryReduction.prefix_facts _ cv st rs ev hprefix
  obtain ⟨hinv,hshape⟩ := ProcActualProcessFacts.prepared_facts sp hs ha prev st rs hp
  rw [(ProcActualMemoryFinal.run_link_final sp hs prev tau cv rs st ev R k hk hprefix hr).2]
  exact (ProcDistGrantBounds.event_granted sp.ids.length sp.params.maxShardBandwidth hs.n1
    (by rw [pv86_maxShard hs.params]; decide) sp.params sp.allowed
    (ProcActualInput.allowances sp.ids prev) (ProcNativeGrant.native st) hinv
    hshape.1 hshape.2.1 ha hshape.2.2 gd sord rord hg k hk).symm
theorem native_lookup (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (rs : List Round)
    (st : PState) (ev : Ev) (R : Run) (gd : Array Nat) (sord rord : List Nat)
    (hprefix : ProcActualPrefix.runPrefix (ProcPreparedSequence.input sp prev)=.ok (cv,st,rs,ev))
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (hg : distributeEv sp.ids.length sp.allowed st.sb st.rb
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntS
      (linkPass sp.ids.length sp.params sp.allowed (ProcActualInput.allowances sp.ids prev)).cntR
        =.ok (gd,sord,rord))
    (hd : sp.ids.Nodup) (a b o r : Nat)
    (ho : indexOf sp.ids a=some o) (hri : indexOf sp.ids b=some r) :
    ((((ProcActualNativeResult.finish sp prev (ProcNativeGrant.native st)).granted.find?
      (·.1==(a,b))).map Prod.snd).getD 0)=
      (R.segs.getD (o*sp.ids.length+r) default).wfin+gd[o*sp.ids.length+r]! := by
  have hob := (indexOf_spec ho).1
  have hrb := (indexOf_spec hri).1
  have hk : o*sp.ids.length+r<sp.ids.length*sp.ids.length := by
    have hm := Nat.mul_le_mul_right sp.ids.length (show o+1≤sp.ids.length by omega)
    rw [Nat.add_mul] at hm
    simp only [Nat.one_mul] at hm
    omega
  rw [ProcNativeGrantLookup.finish_lookup sp prev (ProcNativeGrant.native st) hd a b o r ho hri]
  exact (total_grant sp hs ha prev tau cv rs st ev R gd sord rord hprefix hr hg _ hk).symm
end ZkFormal.NearV3.Candidates.ProcActualSegmentGrant
