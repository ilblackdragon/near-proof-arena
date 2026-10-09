import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountNativeAllocation
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedPhysicalBounds
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestAllocation
import ZkFormal.NearV3.Assembly.Compute
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen

/-- Full native acceptance supplies all account scalar/count/byte bounds on
the CALLER-CHOSEN replay already used by the native node and UPS allocation. -/
theorem accepted_native_accounts {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (h:checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm:m.NativeValid k w)
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {writes : List (List Nat×Bytes)} {oldPost : PTrie} (hr:SizedAccountRun m.pre writes oldPost)
    {state : Bytes} (hup:oldPost.upsert keyBwState state=some m.result.trie) :
    ∃as,nativeAccountViews m.pre oldPost (appliedReceipts k w)=some as ∧
      as.length≤4481 ∧ (as=[] ∨ AcctWf as) ∧
      (∀a∈as,∀b∈a.pre++a.post,b<256) ∧
      (∀msg∈accountShaJobs as,∀b∈msg.bytes,b<256) := by
  have hwell:m.pre.wf=true:=by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  have hbytes:=checkD0a_preBytes hk hw h hm hv
  have hcount:=(forest_allocation_counts (m.pre::steps.map ImplicitStepV3.pre) hbytes).2
  have hvals:(NearSpecV3.valsOf m.pre).length<Algebra.P:=by
    simp only [forestBytes,List.flatMap_cons,List.length_append] at hcount
    rw [native_valsOf_eq]
    unfold Algebra.P
    omega
  have hgas:k.slotB2.gasLimit≤maxGasLimitD0:=by
    have hh:=(relD0a_iff B0 cb wb).mpr h
    simpa only [a1,hk,decide_eq_true_eq] using hh.2.1
  have hreceipts:=applyNewChunk_receipt_bound hm.run hgas
  obtain ⟨as,ha,hlen,hwf,hbs,hjobs⟩:=newchunk_rebased_accounts (TrieShape.of_wf _ hwell) hm.run
    oldPost hr.forget.skeleton (SizedAccountRun.wf hr hwell) hup hvals
    (by unfold Algebra.P;omega)
  exact ⟨as,ha,by omega,hwf,hbs,hjobs⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
