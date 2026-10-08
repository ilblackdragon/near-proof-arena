import ZkFormal.NearV3.Candidates.NativeAccountReplayAgreement
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedNativeAccounts

namespace ZkFormal.NearV3.Candidates.NativeAcceptedAccountViews
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃as,as.length≤4481 ∧ (as=[] ∨ AcctWf as) ∧
      (∀a∈as,∀b∈a.pre++a.post,b<256) ∧
      (∀M∈accountShaJobs as,∀b∈M.bytes,b<256) ∧
      (∀(writes : List (List Nat×Bytes))(oldPost : PTrie)(state : Bytes),
        SizedAccountRun m.pre writes oldPost→oldPost.upsert keyBwState state=some m.result.trie→
        nativeAccountViews m.pre oldPost (appliedReceipts k w)=some as) := by
  have hwell : m.pre.wf=true := by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  obtain ⟨writes,oldPost,mid,so,_,_,hr,hpair,hpost,_,hup⟩:=
    newchunk_old_tree_reconstruct (TrieShape.of_wf _ hwell) hwell hm.run
  obtain ⟨as,ha,hlen,hwf,hbytes,hjobs⟩:=accepted_native_accounts hk hw hc hm hv hr hup
  refine ⟨as,hlen,hwf,hbytes,hjobs,?_⟩
  intro writes' oldPost' state' hr' hup'
  rw [←NativeAccountReplayAgreement.scheduler_agreement hpair hr'.forget.skeleton
    hpost (SizedAccountRun.wf hr' hwell) hup hup' (appliedReceipts k w)]
  exact ha

end ZkFormal.NearV3.Candidates.NativeAcceptedAccountViews
