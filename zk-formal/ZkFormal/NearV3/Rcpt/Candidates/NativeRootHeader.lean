import ZkFormal.NearV3.Rcpt.Candidates.NativeRootChain
import ZkFormal.NearV3.Assembly.NativeHeader

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

theorem implicit_last_unique {k : WalkD0} {root last other : Bytes}
    {pairs : List (Blk×Transition)} {steps : List ImplicitStepV3}
    (hv : ImplicitTraceValid k root pairs steps last)
    (hl : forIn pairs root (checkedImplicitStep k)=.ok other) : last=other := by
  induction hv with
  | nil root=>exact Except.ok.inj hl
  | cons root b t rest steps post last hr hp ht ih=>
    simp only [List.forIn_cons] at hl
    obtain ⟨step,hs,hl⟩:=ReexecV3D0.bind_ok' hl
    obtain ⟨post',hr',hp',rfl⟩:=checkedImplicitStep_success hs
    have he : post'=post:=by rw [hr] at hr'; exact Except.ok.inj hr'.symm
    subst post'
    exact ih hl

/-- The final root of the chosen chronological trace is the endorsed native header root. -/
theorem accepted_last_root {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    last=k.H.prevStateRoot := by
  obtain ⟨m',last',hm',hl,_,_,hh⟩:=checkD0_native_header hk hw hc
  have he:=hm.unique hm'
  subst m'
  exact (implicit_last_unique hv hl).trans hh.stateRoot.symm

/-- Exact endpoint-tagged ROOT conservation for the SAME accepted native trace. -/
theorem accepted_root_chain {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ([0]++k.slotB2.prevStateRoot.map UInt8.toNat)::
      nativeRootRecords 0 (m.result.trie::steps.map ImplicitStepV3.post)=
      nativeInputRoots 0 (m.pre::steps.map ImplicitStepV3.pre)++
        [[steps.length+1]++k.H.prevStateRoot.map UInt8.toNat] := by
  simpa only [accepted_last_root hk hw hc hm hv] using main_implicit_root_chain hm hv

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
