import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootEndpoints
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootHeader

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

theorem prepared_trace_root_endpoints {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {p : Prep} {hint : Hint} (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    p.hdr.prevStateRoot=k.slotB2.prevStateRoot ∧ p.hdr.postStateRoot=k.H.prevStateRoot ∧
      p.hdr.K=steps.length := by
  obtain ⟨hpre,hpost,hK⟩:=prepD0_root_endpoints hp hk
  obtain ⟨_,_,_,_,hcw,_,_⟩:=checkD0_native_header hk hw hc
  have hl:=hv.length
  simp only [List.length_zip,hcw,Nat.min_self] at hl
  exact ⟨hpre,hpost,hK.trans hl.symm⟩

/-- Exact prepared public ROOT endpoint records for the unchanged native trace. -/
theorem prepared_root_chain {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {p : Prep} {hint : Hint} (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ([0]++p.hdr.prevStateRoot.map UInt8.toNat)::
      nativeRootRecords 0 (m.result.trie::steps.map ImplicitStepV3.post)=
      nativeInputRoots 0 (m.pre::steps.map ImplicitStepV3.pre)++
        [[p.hdr.K+1]++p.hdr.postStateRoot.map UInt8.toNat] := by
  obtain ⟨hpre,hpost,hK⟩:=prepared_trace_root_endpoints hp hk hw hc hv
  rw [hpre,hpost,hK]
  exact accepted_root_chain hk hw hc hm hv

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
