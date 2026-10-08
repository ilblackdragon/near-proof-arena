import ZkFormal.NearV3.Candidates.NativePostBytes
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedOrigins

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- The original initialized forest, with actual postpayload updates, has full
NodeOk from acceptance. No separately supplied provider-wf witness is required. -/
theorem native_window_provider_ok {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (u : Inputs) : NodeOk (records u
      (initializeList 0 (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre)))) := by
  have hn:=(Candidates.NativeExecutionUsage.inputs hk hw hc (by decide) hm hv).1
  exact Candidates.PostNodeLocal.node_ok u _ hn

/-- Both serializations remain bytes after updating the same old records. -/
theorem native_window_provider_bytes (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (u : Inputs) (s : NodeS3)
    (hs : s∈records u (initializeList 0 (forestNodes 0 0 0 ts))) :
    ∀post x,x∈s.v.ser post→x<256 := by
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hs
  obtain ⟨n,_,b,hb,rfl⟩:=initializeList_member _ 0 a ha
  intro post
  change ∀x,x∈(node u b.v).ser post→x<256
  cases post with
  | false => rw [node_pre]; exact Candidates.NativePostBytes.forest_bytes ts hw false b (List.mem_of_getElem? hb)
  | true =>
    exact Candidates.PostNodeBytes.node_bytes u b.v (Candidates.NativePostBytes.forest_bytes ts hw true b (List.mem_of_getElem? hb))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
