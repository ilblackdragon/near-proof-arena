import ZkFormal.NearV3.Assembly.NativeHeader
import ZkFormal.NearV3.Assembly.NativeTrace

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem checkD0_header_of_trace {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (ht : traceImplicit k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) = .ok (steps,last)) :
    NativeHeaderV3 k m last := by
  obtain ⟨n,final,hn,hi,_,_,hh⟩ := checkD0_native_header hk hw h
  have he := hm.unique hn
  subst n
  obtain ⟨other,ho,_⟩ := checkedImplicitLoop_trace k _ _ _ hi
  rw [ht] at ho
  have he := congrArg Prod.snd (Except.ok.inj ho)
  change last = final at he
  exact he.symm ▸ hh

/-- Bind the native comparisons to a concrete preparation body. -/
theorem NativeHeaderV3.prepared {k : WalkD0} {m : MainExecutionV3} {last : Bytes}
    (h : NativeHeaderV3 k m last) (hint : Hint) (p : Prep)
    (hb : hint.body = u32 0 ++ encodeReceipts m.result.outgoing)
    (hp : p.body = hint.body) : HeaderSemanticsV3 k hint p m last := by
  exact ⟨h.stateRoot,h.outcomeRoot,h.proposals,h.gasLimit,h.gasUsed,h.tokensBurnt,
    h.outgoingRoot,h.congestion,h.bandwidthRequests,h.split,h.txRoot,hb,hp,hb ▸ h.encoded⟩

end ZkFormal.NearV3.Assembly
