import ZkFormal.NearV3.Assembly.QueryTrace

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def queryWitness (k : WalkD0) (w : StateWitness) (m : MainExecutionV3)
    (steps : List ImplicitStepV3) : StateWitness :=
  { w with
    main := { w.main with values := (nativeQueryStore w.main.values k.slotB2.prevStateRoot
      (mainKeys (appliedReceipts k w) m.bufferedShards) m.result.trie) }
    implicit := steps.map queryTransition }

theorem queryWitness_receipts (k : WalkD0) (w : StateWitness) (m : MainExecutionV3)
    (steps : List ImplicitStepV3) : appliedReceipts k (queryWitness k w m steps) = appliedReceipts k w := rfl

theorem queryWitness_tries {cb old fresh : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW old = .ok w)
    (hn : decodeW fresh = .ok (queryWitness k w m steps))
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.implicitBlks.length = w.implicit.length)
    (hr : m.result.trie.hashOf.length = 32)
    (hp : ∀ s ∈ steps, s.post.hashOf.length = 32) :
    triesD0 cb fresh = triesD0 cb old := by
  have run := hm.run
  rw [hm.pre] at run
  have buffered := nativeQueryStore_buffered hm.root_length run
  obtain ⟨v,hfind,hparse⟩ := hm.buffered
  have hloop := hv.query_unfold hr hp
  rw [hv.queryPairs_eq hl] at hloop
  unfold ZkFormal.NearV3.Assembly.unfoldStep at hloop
  dsimp only at hloop
  simp only [bind,Except.bind,pure,Except.pure] at hloop
  unfold triesD0
  simp only [hk,hw,hn,queryWitness_receipts,bind,Except.bind,hm.block,hm.previous,pure,Except.pure]
  change _ = _
  simp only [queryWitness]
  rw [buffered]
  simp only [hfind,hparse,bind,Except.bind]
  rw [nativeQueryStore_pre _ _ _ _ hm.root_length]
  unfold MainExecutionV3.ctx at run
  simp only [run,bind,Except.bind,nativeQueryStore_post _ _ _ _ hm.root_length hr,hloop]

theorem queryWitness_size {raw : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hd : decodeStateWitness raw = .ok w) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.implicitBlks.length = w.implicit.length) :
    (V3.encodeSW (queryWitness k w m steps)).length ≤ raw.length := by
  have hmain := encodeTransition_size_mono
    (a := (queryWitness k w m steps).main) (b := w.main)
    (Nat.le_refl _) (Nat.le_refl _)
    (nativeQueryStore_cost _ _ _ _ hm.root_length)
  have hi := hv.query_sizes
  rw [map_snd_zip_eq _ _ hl] at hi
  have hlist := encList_size_mono V3.encodeTransition hi
  have hbase := decodeStateWitness_encodeSW_size hd
  simp only [V3.encodeSW,queryWitness,List.length_append] at *
  omega

theorem queryWitness_unfoldBytes {cb old fresh : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW old = .ok w)
    (hn : decodeW fresh = .ok (queryWitness k w m steps))
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.implicitBlks.length = w.implicit.length)
    (hr : m.result.trie.hashOf.length = 32)
    (hp : ∀ s ∈ steps, s.post.hashOf.length = 32) :
    unfoldBytes cb fresh = unfoldBytes cb old := by
  unfold unfoldBytes
  rw [queryWitness_tries hk hw hn hm hv hl hr hp]

end ZkFormal.NearV3.Assembly
