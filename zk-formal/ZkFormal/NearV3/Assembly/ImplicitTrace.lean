import ZkFormal.NearV3.Assembly.ImplicitComplete

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

structure ImplicitStepV3 where
  block : Blk
  witness : Transition
  root : Bytes
  pre : PTrie
  post : PTrie

/-- Executable chronological trace of the native implicit transition loop. -/
def traceImplicit (k : WalkD0) : Bytes → List (Blk × Transition) →
    Except String (List ImplicitStepV3 × Bytes)
  | root, [] => .ok ([], root)
  | root, (b, t) :: rest => do
    let pre := partialTrie t.values root [keyDelayedIdx, keyBwState]
    let post ← applyMissingChunk prims
      (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice) pre
    check (post.hashOf == t.postStateRoot) "invalid: implicit transition post state root"
    let (steps, last) ← traceImplicit k post.hashOf rest
    pure (⟨b, t, root, pre, post⟩ :: steps, last)

/-- Exact native operational trace; no AIR or checker-success field is assumed. -/
inductive ImplicitTraceValid (k : WalkD0) : Bytes → List (Blk × Transition) →
    List ImplicitStepV3 → Bytes → Prop
  | nil (root : Bytes) : ImplicitTraceValid k root [] [] root
  | cons (root : Bytes) (b : Blk) (t : Transition) (rest : List (Blk × Transition))
      (steps : List ImplicitStepV3) (post : PTrie) (last : Bytes)
      (run : applyMissingChunk prims
        (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)
        (partialTrie t.values root [keyDelayedIdx, keyBwState]) = .ok post)
      (rootChecked : post.hashOf = t.postStateRoot)
      (tail : ImplicitTraceValid k post.hashOf rest steps last) :
      ImplicitTraceValid k root ((b,t)::rest)
        (⟨b,t,root,partialTrie t.values root [keyDelayedIdx,keyBwState],post⟩::steps) last

theorem checkedImplicitStep_success {k : WalkD0} {b : Blk} {t : Transition}
    {root : Bytes} {step : ForInStep Bytes}
    (h : checkedImplicitStep k (b,t) root = .ok step) :
    ∃ post, applyMissingChunk prims
      (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)
      (partialTrie t.values root [keyDelayedIdx,keyBwState]) = .ok post ∧
      post.hashOf = t.postStateRoot ∧ step = .yield post.hashOf := by
  unfold checkedImplicitStep at h
  obtain ⟨post, hp, h⟩ := ReexecV3D0.bind_ok' h
  obtain ⟨u, hu, h⟩ := ReexecV3D0.bind_ok' h
  cases h
  exact ⟨post, hp, by cases u; simpa using ReexecV3D0.check_ok hu, rfl⟩

/-- Successful native loop evaluation supplies the executable trace, with every intermediate root. -/
theorem checkedImplicitLoop_trace (k : WalkD0) : ∀ pairs root last,
    forIn pairs root (checkedImplicitStep k) = .ok last →
    ∃ steps, traceImplicit k root pairs = .ok (steps,last) ∧
      ImplicitTraceValid k root pairs steps last
  | [], root, last, h => by cases h; exact ⟨[], rfl, .nil root⟩
  | (b,t)::rest, root, last, h => by
    simp only [List.forIn_cons] at h
    obtain ⟨step, hs, h⟩ := ReexecV3D0.bind_ok' h
    obtain ⟨post, hp, he, rfl⟩ := checkedImplicitStep_success hs
    obtain ⟨steps, ht, hv⟩ := checkedImplicitLoop_trace k rest post.hashOf last h
    refine ⟨_, ?_, .cons root b t rest steps post last hp he hv⟩
    rw [he] at ht
    simp [traceImplicit, hp, he, check, ht, bind, Except.bind, pure, Except.pure]

theorem ImplicitTraceValid.length {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) : steps.length = pairs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simpa using ih

end ZkFormal.NearV3.Assembly
