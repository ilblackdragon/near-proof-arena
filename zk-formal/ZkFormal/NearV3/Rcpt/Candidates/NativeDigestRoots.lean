import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionPayloads

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly

theorem newchunk_root_revealed {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs=.ok out) : isNode t=true := by
  cases t <;> try rfl
  simp [applyNewChunk,readKey,PTrie.find,bind,Except.bind] at h

theorem missing_root_revealed {ctx : ApplyCtx} {t post : PTrie}
    (h : applyMissingChunk prims ctx t=.ok post) : isNode t=true := by
  cases t <;> try rfl
  simp [applyMissingChunk,readKey,PTrie.find,bind,Except.bind] at h

theorem implicit_roots_revealed {k : WalkD0} {root last : Bytes}
    {pairs : List (Blk×Transition)} {steps : List ImplicitStepV3}
    (h : ImplicitTraceValid k root pairs steps last) : ∀s∈steps,isNode s.pre=true := by
  induction h with
  | nil=>simp
  | cons root b t rest steps post last hr hp ht ih=>
    intro s hs
    rcases List.mem_cons.mp hs with rfl|hs
    · exact missing_root_revealed hr
    · exact ih s hs

/-- Native prestate roots are revealed because the unchanged execution first
requires a determined delayed-index read; no extra root-domain assumption. -/
theorem replay_roots_revealed {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat×Bytes)) :
    ∀r∈nativeReplayForest m steps oldPost writes,isNode r.pre=true := by
  intro r hr
  simp only [nativeReplayForest,List.mem_cons,List.mem_map] at hr
  rcases hr with rfl|⟨s,hs,rfl⟩
  · exact newchunk_root_revealed hm.run
  · exact implicit_roots_revealed hv s hs

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
