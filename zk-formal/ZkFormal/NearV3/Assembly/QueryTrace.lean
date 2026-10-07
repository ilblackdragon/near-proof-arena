import ZkFormal.NearV3.Assembly.TransitionQueries
import ZkFormal.NearV3.Assembly.NativeTrace

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def queryTransition (s : ImplicitStepV3) : Transition :=
  { s.witness with values := (nativeQueryStore s.witness.values s.root [keyDelayedIdx,keyBwState] s.post) }

def queryPairs (steps : List ImplicitStepV3) : List (Blk × Transition) :=
  steps.map (fun s => (s.block,queryTransition s))

theorem unfoldStep_query {k : WalkD0} {b : Blk} {t : Transition} {root : Bytes} {post : PTrie}
    (hr : root.length = 32) (hp : post.hashOf.length = 32)
    (h : applyMissingChunk prims (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)
      (partialTrie t.values root [keyDelayedIdx,keyBwState]) = .ok post)
    (acc : List (PTrie × PTrie)) :
    unfoldStep k (b,queryTransition ⟨b,t,root,partialTrie t.values root [keyDelayedIdx,keyBwState],post⟩)
      (acc,root) = unfoldStep k (b,t) (acc,root) := by
  unfold unfoldStep queryTransition
  simp only [nativeQueryStore_pre _ _ _ _ hr,h,bind,Except.bind,pure,Except.pure,
    nativeQueryStore_post _ _ _ _ hr hp]

theorem ImplicitTraceValid.query_unfold {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) (hr : root.length = 32)
    (hp : ∀ s ∈ steps, s.post.hashOf.length = 32) (acc : List (PTrie × PTrie)) :
    forIn (queryPairs steps) (acc,root) (unfoldStep k) =
      forIn pairs (acc,root) (unfoldStep k) := by
  induction hv generalizing acc with
  | nil => rfl
  | cons root b t rest steps post last run checked tail ih =>
    have hpost : post.hashOf.length = 32 := hp ⟨b,t,root,partialTrie t.values root [keyDelayedIdx,keyBwState],post⟩ (by simp)
    have htail : ∀ s ∈ steps, s.post.hashOf.length = 32 := fun s hs => hp s (by simp [hs])
    simp only [queryPairs,List.map_cons,List.forIn_cons]
    rw [unfoldStep_query hr hpost run acc]
    simp only [unfoldStep,run,bind,Except.bind,pure,Except.pure]
    exact ih hpost htail _

theorem queryTransition_size (s : ImplicitStepV3) (hr : s.root.length = 32) :
    (V3.encodeTransition (queryTransition s)).length ≤ (V3.encodeTransition s.witness).length := by
  apply encodeTransition_size_mono (a := queryTransition s) (b := s.witness) (Nat.le_refl _) (Nat.le_refl _)
  exact nativeQueryStore_cost _ _ _ _ hr

theorem ImplicitTraceValid.query_sizes {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) :
    Aligned (fun a b => (V3.encodeTransition a).length ≤ (V3.encodeTransition b).length)
      (steps.map queryTransition) (pairs.map Prod.snd) := by
  induction hv with
  | nil => exact .nil
  | cons root b t rest steps post last run checked tail ih =>
    exact .cons (queryTransition_size _ (implicit_run_root_length run)) ih

theorem queryPairs_zip (steps : List ImplicitStepV3) :
    queryPairs steps = (steps.map ImplicitStepV3.block).zip (steps.map queryTransition) := by
  induction steps with
  | nil => rfl
  | cons s ss ih => simpa only [queryPairs,List.map_cons,List.zip_cons_cons] using congrArg (List.cons (s.block,queryTransition s)) ih

private theorem map_fst_zip_eq {α β : Type} (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.zip_cons_cons,List.map_cons]; rw [ih ys (by simpa using h)]

theorem ImplicitTraceValid.queryPairs_eq {k root steps last} {blocks : List Blk} {ts : List Transition}
    (hv : ImplicitTraceValid k root (blocks.zip ts) steps last) (hl : blocks.length = ts.length) :
    queryPairs steps = blocks.zip (steps.map queryTransition) := by
  rw [queryPairs_zip]
  have hp := congrArg (List.map Prod.fst) hv.pairs
  simp only [List.map_map,Function.comp_def] at hp
  rw [map_fst_zip_eq blocks ts hl] at hp
  rw [hp]

theorem map_snd_zip_eq {α β : Type} (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.zip_cons_cons,List.map_cons]; rw [ih ys (by simpa using h)]

theorem ImplicitTraceValid.witnesses_eq {k root steps last} {blocks : List Blk} {ts : List Transition}
    (hv : ImplicitTraceValid k root (blocks.zip ts) steps last) (hl : blocks.length = ts.length) :
    steps.map ImplicitStepV3.witness = ts := by
  have hp := congrArg (List.map Prod.snd) hv.pairs
  simp only [List.map_map,Function.comp_def] at hp
  rw [map_snd_zip_eq blocks ts hl] at hp
  exact hp

end ZkFormal.NearV3.Assembly
