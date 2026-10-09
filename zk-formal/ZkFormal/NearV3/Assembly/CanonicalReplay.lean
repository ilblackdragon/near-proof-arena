import ZkFormal.NearV3.Assembly.NativeShape
import ZkFormal.NearV3.Assembly.Scheduler

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

def bwRead (ws : List Bytes) (root : Bytes) : Option Bytes :=
  ((partialTrie ws root [keyBwState]).find keyBwState).getD none

def bwReadsFrom : Bytes → List Transition → List (Option Bytes)
  | _, [] => []
  | root, t::ts => bwRead t.values root :: bwReadsFrom t.postStateRoot ts

theorem bwReadsFrom_zip (root : Bytes) (ts : List Transition) :
    bwReadsFrom root ts = (ts.zip (root :: ts.map Transition.postStateRoot)).map
      (fun (t,r) => bwRead t.values r) := by
  induction ts generalizing root with
  | nil => rfl
  | cons t ts ih =>
    simpa only [bwReadsFrom,List.map_cons,List.zip_cons_cons] using
      (congrArg (bwRead t.values root :: ·) (ih t.postStateRoot))

theorem reads0f_eq (k : WalkD0) (w : StateWitness) :
    reads0f k w = bwRead w.main.values k.slotB2.prevStateRoot :: bwReadsFrom w.main.postStateRoot w.implicit := by
  rw [bwReadsFrom_zip]
  rfl

theorem schedStep_bw_find {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (h : schedStep prims ctx pre = .ok (post,so)) : pre.find keyBwState ≠ none := by
  obtain ⟨v,_,_,hr,_,_,_,_⟩ := schedStep_complete h
  intro hn
  unfold readKey at hr
  rw [hn] at hr
  cases hr

theorem applyNewChunk_bw_find {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx pre rs = .ok out) : pre.find keyBwState ≠ none := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨post,so⟩,hs,_⟩ := bind_ok h
  exact schedStep_bw_find hs

theorem applyMissingChunk_bw_find {ctx : ApplyCtx} {pre post : PTrie}
    (h : applyMissingChunk prims ctx pre = .ok post) : pre.find keyBwState ≠ none := by
  unfold applyMissingChunk at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨mid,so⟩,hs,_⟩ := bind_ok h
  exact schedStep_bw_find hs

theorem bwRead_normalStore {ws : List Bytes} {root : Bytes} {keys : List (List Nat)}
    (hr : root.length = 32) (hk : (partialTrie ws root keys).find keyBwState ≠ none) :
    bwRead (normalStore (partialTrie ws root keys)) root = bwRead ws root := by
  unfold bwRead
  rw [partialTrie_normalStore_singleton_find ws root keys keyBwState hr hk]

theorem ImplicitTraceValid.bwReads_replay {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) (x : ExtV3) (tau : Nat)
    (hx : ImplicitViewsAt x tau steps) :
    bwReadsFrom root ((steps.zipIdx tau).map (fun (_,i) => x.transition i)) =
      bwReadsFrom root (pairs.map Prod.snd) := by
  induction h generalizing tau with
  | nil => rfl
  | cons root b t rest steps post last hrun hpost htail ih =>
    have h0 := hx 0 _ rfl
    simp only [Nat.add_zero] at h0
    have hb := bwRead_normalStore h0.1 (applyMissingChunk_bw_find hrun)
    have htailx : ImplicitViewsAt x (tau+1) steps := by
      intro i e hi
      have hh := hx (i+1) e hi
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh
    simp only [List.zipIdx_cons,List.map_cons,bwReadsFrom,ExtV3.transition]
    rw [h0.2.1,hb,h0.2.2]
    apply congrArg (bwRead t.values root :: ·)
    simpa only [ExtV3.transition,hpost] using ih (tau+1) htailx

theorem nativeExecutionViews_reads0f {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hcount : w.implicit.length = k.implicitBlks.length)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    reads0f k (stateWitnessOfV3 k (nativeExecutionViews k w m steps)) = reads0f k w := by
  let x := nativeExecutionViews k w m steps
  have hlen : steps.length = k.implicitBlks.length := by
    rw [hv.length,List.length_zip,hcount,Nat.min_self]
  have hvx : ImplicitViewsAt x 1 steps := runtimePairs_implicit_views hv m hf hc
  have hi := hv.bwReads_replay x 1 hvx
  rw [List.map_snd_zip (by omega : w.implicit.length ≤ k.implicitBlks.length)] at hi
  have hil : (stateWitnessOfV3 k x).implicit =
      (steps.zipIdx 1).map (fun (_,i) => x.transition i) := by
    unfold stateWitnessOfV3
    rw [List.zipIdx_succ,List.map_map]
    exact zipIdx_map_index_eq (fun i => x.transition (i+1)) k.implicitBlks steps 0 hlen.symm
  have hstore : x.store 0 = normalStore m.pre := by
    change (traceStoreViews (runtimePairs m steps)).store 0 = _
    rw [traceStoreViews_store,runtimePairs_pre]
    exact forestStoreViews_store hf hc rfl
  have hpost : x.post 0 = m.result.trie.hashOf := traceStoreViews_post
    (show (runtimePairs m steps)[0]? = some (m.pre,m.result.trie) from rfl)
  have hmain : bwRead (x.store 0) k.slotB2.prevStateRoot = bwRead w.main.values k.slotB2.prevStateRoot := by
    rw [hstore,hm.pre]
    apply bwRead_normalStore hm.root_length
    rw [←hm.pre]
    exact applyNewChunk_bw_find hm.run
  rw [reads0f_eq,reads0f_eq]
  change bwRead (x.store 0) k.slotB2.prevStateRoot ::
      bwReadsFrom (x.post 0) (stateWitnessOfV3 k x).implicit = _
  rw [hmain,hpost,hil,hi,hm.postRoot]

theorem checkD0a_native_canonical {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hcount : w.implicit.length = k.implicitBlks.length)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    (reads0f k (stateWitnessOfV3 k (nativeExecutionViews k w m steps))).all (canonical0f k.L) = true := by
  rw [nativeExecutionViews_reads0f hm hv hcount hf hc]
  have hr := (relD0a_iff B cb wb).mpr h
  simpa only [canon0f,hk,hw] using hr.2.2.2.1

end ZkFormal.NearV3.Assembly
