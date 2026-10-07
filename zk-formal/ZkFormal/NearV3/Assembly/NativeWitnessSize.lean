import ZkFormal.NearV3.Assembly.SourceSemantics
import ZkFormal.NearV3.Assembly.WitnessSize
import ZkFormal.NearV3.Assembly.DecodedTransitions
import ZkFormal.NearV3.Assembly.NativeWitnessFields
import ZkFormal.NearV3.Assembly.HeaderCompose

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def TransitionSizeLE (a b : Transition) : Prop :=
  a.blockHash.length ≤ b.blockHash.length ∧ a.postStateRoot.length ≤ b.postStateRoot.length ∧
    storeCost a.values ≤ storeCost b.values

theorem implicit_views_size (x : ExtV3) (steps : List ImplicitStepV3) (tau : Nat)
    (hv : ImplicitViewsAt x tau steps)
    (hp : ∀ e ∈ steps,
      e.pre = partialTrie e.witness.values e.root [keyDelayedIdx,keyBwState] ∧
      e.post.hashOf = e.witness.postStateRoot ∧ e.witness.blockHash.length = 32) :
    Aligned TransitionSizeLE ((steps.zipIdx tau).map (fun (_,i) => x.transition i))
      (steps.map ImplicitStepV3.witness) := by
  induction steps generalizing tau with
  | nil => exact .nil
  | cons e rest ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    have h0 := hv 0 e rfl
    simp only [Nat.add_zero] at h0
    have he := hp e (by simp)
    apply Aligned.cons
    · change (List.replicate 32 (0 : UInt8)).length ≤ e.witness.blockHash.length ∧
        (x.post tau).length ≤ e.witness.postStateRoot.length ∧
        storeCost (x.store tau) ≤ storeCost e.witness.values
      rw [List.length_replicate,he.2.2,h0.2.2,he.2.1,h0.2.1,he.1]
      exact ⟨Nat.le_refl _,Nat.le_refl _,partialTrie_normalStore_cost _ _ _ h0.1⟩
    · apply ih (tau+1)
      · intro i e hi
        have hh := hv (i+1) e hi
        simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh
      · intro e he
        exact hp e (List.mem_cons_of_mem _ he)

theorem ImplicitTraceValid.post_roots {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) :
    ∀ e ∈ steps, e.post.hashOf = e.witness.postStateRoot := by
  induction h with
  | nil => simp
  | cons root b t rest steps post last hrun hpost htail ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hpost
    · exact ih e he

theorem zipIdx_map_index_eq {α β γ : Type} (f : Nat → γ) (xs : List α) (ys : List β)
    (start : Nat) (h : xs.length = ys.length) :
    (xs.zipIdx start).map (fun (_,i) => f i) = (ys.zipIdx start).map (fun (_,i) => f i) := by
  have hx : (xs.zipIdx start).map (fun (_,i) => f i) = ((xs.zipIdx start).map Prod.snd).map f :=
    (List.map_map ..).symm
  have hy : (ys.zipIdx start).map (fun (_,i) => f i) = ((ys.zipIdx start).map Prod.snd).map f :=
    (List.map_map ..).symm
  rw [hx,hy,List.zipIdx_map_snd,List.zipIdx_map_snd,h]

theorem nativeExecutionViews_witness_size {k : WalkD0} {w : StateWitness} {raw : Bytes}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hd : decodeStateWitness raw = .ok w) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hcount : w.implicit.length = k.implicitBlks.length)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P)
    (hepoch : w.epochId = k.c.epochId) (hinner : w.innerBytes = k.c.chunkInner)
    (hhash : sha256 (encodeReceipts (appliedReceipts k w)) = w.appliedReceiptsHash) :
    (V3.encodeSW (stateWitnessOfV3 k (nativeExecutionViews k w m steps))).length ≤ raw.length := by
  let x := nativeExecutionViews k w m steps
  have hlen : steps.length = k.implicitBlks.length := by
    rw [hv.length,List.length_zip,hcount,Nat.min_self]
  have hwitness : steps.map ImplicitStepV3.witness = w.implicit := by
    have hh := congrArg (List.map Prod.snd) hv.pairs
    simp only [List.map_map,Function.comp_def,List.map_snd_zip (by omega : w.implicit.length ≤ k.implicitBlks.length)] at hh
    exact hh
  have hvx : ImplicitViewsAt x 1 steps := runtimePairs_implicit_views hv m hf hc
  have hashes := decodeStateWitness_transition_hashes hd
  have hi := implicit_views_size x steps 1 hvx (by
    intro e he
    refine ⟨(hv.input_facts e he).1,hv.post_roots e he,?_⟩
    apply (hashes.2 e.witness ?_).1
    rw [← hwitness]
    exact List.mem_map.mpr ⟨e,he,rfl⟩)
  have hil : (stateWitnessOfV3 k x).implicit =
      (steps.zipIdx 1).map (fun (_,i) => x.transition i) := by
    unfold stateWitnessOfV3
    rw [List.zipIdx_succ,List.map_map]
    exact zipIdx_map_index_eq (fun i => x.transition (i+1)) k.implicitBlks steps 0 hlen.symm
  have hi' : Aligned TransitionSizeLE (stateWitnessOfV3 k x).implicit w.implicit := by
    rwa [←hil,hwitness] at hi
  have hmain : TransitionSizeLE (x.transition 0) w.main := by
    have hs : x.store 0 = normalStore m.pre := by
      change (traceStoreViews (runtimePairs m steps)).store 0 = _
      rw [traceStoreViews_store,runtimePairs_pre]
      exact forestStoreViews_store hf hc rfl
    have hp : x.post 0 = m.result.trie.hashOf := traceStoreViews_post
      (show (runtimePairs m steps)[0]? = some (m.pre,m.result.trie) from rfl)
    change (List.replicate 32 (0 : UInt8)).length ≤ w.main.blockHash.length ∧
      (x.post 0).length ≤ w.main.postStateRoot.length ∧ storeCost (x.store 0) ≤ storeCost w.main.values
    rw [List.length_replicate,hashes.1.1,hp,hm.postRoot,hs,hm.pre]
    exact ⟨Nat.le_refl _,Nat.le_refl _,partialTrie_normalStore_cost _ _ _ hm.root_length⟩
  have hsize := decodeStateWitness_replace_stores_size hd (x.transition 0)
    (stateWitnessOfV3 k x).implicit hmain hi'
  have he := nativeExecutionViews_entries (k := k) (m := m) (steps := steps) hd
  have ha : x.applied = appliedReceipts k w := executionViews_applied hd
  change (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ raw.length
  have hencode : V3.encodeSW (stateWitnessOfV3 k x) =
      V3.encodeSW {w with main := x.transition 0, implicit := (stateWitnessOfV3 k x).implicit} := by
    have he' : (stateWitnessOfV3 k x).entries = w.entries := he
    simp only [V3.encodeSW]
    rw [he']
    simp only [stateWitnessOfV3,ha,hhash,hepoch,hinner]
  rw [hencode]
  exact hsize

/-- Constructed source, execution, header, and full encoded-size fields directly
from accepted native bytes. Preparation/shape/amendment and AIR obligations remain. -/
theorem checkD0a_constructed_fields {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ()) :
    ∃ m steps last, let x := nativeExecutionViews k w m steps
      SourceSemanticsV3 k x ∧ m.Valid k x ∧
      ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      NativeHeaderV3 k m last ∧ (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608 := by
  obtain ⟨m,steps,last,hm,ht,hv,hlen,_,hcap,hf⟩ := checkD0a_native_trace hk hw h
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,_⟩ := checkD0_native_steps hk hw hc
  obtain ⟨raw,codes,hfile,hd,hraw,hepoch,hinner,hhash⟩ := checkD0_witness_fields hk hw hc
  have hsize := nativeExecutionViews_witness_size hd hm hv hcount hf hcap hepoch hinner hhash
  have hi := executionViews_implicit (w := w)
    (dictionary := sourceDictionarySeeds (sourceKeysV3 k) w.entries) hv hf hcap
  rw [List.map_fst_zip (by omega : k.implicitBlks.length ≤ w.implicit.length)] at hi
  exact ⟨m,steps,last,checkD0a_source_semantics hk hw h m steps,
    executionViews_main hm hd hf hcap,hi,checkD0_header_of_trace hk hw hc hm ht,
    Nat.le_trans hsize hraw⟩

end ZkFormal.NearV3.Assembly
