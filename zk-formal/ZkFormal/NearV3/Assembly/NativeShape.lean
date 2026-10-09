import ZkFormal.NearV3.Assembly.NativeWitnessSize
import ZkFormal.NearV3.Assembly.EncodedShapeBounds

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem walkD0_header_decode {cb : Bytes} {k : WalkD0} (h : walkD0 cb = .ok k) :
    decodeChunkInner k.c.chunkInner = .ok k.H := by
  unfold walkD0 at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals cases h; assumption

theorem decodeChunkInner_shape_bytes {bs : Bytes} {ci : ChunkInner}
    (h : decodeChunkInner bs = .ok ci) : V3.innerWf ci = true ∧ bs = V3.encodeChunkInner ci := by
  unfold decodeChunkInner at h
  obtain ⟨⟨ci',rest⟩,hp,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  · rename_i he
    have he' : rest = [] := by simpa using he
    subst rest
    cases h
    exact ⟨pChunkInner_shape hp,by simpa only [List.append_nil] using pChunkInner_bytes hp⟩

theorem implicit_views_hashes (x : ExtV3) (steps : List ImplicitStepV3) (tau : Nat)
    (hv : ImplicitViewsAt x tau steps)
    (hp : ∀ e ∈ steps, e.post.hashOf.length = 32) :
    ∀ t ∈ (steps.zipIdx tau).map (fun (_,i) => x.transition i), TransitionHashes t := by
  induction steps generalizing tau with
  | nil => simp
  | cons e rest ih =>
    simp only [List.zipIdx_cons,List.map_cons,List.mem_cons]
    intro t ht
    rcases ht with rfl | ht
    · have h0 := (hv 0 e rfl).2.2
      simp only [Nat.add_zero] at h0
      exact ⟨by simp [TransitionHashes,ExtV3.transition],by
        change (x.post tau).length = 32
        rw [h0]
        exact hp e (by simp)⟩
    · apply ih (tau+1) ?_ (fun e he => hp e (List.mem_cons_of_mem _ he)) t ht
      intro i e hi
      have hh := hv (i+1) e hi
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh

/-- The concrete normalized-store constructor retains the unchanged D0Shape. -/
theorem nativeExecutionViews_shape {cb raw : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hd : decodeStateWitness raw = .ok w) (hb : raw.length ≤ 8388608)
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hcount : w.implicit.length = k.implicitBlks.length)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P)
    (hepoch : w.epochId = k.c.epochId)
    (hs : (V3.encodeSW (stateWitnessOfV3 k (nativeExecutionViews k w m steps))).length ≤ 8388608) :
    V3.D0Shape (stateWitnessOfV3 k (nativeExecutionViews k w m steps)) := by
  let x := nativeExecutionViews k w m steps
  change (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608 at hs
  have hlen : steps.length = k.implicitBlks.length := by
    rw [hv.length,List.length_zip,hcount,Nat.min_self]
  have hwitness : steps.map ImplicitStepV3.witness = w.implicit := by
    have hh := congrArg (List.map Prod.snd) hv.pairs
    simp only [List.map_map,Function.comp_def,List.map_snd_zip (by omega : w.implicit.length ≤ k.implicitBlks.length)] at hh
    exact hh
  have hashes := decodeStateWitness_transition_hashes hd
  have hi := implicit_views_hashes x steps 1 (runtimePairs_implicit_views hv m hf hc) (by
    intro e he
    rw [hv.post_roots e he]
    apply (hashes.2 e.witness ?_).2
    rw [←hwitness]
    exact List.mem_map.mpr ⟨e,he,rfl⟩)
  have hil : (stateWitnessOfV3 k x).implicit =
      (steps.zipIdx 1).map (fun (_,i) => x.transition i) := by
    unfold stateWitnessOfV3
    rw [List.zipIdx_succ,List.map_map]
    exact zipIdx_map_index_eq (fun i => x.transition (i+1)) k.implicitBlks steps 0 hlen.symm
  rw [←hil] at hi
  have hmhash : TransitionHashes (stateWitnessOfV3 k x).main := by
    have hp : x.post 0 = m.result.trie.hashOf := traceStoreViews_post
      (show (runtimePairs m steps)[0]? = some (m.pre,m.result.trie) from rfl)
    constructor
    · simp [stateWitnessOfV3,ExtV3.transition]
    · change (x.post 0).length = 32
      rw [hp,hm.postRoot]
      exact hashes.1.2
  have htw := encodeSW_transition_shapes hs hmhash hi
  have horig := decodeStateWitness_shape hd hb
  have hhead := decodeChunkInner_shape_bytes (walkD0_header_decode hk)
  have he : x.dictionary.map DictionaryEntryV3.entry = w.entries :=
    nativeExecutionViews_entries (k := k) (m := m) (steps := steps) hd
  have hbound : lenT (V3.encodeSW (stateWitnessOfV3 k x)) ≤ MAX_WITNESS := by
    rw [ReexecV3D0.lenT_eq]
    unfold MAX_WITNESS
    omega
  simp only [V3.D0Shape,V3.D0Shape.wf,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at horig ⊢
  rcases horig with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hepoch32,hinner⟩,hinnerwf⟩,hmainwf⟩,hecount⟩,heall⟩,hhash⟩,hno⟩,hicount⟩,hiall⟩,hnew⟩,hsize⟩
  have hec : (x.dictionary.map DictionaryEntryV3.entry).length < 4294967296 := by
    rw [he]; exact hecount
  have hea : (x.dictionary.map DictionaryEntryV3.entry).all V3.entryWf = true := by
    rw [he]; exact heall
  repeat' apply And.intro
  all_goals first
    | exact htw.1
    | exact htw.2
    | exact hbound
    | simpa only [stateWitnessOfV3,←hepoch] using hepoch32
    | exact hhead.2
    | exact hhead.1
    | exact hec
    | exact hea
    | simpa only [stateWitnessOfV3_implicit_length,←hcount] using hicount
    | simp only [stateWitnessOfV3,V3.h32,ArenaCore.sha256_length,beq_self_eq_true]

theorem checkD0a_constructed_shape {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ()) :
    ∃ m steps, V3.D0Shape (stateWitnessOfV3 k (nativeExecutionViews k w m steps)) := by
  obtain ⟨m,steps,last,hm,ht,hv,hlen,_,hcap,hf⟩ := checkD0a_native_trace hk hw h
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,_⟩ := checkD0_native_steps hk hw hc
  obtain ⟨raw,codes,hfile,hd,hraw,hepoch,hinner,hhash⟩ := checkD0_witness_fields hk hw hc
  have hsize := nativeExecutionViews_witness_size hd hm hv hcount hf hcap hepoch hinner hhash
  exact ⟨m,steps,nativeExecutionViews_shape hk hd hraw hm hv hcount hf hcap hepoch
    (Nat.le_trans hsize hraw)⟩

end ZkFormal.NearV3.Assembly
