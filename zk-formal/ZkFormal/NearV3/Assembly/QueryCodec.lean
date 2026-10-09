import ZkFormal.NearV3.Assembly.QueryWitness
import ZkFormal.NearV3.Assembly.NativeShape

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

set_option maxHeartbeats 2000000 in
theorem queryWitness_shape {raw : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hd : decodeStateWitness raw = .ok w) (hb : raw.length ≤ 8388608) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.implicitBlks.length = w.implicit.length) :
    V3.D0Shape (queryWitness k w m steps) := by
  have hs := queryWitness_size hd hm hv hl
  have hfull : (V3.encodeSW (queryWitness k w m steps)).length ≤ 8388608 := by omega
  have hhash := decodeStateWitness_transition_hashes hd
  have himp : ∀ t ∈ (queryWitness k w m steps).implicit, TransitionHashes t := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    have hw : s.witness ∈ w.implicit := by
      rw [←hv.witnesses_eq hl]
      exact List.mem_map.mpr ⟨s,hs,rfl⟩
    exact hhash.2 s.witness hw
  have ht := encodeSW_transition_shapes hfull hhash.1 himp
  have horig := decodeStateWitness_shape hd hb
  have hlen : steps.length = w.implicit.length := by
    have he := congrArg List.length (hv.witnesses_eq hl)
    simpa only [List.length_map] using he
  have hbound : lenT (V3.encodeSW (queryWitness k w m steps)) ≤ MAX_WITNESS := by
    rw [ReexecV3D0.lenT_eq]
    unfold MAX_WITNESS
    omega
  simp only [V3.D0Shape,V3.D0Shape.wf,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at horig ⊢
  rcases horig with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hepoch,hinner⟩,hinnerwf⟩,hmain⟩,hecount⟩,heall⟩,hah⟩,hnt⟩,hicount⟩,hiall⟩,hnnew⟩,hsize⟩
  repeat' apply And.intro
  all_goals first
    | exact ht.1
    | exact ht.2
    | exact hbound
    | simpa only [queryWitness,List.length_map,hlen] using hepoch
    | simpa only [queryWitness,List.length_map,hlen] using hinner
    | simpa only [queryWitness,List.length_map,hlen] using hinnerwf
    | simpa only [queryWitness,List.length_map,hlen] using hecount
    | simpa only [queryWitness,List.length_map,hlen] using heall
    | simpa only [queryWitness,List.length_map,hlen] using hah
    | simpa only [queryWitness,List.length_map,hlen] using hnt
    | simpa only [queryWitness,List.length_map,hlen] using hicount
    | simpa only [queryWitness,List.length_map,hlen] using hnnew

set_option maxHeartbeats 2000000 in
theorem queryWitness_decode {raw : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hd : decodeStateWitness raw = .ok w) (hb : raw.length ≤ 8388608) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.implicitBlks.length = w.implicit.length) :
    decodeW (V3.encodeWitnessFile (queryWitness k w m steps)) = .ok (queryWitness k w m steps) := by
  have hs := queryWitness_shape hd hb hm hv hl
  unfold decodeW
  rw [V3.decodeWitnessFile_encode _ hs]
  exact V3.decodeStateWitness_encode _ hs

end ZkFormal.NearV3.Assembly
