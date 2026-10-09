import ZkFormal.NearV3.Assembly.QueryCodec

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

set_option maxHeartbeats 2000000 in
/-- Accepted native input has a concretely encodable targeted-store witness with
unchanged unfolded cost and no larger raw encoding. AIR allocation is separate. -/
theorem checkD0a_query_witness {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ()) :
    ∃ m steps, let q := queryWitness k w m steps
      V3.D0Shape q ∧ (V3.encodeSW q).length ≤ 8388608 ∧
      decodeW (V3.encodeWitnessFile q) = .ok q ∧
      unfoldBytes cb (V3.encodeWitnessFile q) = unfoldBytes cb wb ∧
      unfoldBytes cb (V3.encodeWitnessFile q) ≤ B := by
  obtain ⟨m,steps,last,hm,ht,hv,hlen,_,hcap,hf⟩ := checkD0a_native_trace hk hw h
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,_⟩ := checkD0_native_steps hk hw hc
  obtain ⟨raw,codes,hfile,hd,hraw,hepoch,hinner,hhash⟩ := checkD0_witness_fields hk hw hc
  have hl : k.implicitBlks.length = w.implicit.length := hcount.symm
  have hhashes := decodeStateWitness_transition_hashes hd
  have hr : m.result.trie.hashOf.length = 32 := by rw [hm.postRoot]; exact hhashes.1.2
  have hp : ∀ s ∈ steps, s.post.hashOf.length = 32 := by
    intro s hs
    rw [hv.post_roots s hs]
    apply (hhashes.2 s.witness ?_).2
    rw [←hv.witnesses_eq hl]
    exact List.mem_map.mpr ⟨s,hs,rfl⟩
  have hshape := queryWitness_shape hd hraw hm hv hl
  have hsize := queryWitness_size hd hm hv hl
  have hdecode := queryWitness_decode hd hraw hm hv hl
  have heq := queryWitness_unfoldBytes hk hw hdecode hm hv hl hr hp
  have hold : unfoldBytes cb wb ≤ B := by
    have hh := (relD0a_iff B cb wb).mpr h
    simpa only [a7,decide_eq_true_eq] using hh.2.2.2.2.1
  exact ⟨m,steps,hshape,by omega,hdecode,heq,by rw [heq]; exact hold⟩

end ZkFormal.NearV3.Assembly
