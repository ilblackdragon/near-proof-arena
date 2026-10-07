import ZkFormal.NearV3.Assembly.ChunkInnerBytes
import ZkFormal.NearV3.Assembly.CodecSize

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pChunkHeader_shape {bs rest ib : Bytes} {ci : ChunkInner}
    (h : pChunkHeader bs = .ok ((ib,ci),rest)) : V3.innerWf ci = true := by
  unfold pChunkHeader at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals cases h; exact pChunkInner_shape (by assumption)

set_option maxHeartbeats 2000000 in
theorem decodeStateWitness_shape {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) (hb : bs.length ≤ 8388608) : V3.D0Shape w := by
  have hsize := decodeStateWitness_encodeSW_size h
  have hbound : lenT (V3.encodeSW w) ≤ MAX_WITNESS := by
    rw [ReexecV3D0.lenT_eq]
    unfold MAX_WITNESS
    omega
  unfold decodeStateWitness at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have he := pChunkHeader_inner_bytes (by assumption)
    have hi := pChunkHeader_shape (by assumption)
    have hent := pVec_property pEntry (fun e => V3.entryWf e = true)
      (fun _ _ _ hh => pEntry_wf hh) (by assumption)
    have himp := pVec_property pTransition (fun t => V3.transitionWf t = true)
      (fun _ _ _ hh => pTransition_wf hh) (by assumption)
    simp only [V3.D0Shape,V3.D0Shape.wf,V3.h32,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    repeat' apply And.intro
    all_goals first
      | exact V3.pHash_len (by assumption)
      | exact he
      | exact hi
      | exact pTransition_wf (by assumption)
      | exact pVec_length_bound (by assumption)
      | exact List.all_eq_true.mpr hent
      | exact List.all_eq_true.mpr himp
      | exact hbound
      | grind only

end ZkFormal.NearV3.Assembly
