import ZkFormal.NearV3.Assembly.HeaderBytes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pChunkInner_bytes {bs rest : Bytes} {ci : ChunkInner}
    (h : pChunkInner bs = .ok (ci,rest)) : bs = V3.encodeChunkInner ci ++ rest := by
  unfold pChunkInner at h
  obtain ⟨⟨tag,b0⟩,ht,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  ·
    obtain ⟨⟨pbh,b1⟩,h1,h⟩ := bind_ok h
    obtain ⟨⟨psr,b2⟩,h2,h⟩ := bind_ok h
    obtain ⟨⟨por,b3⟩,h3,h⟩ := bind_ok h
    obtain ⟨⟨emr,b4⟩,h4,h⟩ := bind_ok h
    obtain ⟨⟨el,b5⟩,h5,h⟩ := bind_ok h
    obtain ⟨⟨hc,b6⟩,h6,h⟩ := bind_ok h
    obtain ⟨⟨sid,b7⟩,h7,h⟩ := bind_ok h
    obtain ⟨⟨pgu,b8⟩,h8,h⟩ := bind_ok h
    obtain ⟨⟨gl,b9⟩,h9,h⟩ := bind_ok h
    obtain ⟨⟨pbb,b10⟩,h10,h⟩ := bind_ok h
    obtain ⟨⟨porr,b11⟩,h11,h⟩ := bind_ok h
    obtain ⟨⟨txr,b12⟩,h12,h⟩ := bind_ok h
    obtain ⟨⟨props,b13⟩,h13,h⟩ := bind_ok h
    obtain ⟨⟨cong,b14⟩,h14,h⟩ := bind_ok h
    obtain ⟨⟨bw,b15⟩,h15,h⟩ := bind_ok h
    split at h
    all_goals
      obtain ⟨⟨sp,last⟩,hsp,h⟩ := bind_ok h
      simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      dsimp only at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hsp
      have he : b15 = (if tag == 4 then encOpt (fun b => b) sp else []) ++ last := by
        first
        | simpa only [*,ite_true] using pOption_bytes pTrieSplit (fun b => b) (fun _ _ _ hh => pTrieSplit_bytes hh) hsp
        | simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at hsp
          obtain ⟨rfl,rfl⟩ := hsp
          simp only [*,ite_false,Bool.false_eq_true,↓reduceIte,List.nil_append]
      rw [(ReexecV3D0.lift_readLE_inv (n := 1) ht).1]
      rw [pHash_bytes h1]
      rw [pHash_bytes h2]
      rw [pHash_bytes h3]
      rw [pHash_bytes h4]
      rw [(ReexecV3D0.lift_readLE_inv (n := 8) h5).1]
      rw [(ReexecV3D0.lift_readLE_inv (n := 8) h6).1]
      rw [(ReexecV3D0.lift_readLE_inv (n := 8) h7).1]
      rw [(ReexecV3D0.lift_readLE_inv (n := 8) h8).1]
      rw [(ReexecV3D0.lift_readLE_inv (n := 8) h9).1]
      rw [(ReexecV3D0.lift_readLE_inv (n := 16) h10).1]
      rw [pHash_bytes h11]
      rw [pHash_bytes h12]
      rw [pVec_bytes pValidatorStake (fun b => b) (fun _ _ _ hh => pValidatorStake_bytes hh) h13]
      rw [pCongestion_bytes h14]
      rw [pBwRequests_bytes h15]
      rw [he]
      simp only [V3.encodeChunkInner,List.append_assoc]
      rfl

theorem pChunkHeader_inner_bytes {bs rest ib : Bytes} {ci : ChunkInner}
    (h : pChunkHeader bs = .ok ((ib,ci),rest)) : ib = V3.encodeChunkInner ci := by
  unfold pChunkHeader at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have he := pChunkInner_bytes (by assumption)
    rw [he,ReexecV3D0.consumed_app]

end ZkFormal.NearV3.Assembly
