import ZkFormal.NearV3.Assembly.DecodedShapes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pPublicKey_shape {label : String} {bs rest : Bytes} {k : PublicKey}
    (h : pPublicKey label bs = .ok (k,rest)) : V3.pkWf3 k = true := by
  unfold pPublicKey at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp_all only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq]
    obtain ⟨rfl,rfl⟩ := h
    have hn := (ReexecV3D0.pTake_split (by assumption)).2
    simp_all [V3.pkWf3]

theorem pPublicKey_bytes {label : String} {bs rest : Bytes} {k : PublicKey}
    (h : pPublicKey label bs = .ok (k,rest)) : bs = k.encode ++ rest := by
  unfold pPublicKey at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp_all only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq]
    obtain ⟨rfl,rfl⟩ := h
    have ht := (ReexecV3D0.lift_readLE_inv (n := 1) (by assumption)).1
    have hd := (ReexecV3D0.pTake_split (by assumption)).1
    rw [ht,hd,←List.append_assoc]
    rfl

theorem pAccountId_bytes {label : String} {bs rest a : Bytes}
    (h : pAccountId label bs = .ok (a,rest)) : bs = borshBytes a ++ rest := by
  unfold pAccountId at h
  obtain ⟨⟨a',r⟩,ha,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h; exact (ReexecV3D0.pBytes_inv ha).1
  · cases h

theorem pCongestion_shape {bs rest : Bytes} {c : Congestion}
    (h : pCongestion bs = .ok (c,rest)) : V3.congestionWf c = true := by
  unfold pCongestion at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [V3.congestionWf,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨⟨V3.pU128_lt (by assumption),V3.pU128_lt (by assumption)⟩,
      (ReexecV3D0.lift_readLE_inv (n := 8) (by assumption)).2⟩,
      (ReexecV3D0.lift_readLE_inv (n := 2) (by assumption)).2⟩

theorem pBwRequest_shape {bs rest : Bytes} {q : BwRequest}
    (h : pBwRequest bs = .ok (q,rest)) : V3.bwRequestWf q = true := by
  unfold pBwRequest at h
  obtain ⟨⟨s,r⟩,hs,h⟩ := bind_ok h
  obtain ⟨⟨b,r'⟩,hb,h⟩ := bind_ok h
  cases h
  simp only [V3.bwRequestWf,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  exact ⟨(ReexecV3D0.lift_readLE_inv (n := 2) hs).2,(ReexecV3D0.pTake_split hb).2⟩

theorem pBwRequests_shape {bs rest : Bytes} {qs : List BwRequest}
    (h : pBwRequests bs = .ok (qs,rest)) :
    qs.length < 4294967296 ∧ qs.all V3.bwRequestWf = true := by
  unfold pBwRequests at h
  obtain ⟨⟨tag,r⟩,_,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  · exact ⟨pVec_length_bound h,List.all_eq_true.mpr
      (pVec_property pBwRequest _ (fun _ _ _ hh => pBwRequest_shape hh) h)⟩

end ZkFormal.NearV3.Assembly
