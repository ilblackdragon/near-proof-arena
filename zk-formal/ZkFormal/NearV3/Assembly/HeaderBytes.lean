import ZkFormal.NearV3.Assembly.ChunkInnerShape

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pHash_bytes {label : String} {bs rest hsh : Bytes}
    (h : pHash label bs = .ok (hsh,rest)) : bs = hsh ++ rest := by
  unfold pHash NearSpecV3.lift at h
  split at h
  · cases h
    exact (ReexecV3D0.takeN_split (by assumption)).1
  · cases h

theorem pValidatorStake_bytes {bs rest v : Bytes}
    (h : pValidatorStake bs = .ok (v,rest)) : bs = v ++ rest := by
  obtain ⟨pre,hpre,_⟩ := ReexecV3D0.cfk ReexecV3D0.cf_pValidatorStake h
  have hv : v = consumed bs rest := by
    unfold pValidatorStake at h
    repeat' (first
      | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
      | (split at h)
      | (dsimp only at h))
    all_goals try (cases h; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals cases h; rfl
  rw [hv,hpre,ReexecV3D0.consumed_app]

theorem pTrieSplit_bytes {bs rest v : Bytes}
    (h : pTrieSplit bs = .ok (v,rest)) : bs = v ++ rest := by
  obtain ⟨pre,hpre,_⟩ := ReexecV3D0.cfk ReexecV3D0.cf_pTrieSplit h
  have hv : v = consumed bs rest := by
    unfold pTrieSplit at h
    repeat' (first
      | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
      | (dsimp only at h))
    cases h; rfl
  rw [hv,hpre,ReexecV3D0.consumed_app]

theorem pMany_bytes {α : Type} (p : P α) (enc : α → Bytes)
    (hp : ∀ bs a rest, p bs = .ok (a,rest) → bs = enc a ++ rest) :
    ∀ n {bs rest : Bytes} {xs : List α}, pMany p n bs = .ok (xs,rest) →
      bs = concatAll (xs.map enc) ++ rest
  | 0, _, _, _, h => by cases h; rfl
  | n+1, _, _, _, h => by
    unfold pMany at h
    obtain ⟨⟨a,r⟩,ha,h⟩ := bind_ok h
    obtain ⟨⟨xs,r'⟩,hs,h⟩ := bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    have hxs := pMany_bytes p enc hp n hs
    rw [hp _ _ _ ha,hxs]
    simp only [List.map_cons,concatAll,List.append_assoc]

theorem pVec_bytes {α : Type} (p : P α) (enc : α → Bytes)
    (hp : ∀ bs a rest, p bs = .ok (a,rest) → bs = enc a ++ rest)
    {label : String} {bs rest : Bytes} {xs : List α}
    (h : pVec label p bs = .ok (xs,rest)) : bs = encList enc xs ++ rest := by
  unfold pVec at h
  obtain ⟨⟨n,r⟩,hn,h⟩ := bind_ok h
  rw [(ReexecV3D0.lift_readLE_inv (n := 4) hn).1,pMany_bytes p enc hp n h]
  simp only [encList,pMany_length p n h,List.append_assoc]
  rfl

theorem pOption_bytes {α : Type} (p : P α) (enc : α → Bytes)
    (hp : ∀ bs a rest, p bs = .ok (a,rest) → bs = enc a ++ rest)
    {label : String} {bs rest : Bytes} {a : Option α}
    (h : pOption label p bs = .ok (a,rest)) : bs = encOpt enc a ++ rest := by
  unfold pOption at h
  obtain ⟨⟨tag,r⟩,ht,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
    exact (ReexecV3D0.lift_readLE_inv (n := 1) ht).1
  · obtain ⟨⟨v,r'⟩,hv,h⟩ := bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rw [(ReexecV3D0.lift_readLE_inv (n := 1) ht).1,hp _ _ _ hv]
    simp only [encOpt,List.append_assoc]
    rfl
  · cases h

theorem pCongestion_bytes {bs rest : Bytes} {c : Congestion}
    (h : pCongestion bs = .ok (c,rest)) : bs = V3.encodeCongestion c ++ rest := by
  unfold pCongestion at h
  obtain ⟨⟨tag,b1⟩,ht,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  · rename_i htag
    have ht0 : tag = 0 := by simp only [bne_iff_ne] at htag; omega
    subst tag
    obtain ⟨⟨d,b2⟩,hd,h⟩ := bind_ok h
    obtain ⟨⟨b,b3⟩,hb,h⟩ := bind_ok h
    obtain ⟨⟨r,b4⟩,hr,h⟩ := bind_ok h
    obtain ⟨⟨a,b5⟩,ha,h⟩ := bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    dsimp only at hb hr ha
    rw [(ReexecV3D0.lift_readLE_inv (n := 1) ht).1,
      (ReexecV3D0.lift_readLE_inv (n := 16) hd).1,
      (ReexecV3D0.lift_readLE_inv (n := 16) hb).1,
      (ReexecV3D0.lift_readLE_inv (n := 8) hr).1,
      (ReexecV3D0.lift_readLE_inv (n := 2) ha).1]
    simp only [V3.encodeCongestion,List.append_assoc]
    rfl

theorem pBwRequest_bytes {bs rest : Bytes} {q : BwRequest}
    (h : pBwRequest bs = .ok (q,rest)) : bs = V3.encodeBwRequest q ++ rest := by
  unfold pBwRequest at h
  obtain ⟨⟨s,r⟩,hs,h⟩ := bind_ok h
  obtain ⟨⟨b,r'⟩,hb,h⟩ := bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
  obtain ⟨rfl,rfl⟩ := h
  rw [(ReexecV3D0.lift_readLE_inv (n := 2) hs).1,(ReexecV3D0.pTake_split hb).1]
  simp only [V3.encodeBwRequest,List.append_assoc]
  rfl

theorem pBwRequests_bytes {bs rest : Bytes} {qs : List BwRequest}
    (h : pBwRequests bs = .ok (qs,rest)) : bs = V3.encodeBwRequests qs ++ rest := by
  unfold pBwRequests at h
  obtain ⟨⟨tag,r⟩,ht,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  · rename_i htag
    have ht0 : tag = 0 := by simp only [bne_iff_ne] at htag; omega
    subst tag
    rw [(ReexecV3D0.lift_readLE_inv (n := 1) ht).1,
      pVec_bytes pBwRequest V3.encodeBwRequest (fun _ _ _ hh => pBwRequest_bytes hh) h]
    simp only [V3.encodeBwRequests,List.append_assoc]
    rfl

end ZkFormal.NearV3.Assembly
