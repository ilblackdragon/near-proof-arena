import ZkFormal.NearV3.Assembly.HeaderWireShape

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched ReexecV3D0 V3

theorem encVS_shape {a : Bytes} {k : PublicKey} {s : Nat}
    (ha : AccountId.valid a = true) (hk : pkWf3 k = true) (hs : s < Params.two128) :
    vsWf (encVS a k s) = true := by
  have haLen : a.length ≤ 64 := by
    have hh := ha
    simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1.2
  have hu : pU128 "" (u128 s) = .ok (s,[]) := by
    simpa only [List.append_nil] using pU128_ok "" s [] hs
  unfold vsWf vsCand encVS
  simp only [List.append_assoc,pU8_ok _ _ _ (by decide : (0:Nat)<256),
    bind,Except.bind,pBytes_ok _ _ _ (by omega : a.length < 4294967296),
    pPublicKey_ok _ _ _ hk,hu,pure,Except.pure]
  simp only [beq_self_eq_true,ha,hk,hs,decide_true,Bool.true_and]

theorem encTS_shape {a : Bytes} {l r : Nat}
    (ha : AccountId.valid a = true) (hl : l < 18446744073709551616)
    (hr : r < 18446744073709551616) : tsWf (encTS a l r) = true := by
  have haLen : a.length ≤ 64 := by
    have hh := ha
    simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1.2
  have hu : pU64 "" (u64 r) = .ok (r,[]) := by
    simpa only [List.append_nil] using pU64_ok "" r [] hr
  unfold tsWf tsCand encTS
  simp only [List.append_assoc,pBytes_ok _ _ _ (by omega : a.length < 4294967296),
    bind,Except.bind,pU64_ok _ _ _ hl,hu,pure,Except.pure]
  simp only [beq_self_eq_true,ha,hl,hr,decide_true,Bool.true_and]

theorem pValidatorStake_shape {bs rest v : Bytes}
    (h : pValidatorStake bs = .ok (v,rest)) : vsWf v = true := by
  unfold pValidatorStake at h
  obtain ⟨⟨tag,b1⟩,ht,h⟩ := Sched.bind_ok h
  dsimp only at h
  split at h
  · cases h
  · rename_i htag
    have ht0 : tag = 0 := by simp only [bne_iff_ne] at htag; omega
    subst tag
    obtain ⟨⟨a,b2⟩,ha,h⟩ := Sched.bind_ok h
    obtain ⟨⟨k,b3⟩,hk,h⟩ := Sched.bind_ok h
    obtain ⟨⟨s,b4⟩,hs,h⟩ := Sched.bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    dsimp only at hk hs
    have he : bs = encVS a k s ++ b4 := by
      rw [(lift_readLE_inv (n := 1) ht).1,pAccountId_bytes ha,pPublicKey_bytes hk,
        (lift_readLE_inv (n := 16) hs).1]
      simp only [encVS,List.append_assoc]
      rfl
    rw [he,consumed_app]
    exact encVS_shape (V3.pAccountId_valid ha) (pPublicKey_shape hk) (V3.pU128_lt hs)

theorem pTrieSplit_shape {bs rest v : Bytes}
    (h : pTrieSplit bs = .ok (v,rest)) : tsWf v = true := by
  unfold pTrieSplit at h
  obtain ⟨⟨a,b1⟩,ha,h⟩ := Sched.bind_ok h
  obtain ⟨⟨l,b2⟩,hl,h⟩ := Sched.bind_ok h
  obtain ⟨⟨r,b3⟩,hr,h⟩ := Sched.bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
  obtain ⟨rfl,rfl⟩ := h
  have he : bs = encTS a l r ++ b3 := by
    rw [pAccountId_bytes ha,(lift_readLE_inv (n := 8) hl).1,(lift_readLE_inv (n := 8) hr).1]
    simp only [encTS,List.append_assoc]
    rfl
  rw [he,consumed_app]
  exact encTS_shape (V3.pAccountId_valid ha) (lift_readLE_inv (n := 8) hl).2
    (lift_readLE_inv (n := 8) hr).2

end ZkFormal.NearV3.Assembly
