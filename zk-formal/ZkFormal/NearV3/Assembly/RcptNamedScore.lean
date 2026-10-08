import ZkFormal.NearV3.Assembly.RcptPredecessorScore
import ZkFormal.NearV3.Assembly.RcptNativeNamed

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

/- Generalized legacy RcptChars4 receiver arithmetic; source SHA256
1a7e148ba5cea2d2aed2b2cafb8bca5a31c1948aba9eefb2f2b284084076d28c.
Only native byte validity and the unchanged D0 parser's named-receiver condition
replace the legacy Good predicate. No non-system predecessor premise is used. -/

theorem character_hexcnt_le (r : Receipt) (hv : AccountId.valid r.receiverId=true) : accV (characterData r) ((characterData r).recv.length - 1) ≤ 64 := by
  have hL : 2≤(characterData r).recv.length ∧ (characterData r).recv.length≤64 := (strOk_of r.receiverId hv).len
  have := runSum_le (fun j => b2n (isHexC ((characterData r).recv.getD j 0))) 1
    (fun j => by unfold b2n; split <;> omega) ((characterData r).recv.length - 1)
  unfold accV; omega

theorem character_hex_all (r : Receipt) {n : Nat} (hn : n ≤ (characterData r).recv.length) (k : Nat)
    (h : runSum (fun j => b2n (isHexC ((characterData r).recv.getD (j + k) 0))) (n - 1) = n) (hk : k + n = (characterData r).recv.length)
    (hpos : 0 < n) : AccountId.allHex ((r.receiverId).drop k) = true := by
  have hf := runSum_full (fun j => b2n (isHexC ((characterData r).recv.getD (j + k) 0)))
    (fun j => by unfold b2n; split <;> omega) (n - 1) (by omega)
  have hl : (characterData r).recv = toNats r.receiverId := by rfl
  simp only [AccountId.allHex, List.all_eq_true]
  intro u hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  simp only [List.length_drop] at hj
  have := hf j (by have : (characterData r).recv.length = r.receiverId.length := by rw [hl]; simp [toNats]
                   omega)
  rw [hl] at this
  simp only [toNats, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show j + k < r.receiverId.length by omega), Option.map_some,
    Option.getD_some, b2n] at this
  simp only [List.getElem_drop, ← isHexC_toNat]
  simp only [Nat.add_comm k j]
  split at this
  · assumption
  · omega

theorem character_named_nonzero (r : Receipt) (hv : AccountId.valid r.receiverId=true)
    (hn : AccountId.isNamed r.receiverId=true) : NamedOk (characterData r) := by
  have hS : StrOk (characterData r).recv := strOk_of r.receiverId hv
  have hL := hS.len
  have hnm := hn
  simp only [AccountId.isNamed, Bool.not_eq_true', Bool.or_eq_false_iff] at hnm
  obtain ⟨⟨heth, hnear⟩, hdet⟩ := hnm
  have hl : (characterData r).recv = toNats r.receiverId := by rfl
  have hlen : r.receiverId.length = (characterData r).recv.length := by rw [hl]; simp [toNats]
  have hA := character_hexcnt_le r hv
  have hb0 := hS.byte 0 (by omega)
  have hb1 := hS.byte 1 (by omega)
  have hh : h01V (characterData r) ≤ 2 := by unfold h01V b2n; split <;> split <;> omega
  -- the first two bytes
  have take2 : ∀ a b : Nat, a < 256 → b < 256 → (characterData r).recv.getD 0 0 = a → (characterData r).recv.getD 1 0 = b →
      r.receiverId.take 2 = [UInt8.ofNat a, UInt8.ofNat b] := by
    intro a b ha hb h0 h1
    apply toNats_inj
    have : toNats (r.receiverId.take 2) = ((characterData r).recv).take 2 := by rw [hl]; simp [toNats, List.map_take]
    rw [this]
    apply List.ext_getElem (by simp [toNats]; omega)
    intro j hj1 hj2
    simp [toNats] at hj2
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have e0 : (characterData r).recv[0] = a := by
        rw [← h0]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (characterData r).recv.length by omega)]
      simp only [List.getElem_take, e0]
      simp [toNats, UInt8.toNat_ofNat, Nat.mod_eq_of_lt ha]
    · have e1 : (characterData r).recv[1] = b := by
        rw [← h1]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 1 < (characterData r).recv.length by omega)]
      simp only [List.getElem_take, e1]
      simp [toNats, UInt8.toNat_ofNat, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, ?_⟩
  · unfold pV1; rw [ofNat_mod]
    have hlt : sqd (characterData r).recv.length 64 + sqd (accV (characterData r) ((characterData r).recv.length - 1)) (characterData r).recv.length
        < Render.P := by
      have := P_big
      have := sqd_small (a := (characterData r).recv.length) (b := 64) (by omega) (by omega)
      have := sqd_small (a := accV (characterData r) ((characterData r).recv.length - 1)) (b := (characterData r).recv.length) (by omega)
        (by omega)
      omega
    apply ofNat_ne_zero _ hlt
    intro h0
    have h64 : (characterData r).recv.length = 64 := sqd_eq_zero (by omega)
    have hcnt : accV (characterData r) ((characterData r).recv.length - 1) = (characterData r).recv.length := sqd_eq_zero (by omega)
    have := character_hex_all r (n := (characterData r).recv.length) (Nat.le_refl _) 0
      (by unfold accV at hcnt; simp only [Nat.add_zero]; exact hcnt) (by omega) (by omega)
    simp only [List.drop_zero] at this
    simp [AccountId.isNearImplicit, hlen, h64, this] at hnear
  · unfold pV2; rw [ofNat_mod]
    have hlt : sqd (characterData r).recv.length 42 + sqd ((characterData r).recv.getD 0 0) 48 + sqd ((characterData r).recv.getD 1 0) 120 +
        sqd (accV (characterData r) ((characterData r).recv.length - 1)) (h01V (characterData r) + 40) < Render.P := by
      have := P_big
      have := sqd_small (a := (characterData r).recv.length) (b := 42) (by omega) (by omega)
      have := sqd_small (a := (characterData r).recv.getD 0 0) (b := 48) (by omega) (by omega)
      have := sqd_small (a := (characterData r).recv.getD 1 0) (b := 120) (by omega) (by omega)
      have := sqd_small (a := accV (characterData r) ((characterData r).recv.length - 1)) (b := h01V (characterData r) + 40) (by omega)
        (by omega)
      omega
    apply ofNat_ne_zero _ hlt
    intro h0
    have h42 : (characterData r).recv.length = 42 := sqd_eq_zero (by omega)
    have h48 : (characterData r).recv.getD 0 0 = 48 := sqd_eq_zero (by omega)
    have h120 : (characterData r).recv.getD 1 0 = 120 := sqd_eq_zero (by omega)
    have hcnt : accV (characterData r) ((characterData r).recv.length - 1) = h01V (characterData r) + 40 := sqd_eq_zero (by omega)
    have hh1 : h01V (characterData r) = 1 := by simp only [h01V, h48, h120]; decide
    rw [h42, hh1] at hcnt
    unfold accV at hcnt
    rw [show 42 - 1 = 39 + 2 by rfl, runSum_split2] at hcnt
    simp only [Nat.zero_add, h48, h120] at hcnt
    have hx0 : b2n (isHexC 48) = 1 := by decide
    have hx1 : b2n (isHexC 120) = 0 := by decide
    rw [hx0, hx1] at hcnt
    have hall := character_hex_all r (n := 40) (by omega) 2 (by show runSum _ 39 = 40; omega) (by omega) (by omega)
    have ht := take2 48 120 (by decide) (by decide) h48 h120
    simp [AccountId.isEthImplicit, hlen, h42, ht, hall] at heth
  · unfold pV3; rw [ofNat_mod]
    have hlt : sqd (characterData r).recv.length 42 + sqd ((characterData r).recv.getD 0 0) 48 + sqd ((characterData r).recv.getD 1 0) 115 +
        sqd (accV (characterData r) ((characterData r).recv.length - 1)) (h01V (characterData r) + 40) < Render.P := by
      have := P_big
      have := sqd_small (a := (characterData r).recv.length) (b := 42) (by omega) (by omega)
      have := sqd_small (a := (characterData r).recv.getD 0 0) (b := 48) (by omega) (by omega)
      have := sqd_small (a := (characterData r).recv.getD 1 0) (b := 115) (by omega) (by omega)
      have := sqd_small (a := accV (characterData r) ((characterData r).recv.length - 1)) (b := h01V (characterData r) + 40) (by omega)
        (by omega)
      omega
    apply ofNat_ne_zero _ hlt
    intro h0
    have h42 : (characterData r).recv.length = 42 := sqd_eq_zero (by omega)
    have h48 : (characterData r).recv.getD 0 0 = 48 := sqd_eq_zero (by omega)
    have h115 : (characterData r).recv.getD 1 0 = 115 := sqd_eq_zero (by omega)
    have hcnt : accV (characterData r) ((characterData r).recv.length - 1) = h01V (characterData r) + 40 := sqd_eq_zero (by omega)
    have hh1 : h01V (characterData r) = 1 := by simp only [h01V, h48, h115]; decide
    rw [h42, hh1] at hcnt
    unfold accV at hcnt
    rw [show 42 - 1 = 39 + 2 by rfl, runSum_split2] at hcnt
    simp only [Nat.zero_add, h48, h115] at hcnt
    have hx0 : b2n (isHexC 48) = 1 := by decide
    have hx1 : b2n (isHexC 115) = 0 := by decide
    rw [hx0, hx1] at hcnt
    have hall := character_hex_all r (n := 40) (by omega) 2 (by show runSum _ 39 = 40; omega) (by omega) (by omega)
    have ht := take2 48 115 (by decide) (by decide) h48 h115
    simp [AccountId.isNearDeterministic, hlen, h42, ht, hall] at hdet


theorem character_named_inverses (r : Receipt) (hv : AccountId.valid r.receiverId=true)
    (hn : AccountId.isNamed r.receiverId=true) :
    Fp.ofNat (pV1 (characterData r))*(Fp.ofNat (pV1 (characterData r)))⁻¹=1 ∧
    Fp.ofNat (pV2 (characterData r))*(Fp.ofNat (pV2 (characterData r)))⁻¹=1 ∧
    Fp.ofNat (pV3 (characterData r))*(Fp.ofNat (pV3 (characterData r)))⁻¹=1 := by
  obtain ⟨h1,h2,h3⟩ := character_named_nonzero r hv hn
  exact ⟨Fp.mul_inv_cancel h1,Fp.mul_inv_cancel h2,Fp.mul_inv_cancel h3⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
