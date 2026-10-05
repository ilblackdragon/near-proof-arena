import ZkFormal.Near.Render.Proof.RcptChars3

/-!
# ZkFormal.Near.Render.Proof.RcptChars4 — `PredOk`, `NamedOk` from `Good`

The predecessor is not `system` (`inSlice`), so `Σ (p_j − "system"_j)² + (L − 6)²`
is a nonzero natural below `p`; the receiver is named, so none of the three
implicit-account patterns (64 hex, `0x` + 40 hex, `0s` + 40 hex) matches.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem runSum_le (x : Nat → Nat) (B : Nat) (h : ∀ j, x j ≤ B) : ∀ i, runSum x i ≤ (i + 1) * B
  | 0 => by rw [runSum_zero]; have := h 0; omega
  | i + 1 => by rw [runSum_succ, Nat.add_mul, Nat.one_mul]; have := runSum_le x B h i; have := h (i + 1); omega

theorem runSum_eq_zero (x : Nat → Nat) : ∀ i, runSum x i = 0 → ∀ j, j ≤ i → x j = 0
  | 0, h, j, hj => by rw [runSum_zero] at h; rw [show j = 0 by omega]; exact h
  | i + 1, h, j, hj => by
    rw [runSum_succ] at h
    by_cases hj' : j = i + 1
    · subst hj'; omega
    · exact runSum_eq_zero x i (by omega) j (by omega)

theorem runSum_full (x : Nat → Nat) (h : ∀ j, x j ≤ 1) : ∀ i, runSum x i = i + 1 → ∀ j, j ≤ i → x j = 1
  | 0, hs, j, hj => by rw [runSum_zero] at hs; rw [show j = 0 by omega]; exact hs
  | i + 1, hs, j, hj => by
    rw [runSum_succ] at hs
    have h1 := runSum_le x 1 h i
    have h2 := h (i + 1)
    by_cases hj' : j = i + 1
    · subst hj'; omega
    · exact runSum_full x h i (by omega) j (by omega)

theorem sqd_eq_zero {a b : Nat} (h : sqd a b = 0) : a = b := by
  unfold sqd at h
  rcases Nat.le_total a b with h' | h'
  · have : (b - a) * (b - a) = 0 := by omega
    rcases Nat.mul_eq_zero.1 this with h'' | h'' <;> omega
  · have : (a - b) * (a - b) = 0 := by omega
    rcases Nat.mul_eq_zero.1 this with h'' | h'' <;> omega

theorem sqd_le {a b : Nat} (ha : a < 256) (hb : b < 256) : sqd a b ≤ 65025 := by
  unfold sqd
  rcases Nat.le_total a b with h | h
  · rw [show a - b = 0 by omega]
    have : (b - a) * (b - a) ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · rw [show b - a = 0 by omega]
    have : (a - b) * (a - b) ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem sqd_small {a b : Nat} (ha : a ≤ 300) (hb : b ≤ 300) : sqd a b ≤ 90000 := by
  unfold sqd
  rcases Nat.le_total a b with h | h
  · rw [show a - b = 0 by omega]
    have : (b - a) * (b - a) ≤ 300 * 300 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · rw [show b - a = 0 by omega]
    have : (a - b) * (a - b) ≤ 300 * 300 := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem toNats_inj {a b : Bytes} (h : toNats a = toNats b) : a = b := by
  have := congrArg ofNats h
  simpa [ofNats_toNats] using this

theorem isHexC_toNat (u : UInt8) : isHexC u.toNat = AccountId.isHex u := by
  simp only [isHexC, AccountId.isHex]; cases (48 ≤ u.toNat && u.toNat ≤ 57) <;> simp

theorem P_big : 100000000 < Render.P := by decide

theorem runSum_split2 (x : Nat → Nat) : ∀ n, runSum x (n + 2) = x 0 + x 1 + runSum (fun j => x (j + 2)) n
  | 0 => by simp [runSum_succ, runSum_zero]
  | n + 1 => by
    rw [runSum_succ, runSum_split2 x n, runSum_succ, show n + 2 + 1 = n + 1 + 2 by omega]; omega

section
variable {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e)
include hg hr

theorem predOk : PredOk (Df c e r) := by
  have hS := pred_ok hg hr
  have hsl := rc_slice hg hr
  simp only [Receipt.inSlice, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsl
  have hne := hsl.1.2
  unfold PredOk pP
  rw [ofNat_mod]
  have hL := hS.len
  have hB : accP (Df c e r) ((Df c e r).pred.length - 1) ≤ 64 * 65025 := by
    have h3 := runSum_le (fun j => sqd ((Df c e r).pred.getD j 0) (sysB j)) 65025 (fun j => by
      have h1 : (Df c e r).pred.getD j 0 < 256 := by
        by_cases hj : j < (Df c e r).pred.length
        · exact hS.byte j hj
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (Df c e r).pred.length ≤ j by omega)]
      have h2 : sysB j < 256 := by
        simp only [sysB_eq, List.getD_eq_getElem?_getD]
        rcases (show j < 6 ∨ 6 ≤ j by omega) with h | h
        · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
        · simp [List.getElem?_eq_none (show [115, 121, 115, 116, 101, 109].length ≤ j by simp; omega)]
      exact sqd_le h1 h2) ((Df c e r).pred.length - 1)
    exact Nat.le_trans h3 (Nat.mul_le_mul_right _ (by omega))
  have hB2 : sqd (Df c e r).pred.length 6 ≤ 90000 := sqd_small (by omega) (by omega)
  apply ofNat_ne_zero _ (by have := P_big; omega)
  intro h0
  have h6 : (Df c e r).pred.length = 6 := sqd_eq_zero (by omega)
  have hz := runSum_eq_zero _ _ (show accP (Df c e r) ((Df c e r).pred.length - 1) = 0 by omega)
  apply hne
  apply toNats_inj
  rw [← show (Df c e r).pred = toNats (e.rc r).predecessorId by rw [Df_eq hr]; rfl]
  apply List.ext_getElem (by rw [h6]; rfl)
  intro j h1 h2
  have := sqd_eq_zero (hz j (by omega))
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, sysB_eq] at this
  rw [this]
  rw [h6] at h1
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem hexcnt_le : accV (Df c e r) ((Df c e r).recv.length - 1) ≤ 64 := by
  have hL := (recv_ok hg hr).len
  have := runSum_le (fun j => b2n (isHexC ((Df c e r).recv.getD j 0))) 1
    (fun j => by unfold b2n; split <;> omega) ((Df c e r).recv.length - 1)
  unfold accV; omega

theorem hex_all {n : Nat} (hn : n ≤ (Df c e r).recv.length) (k : Nat)
    (h : runSum (fun j => b2n (isHexC ((Df c e r).recv.getD (j + k) 0))) (n - 1) = n) (hk : k + n = (Df c e r).recv.length)
    (hpos : 0 < n) : AccountId.allHex (((e.rc r).receiverId).drop k) = true := by
  have hf := runSum_full (fun j => b2n (isHexC ((Df c e r).recv.getD (j + k) 0)))
    (fun j => by unfold b2n; split <;> omega) (n - 1) (by omega)
  have hl : (Df c e r).recv = toNats (e.rc r).receiverId := by rw [Df_eq hr]; rfl
  simp only [AccountId.allHex, List.all_eq_true]
  intro u hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  simp only [List.length_drop] at hj
  have := hf j (by have : (Df c e r).recv.length = (e.rc r).receiverId.length := by rw [hl]; simp [toNats]
                   omega)
  rw [hl] at this
  simp only [toNats, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show j + k < (e.rc r).receiverId.length by omega), Option.map_some,
    Option.getD_some, b2n] at this
  simp only [List.getElem_drop, ← isHexC_toNat]
  simp only [Nat.add_comm k j]
  split at this
  · assumption
  · omega

theorem namedOk : NamedOk (Df c e r) := by
  have hS := recv_ok hg hr
  have hL := hS.len
  have hsl := rc_slice hg hr
  simp only [Receipt.inSlice, Bool.and_eq_true] at hsl
  have hnm := hsl.2
  simp only [AccountId.isNamed, Bool.not_eq_true', Bool.or_eq_false_iff] at hnm
  obtain ⟨⟨heth, hnear⟩, hdet⟩ := hnm
  have hl : (Df c e r).recv = toNats (e.rc r).receiverId := by rw [Df_eq hr]; rfl
  have hlen : (e.rc r).receiverId.length = (Df c e r).recv.length := by rw [hl]; simp [toNats]
  have hA := hexcnt_le hg hr
  have hb0 := hS.byte 0 (by omega)
  have hb1 := hS.byte 1 (by omega)
  have hh : h01V (Df c e r) ≤ 2 := by unfold h01V b2n; split <;> split <;> omega
  -- the first two bytes
  have take2 : ∀ a b : Nat, a < 256 → b < 256 → (Df c e r).recv.getD 0 0 = a → (Df c e r).recv.getD 1 0 = b →
      (e.rc r).receiverId.take 2 = [UInt8.ofNat a, UInt8.ofNat b] := by
    intro a b ha hb h0 h1
    apply toNats_inj
    have : toNats ((e.rc r).receiverId.take 2) = ((Df c e r).recv).take 2 := by rw [hl]; simp [toNats, List.map_take]
    rw [this]
    apply List.ext_getElem (by simp [toNats]; omega)
    intro j hj1 hj2
    simp [toNats] at hj2
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have e0 : (Df c e r).recv[0] = a := by
        rw [← h0]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (Df c e r).recv.length by omega)]
      simp only [List.getElem_take, e0]
      simp [toNats, UInt8.toNat_ofNat, Nat.mod_eq_of_lt ha]
    · have e1 : (Df c e r).recv[1] = b := by
        rw [← h1]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 1 < (Df c e r).recv.length by omega)]
      simp only [List.getElem_take, e1]
      simp [toNats, UInt8.toNat_ofNat, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, ?_⟩
  · unfold pV1; rw [ofNat_mod]
    have hlt : sqd (Df c e r).recv.length 64 + sqd (accV (Df c e r) ((Df c e r).recv.length - 1)) (Df c e r).recv.length
        < Render.P := by
      have := P_big
      have := sqd_small (a := (Df c e r).recv.length) (b := 64) (by omega) (by omega)
      have := sqd_small (a := accV (Df c e r) ((Df c e r).recv.length - 1)) (b := (Df c e r).recv.length) (by omega)
        (by omega)
      omega
    apply ofNat_ne_zero _ hlt
    intro h0
    have h64 : (Df c e r).recv.length = 64 := sqd_eq_zero (by omega)
    have hcnt : accV (Df c e r) ((Df c e r).recv.length - 1) = (Df c e r).recv.length := sqd_eq_zero (by omega)
    have := hex_all hg hr (n := (Df c e r).recv.length) (Nat.le_refl _) 0
      (by unfold accV at hcnt; simp only [Nat.add_zero]; exact hcnt) (by omega) (by omega)
    simp only [List.drop_zero] at this
    simp [AccountId.isNearImplicit, hlen, h64, this] at hnear
  · unfold pV2; rw [ofNat_mod]
    have hlt : sqd (Df c e r).recv.length 42 + sqd ((Df c e r).recv.getD 0 0) 48 + sqd ((Df c e r).recv.getD 1 0) 120 +
        sqd (accV (Df c e r) ((Df c e r).recv.length - 1)) (h01V (Df c e r) + 40) < Render.P := by
      have := P_big
      have := sqd_small (a := (Df c e r).recv.length) (b := 42) (by omega) (by omega)
      have := sqd_small (a := (Df c e r).recv.getD 0 0) (b := 48) (by omega) (by omega)
      have := sqd_small (a := (Df c e r).recv.getD 1 0) (b := 120) (by omega) (by omega)
      have := sqd_small (a := accV (Df c e r) ((Df c e r).recv.length - 1)) (b := h01V (Df c e r) + 40) (by omega)
        (by omega)
      omega
    apply ofNat_ne_zero _ hlt
    intro h0
    have h42 : (Df c e r).recv.length = 42 := sqd_eq_zero (by omega)
    have h48 : (Df c e r).recv.getD 0 0 = 48 := sqd_eq_zero (by omega)
    have h120 : (Df c e r).recv.getD 1 0 = 120 := sqd_eq_zero (by omega)
    have hcnt : accV (Df c e r) ((Df c e r).recv.length - 1) = h01V (Df c e r) + 40 := sqd_eq_zero (by omega)
    have hh1 : h01V (Df c e r) = 1 := by simp only [h01V, h48, h120]; decide
    rw [h42, hh1] at hcnt
    unfold accV at hcnt
    rw [show 42 - 1 = 39 + 2 by rfl, runSum_split2] at hcnt
    simp only [Nat.zero_add, h48, h120] at hcnt
    have hx0 : b2n (isHexC 48) = 1 := by decide
    have hx1 : b2n (isHexC 120) = 0 := by decide
    rw [hx0, hx1] at hcnt
    have hall := hex_all hg hr (n := 40) (by omega) 2 (by show runSum _ 39 = 40; omega) (by omega) (by omega)
    have ht := take2 48 120 (by decide) (by decide) h48 h120
    simp [AccountId.isEthImplicit, hlen, h42, ht, hall] at heth
  · unfold pV3; rw [ofNat_mod]
    have hlt : sqd (Df c e r).recv.length 42 + sqd ((Df c e r).recv.getD 0 0) 48 + sqd ((Df c e r).recv.getD 1 0) 115 +
        sqd (accV (Df c e r) ((Df c e r).recv.length - 1)) (h01V (Df c e r) + 40) < Render.P := by
      have := P_big
      have := sqd_small (a := (Df c e r).recv.length) (b := 42) (by omega) (by omega)
      have := sqd_small (a := (Df c e r).recv.getD 0 0) (b := 48) (by omega) (by omega)
      have := sqd_small (a := (Df c e r).recv.getD 1 0) (b := 115) (by omega) (by omega)
      have := sqd_small (a := accV (Df c e r) ((Df c e r).recv.length - 1)) (b := h01V (Df c e r) + 40) (by omega)
        (by omega)
      omega
    apply ofNat_ne_zero _ hlt
    intro h0
    have h42 : (Df c e r).recv.length = 42 := sqd_eq_zero (by omega)
    have h48 : (Df c e r).recv.getD 0 0 = 48 := sqd_eq_zero (by omega)
    have h115 : (Df c e r).recv.getD 1 0 = 115 := sqd_eq_zero (by omega)
    have hcnt : accV (Df c e r) ((Df c e r).recv.length - 1) = h01V (Df c e r) + 40 := sqd_eq_zero (by omega)
    have hh1 : h01V (Df c e r) = 1 := by simp only [h01V, h48, h115]; decide
    rw [h42, hh1] at hcnt
    unfold accV at hcnt
    rw [show 42 - 1 = 39 + 2 by rfl, runSum_split2] at hcnt
    simp only [Nat.zero_add, h48, h115] at hcnt
    have hx0 : b2n (isHexC 48) = 1 := by decide
    have hx1 : b2n (isHexC 115) = 0 := by decide
    rw [hx0, hx1] at hcnt
    have hall := hex_all hg hr (n := 40) (by omega) 2 (by show runSum _ 39 = 40; omega) (by omega) (by omega)
    have ht := take2 48 115 (by decide) (by decide) h48 h115
    simp [AccountId.isNearDeterministic, hlen, h42, ht, hall] at hdet

end

end RcptP

end ZkFormal.Near.Render
