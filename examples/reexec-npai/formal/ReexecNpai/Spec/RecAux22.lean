import ReexecNpai.Spec.RecAux21

/-!
# Record parse: branch records, one iteration of the slot loop
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem bit_lo (bm ex i : Nat) (hbm : bm < 65536) (hi : i < 16) :
    (bm + ex * 65536) / 2 ^ i % 2 = bitOf bm i := by
  have h1 : (65536 : Nat) = 2 * 2 ^ (15 - i) * 2 ^ i := by
    rw [Nat.mul_assoc, ← Nat.pow_add, show 15 - i + i = 15 by omega]
  rw [h1, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), Nat.mul_left_comm,
    Nat.add_mul_mod_self_left]
  rfl

theorem bit_hi (bm ex i : Nat) (hbm : bm < 65536) :
    (bm + ex * 65536) / 2 ^ (i + 16) % 2 = bitOf ex i := by
  rw [show (2 : Nat) ^ (i + 16) = 65536 * 2 ^ i by rw [Nat.pow_add, Nat.mul_comm],
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by omega : 0 < 65536), Nat.div_eq_of_lt hbm,
    Nat.zero_add]
  rfl

theorem evAnd1' (x : Nat) : BinOp.and.eval x 1 = x % 2 := by
  simp only [BinOp.eval, Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 2 > 0 by omega); unfold wordMod; omega)

section
variable {pub cb pb : Bytes}

set_option maxHeartbeats 4000000 in
/-- An iteration over an absent slot. -/
theorem brBody_none {m : M} {i bm ex : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h6 : m.regs 6 = i + 1) (hi : i < 16) (h1 : m.regs 1 = bm + ex * 65536) (hbm : bm < 65536) (hex : ex < 65536)
    (hb : bitOf bm i = 0) :
    twp P (Inp pub cb pb) brBody m (fun m' c => m'.mem = m.mem ∧ m'.regs 6 = i ∧
      (∀ j, j ≠ 6 → j ≠ 11 → m'.regs j = m.regs j) ∧ c ≤ 8) := by
  have s1 : BinOp.shr.eval (bm + ex * 65536) i = (bm + ex * 65536) / 2 ^ i :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have b1 := bit_lo bm ex i hbm hi
  rw [hb] at b1
  simp only [brBody]
  rec_auto [hk1, hk8, h6, h1, s1, evAnd1', b1]

/-- Registers the slot loop leaves alone. -/
def BrFrame (m m' : M) : Prop :=
  m'.regs 1 = m.regs 1 ∧ m'.regs 5 = m.regs 5 ∧ m'.regs 8 = m.regs 8 ∧ m'.regs 9 = m.regs 9 ∧
  m'.regs 10 = m.regs 10 ∧ m'.regs 14 = m.regs 14 ∧ m'.regs 15 = m.regs 15

set_option maxHeartbeats 4000000 in
/-- An iteration over a present, unrevealed slot. -/
theorem brBody_hash {m : M} {i bm ex p2 : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h6 : m.regs 6 = i + 1) (hi : i < 16) (h1 : m.regs 1 = bm + ex * 65536) (hbm : bm < 65536) (hex : ex < 65536)
    (hb : bitOf bm i = 1) (he : bitOf ex i = 0) (h2 : m.regs 2 = p2) (hp2 : 32 ≤ p2) (hp2' : p2 ≤ 13844304) :
    twp P (Inp pub cb pb) brBody m (fun m' c => m'.mem = m.mem ∧ m'.regs 6 = i ∧ m'.regs 2 = p2 - 32 ∧
      (∀ j, j ≠ 2 → j ≠ 6 → j ≠ 11 → m'.regs j = m.regs j) ∧ c ≤ 20) := by
  have s1 : BinOp.shr.eval (bm + ex * 65536) i = (bm + ex * 65536) / 2 ^ i :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have s2 : BinOp.shr.eval (bm + ex * 65536) (i + 16) = (bm + ex * 65536) / 2 ^ (i + 16) :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have b1 := bit_lo bm ex i hbm hi
  have b2 := bit_hi bm ex i hbm
  rw [hb] at b1; rw [he] at b2
  have hsub : BinOp.sub.eval p2 32 = p2 - 32 := by simp only [BinOp.eval, wordMod]; omega
  simp only [brBody]
  rec_auto [hk1, hk8, h6, h1, h2, s1, s2, evAnd1', b1, b2, hsub]
  all_goals first | omega | (intro j h2 h6 h11; simp [h2, h6, h11])

set_option maxHeartbeats 8000000 in
/-- An iteration over a revealed child: pop it, set its `pslot`, append it to the child list. -/
theorem brBody_pop {m : M} {i bm ex p2 sp kc c : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h6 : m.regs 6 = i + 1) (hi : i < 16) (h1 : m.regs 1 = bm + ex * 65536) (hbm : bm < 65536) (hex : ex < 65536)
    (hb : bitOf bm i = 1) (he : bitOf ex i = 1) (h2 : m.regs 2 = p2) (hp2 : 32 ≤ p2) (hp2' : p2 ≤ 13844304)
    (h7 : m.regs 7 = sp) (hsp : 1 ≤ sp) (hspN : sp ≤ NCAP) (h3 : m.regs 3 = kc) (hkc : kc < NCAP)
    (hc : rd32 m (STK + 4 * (sp - 1)) = c) (hcN : c < NCAP)
    (hz : readMem m.mem (p2 - 32) 32 = readMem m.mem 136 32) :
    twp P (Inp pub cb pb) brBody m (fun m' cost =>
      m'.mem = wr4 (wr4 m.mem (AR + 24 * c + 8) (p2 - 32)) (KL + 4 * kc) c ∧
      m'.regs 6 = i ∧ m'.regs 2 = p2 - 32 ∧ m'.regs 7 = sp - 1 ∧ m'.regs 3 = kc + 1 ∧
      BrFrame m m' ∧ cost ≤ 70) := by
  simp only [NCAP] at hspN hkc hcN
  simp only [STK, rd32] at hc
  rw [show 7753384 + 4 * (sp - 1) = (sp - 1) * 4 + 7753384 by omega] at hc
  have s1 : BinOp.shr.eval (bm + ex * 65536) i = (bm + ex * 65536) / 2 ^ i :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have s2 : BinOp.shr.eval (bm + ex * 65536) (i + 16) = (bm + ex * 65536) / 2 ^ (i + 16) :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have b1 := bit_lo bm ex i hbm hi
  have b2 := bit_hi bm ex i hbm
  rw [hb] at b1; rw [he] at b2
  have hsub : BinOp.sub.eval p2 32 = p2 - 32 := by simp only [BinOp.eval, wordMod]; omega
  simp only [brBody, BrFrame]
  rec_auto [hk1, hk8, h6, h1, h2, h7, h3, s1, s2, evAnd1', b1, b2, hsub, hc, hz]
  repeat' apply And.intro
  all_goals first | omega | rfl |
    (simp only [wr4, show 117000 + (24 * c + 8) = c * 24 + 117008 by omega,
      show 6662472 + 4 * kc = kc * 4 + 6662472 by omega]; done)

set_option maxHeartbeats 8000000 in
theorem brBody_pop_wp {m : M} {i bm ex p2 sp kc c : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h6 : m.regs 6 = i + 1) (hi : i < 16) (h1 : m.regs 1 = bm + ex * 65536) (hbm : bm < 65536) (hex : ex < 65536)
    (hb : bitOf bm i = 1) (he : bitOf ex i = 1) (h2 : m.regs 2 = p2) (hp2 : 32 ≤ p2) (hp2' : p2 ≤ 13844304)
    (h7 : m.regs 7 = sp) (hspN : sp ≤ NCAP) (h3 : m.regs 3 = kc) (hkc : kc < NCAP)
    (hc : rd32 m (STK + 4 * (sp - 1)) = c) (hcN : 1 ≤ sp → c < NCAP) :
    wp P (Inp pub cb pb) brBody m (fun m' =>
      readMem m.mem (p2 - 32) 32 = readMem m.mem 136 32 ∧ 1 ≤ sp ∧
      m'.mem = wr4 (wr4 m.mem (AR + 24 * c + 8) (p2 - 32)) (KL + 4 * kc) c ∧
      m'.regs 6 = i ∧ m'.regs 2 = p2 - 32 ∧ m'.regs 7 = sp - 1 ∧ m'.regs 3 = kc + 1 ∧ BrFrame m m') := by
  simp only [NCAP] at hspN hkc hcN
  have s1 : BinOp.shr.eval (bm + ex * 65536) i = (bm + ex * 65536) / 2 ^ i :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have s2 : BinOp.shr.eval (bm + ex * 65536) (i + 16) = (bm + ex * 65536) / 2 ^ (i + 16) :=
    eval_shr _ _ (by omega) (by unfold wordMod; omega)
  have b1 := bit_lo bm ex i hbm hi
  have b2 := bit_hi bm ex i hbm
  rw [hb] at b1; rw [he] at b2
  have hsub : BinOp.sub.eval p2 32 = p2 - 32 := by simp only [BinOp.eval, wordMod]; omega
  simp only [brBody, BrFrame]
  rcases Nat.eq_zero_or_pos sp with h0 | hsp
  · clear hc hcN
    rec_vc [hk1, hk8, h6, h1, h2, h7, h3, s1, s2, evAnd1', b1, b2, hsub]
    intro _ _ hh; omega
  · have hcN := hcN hsp
    simp only [STK, rd32] at hc
    rw [show 7753384 + 4 * (sp - 1) = (sp - 1) * 4 + 7753384 by omega] at hc
    rec_auto [hk1, hk8, h6, h1, h2, h7, h3, s1, s2, evAnd1', b1, b2, hsub, hc]
    repeat' apply And.intro
    all_goals first | omega |
      (simp only [wr4, show 117000 + (24 * c + 8) = c * 24 + 117008 by omega,
        show 6662472 + 4 * kc = kc * 4 + 6662472 by omega]; done) | assumption

end

end ReexecNpai
