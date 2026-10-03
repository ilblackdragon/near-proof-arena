import ReexecNpai.Spec.RecAux26

/-!
# Record parse: branch records, header checks ↔ positional facts
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem bitOf_testBit (x i : Nat) : bitOf x i = if x.testBit i then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [bitOf]
  have := Nat.mod_lt (x / 2 ^ i) (show 2 > 0 by omega)
  by_cases h : x / 2 ^ i % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem land_iff (ex bm : Nat) (hex : ex < 65536) : ex &&& bm = ex ↔ SubB 16 bm ex := by
  constructor
  · intro h i _ hi
    rw [bitOf_testBit] at hi ⊢
    cases he : ex.testBit i with
    | false => rw [he] at hi; simp at hi
    | true =>
      have h2 := congrArg (fun x => x.testBit i) h
      simp only [Nat.testBit_and, he, Bool.true_and] at h2
      simp [h2]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases he : ex.testBit i with
    | false => simp
    | true =>
      have hi : i < 16 := by
        refine Decidable.byContradiction fun hc => ?_
        have : ex < 2 ^ i := Nat.lt_of_lt_of_le hex (by
          calc 65536 = 2 ^ 16 := rfl
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
        rw [Nat.testBit_lt_two_pow this] at he
        exact absurd he (by simp)
      have := h i hi (by rw [bitOf_testBit, he]; rfl)
      rw [bitOf_testBit] at this
      cases hb : bm.testBit i with
      | false => rw [hb] at this; simp at this
      | true => rfl

theorem sl_drop_take (pb : Bytes) (a n d : Nat) (h : d + 32 ≤ n) :
    ((sl pb a n).drop d).take 32 = sl pb (a + d) 32 := by
  simp only [sl, List.drop_take, List.drop_drop, List.take_take]
  congr 1; omega

theorem brSlot_get (pb : Bytes) (o j : Nat) (hj : j < brNp pb o) :
    (brSlots pb o).getD j [] = sl pb (brR pb o + 2 + 32 * j) 32 := by
  rw [brSlots, chunks32_getD _ _ _ hj, sl_drop_take _ _ _ _ (by omega)]

/-- The slot zero checks, by memory or by position. -/
theorem zeroB_iff {pb : Bytes} {o : Nat} {M0 : Nat → UInt8} (hpf : readMem M0 PF pb.length = pb)
    (hd : readMem M0 0 168 = dataSeg) (hend : brEnd pb o ≤ pb.length) :
    ZeroB 16 (brBm pb o) (brEx pb o) (brSlots pb o) ↔
      ∀ j, j < 16 → bitOf (brBm pb o) j = 1 → bitOf (brEx pb o) j = 1 →
        readMem M0 (PF + brR pb o + 2 + 32 * popc j (brBm pb o)) 32 = readMem M0 136 32 := by
  have key : ∀ j, j < 16 → bitOf (brBm pb o) j = 1 →
      (readMem M0 (PF + brR pb o + 2 + 32 * popc j (brBm pb o)) 32 = readMem M0 136 32 ↔
        (brSlots pb o).getD (popc j (brBm pb o)) [] = zeros 32) := by
    intro j hj hb
    have hp := popc_top j (brBm pb o)
    rw [hb] at hp
    have hm := popc_mono (brBm pb o) (show j + 1 ≤ 16 by omega)
    have hlt : popc j (brBm pb o) < brNp pb o := by simp only [brNp]; omega
    rw [brSlot_get _ _ _ hlt, dZero hd,
      rm_at hpf (show PF + brR pb o + 2 + 32 * popc j (brBm pb o) = PF + (brR pb o + 2 + 32 * popc j (brBm pb o))
        by omega) (by simp only [brEnd] at hend; omega)]
  constructor
  · intro h j hj hb he; exact (key j hj hb).mpr (h j hj hb he)
  · intro h j hj hb he; exact (key j hj hb).mp (h j hj hb he)

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m m1 : M}

/-- The header chunks of a branch, assembled into `BrMid` (all positional facts but the slot zeros). -/
theorem brMid_of (hs : RecStart cb pb rs R N o A K S m m1)
    (hk : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6)
    (v5 : u8At pb o = 5 → o + 5 ≤ pb.length)
    (tag : u8At pb (brP pb o + 2) = if u8At pb o = 4 then 1 else 2)
    (sub : SubB 16 (brBm pb o) (brEx pb o)) (hend : brEnd pb o ≤ pb.length)
    (vlen : u8At pb o = 5 → sl pb (brP pb o + 3) 4 = sl pb (o + 1) 4)
    (vzero : u8At pb o = 5 → sl pb (brP pb o + 7) 32 = zeros 32)
    {ma mb mc md me m4 : M}
    (a0 : ma.mem = wr4 m1.mem (AR + 24 * A.length + 20) (brVal pb o))
    (a5 : ma.regs 5 = revSum pb A + (if u8At pb o = 5 then leAt pb (o + 1) 4 else 0))
    (a7 : ma.regs 7 = m1.regs 7) (a9 : ma.regs 9 = m1.regs 9)
    (b0 : mb.mem = wr4 (wr4 ma.mem (AR + 24 * A.length) (PF + brP pb o + 2)) (AR + 24 * A.length + 12)
      (rd32 ma C_KC))
    (b5 : mb.regs 5 = ma.regs 5) (b7 : mb.regs 7 = ma.regs 7) (b9 : mb.regs 9 = ma.regs 9)
    (c0 : mc.mem = mb.mem) (cr : ∀ j, j ≠ 2 → j ≠ 11 → j ≠ 12 → j ≠ 13 → mc.regs j = mb.regs j)
    (d0 : md.mem = mc.mem) (dr : ∀ j, j ≠ 1 → j ≠ 2 → j ≠ 6 → j ≠ 11 → j ≠ 12 → j ≠ 13 → md.regs j = mc.regs j)
    (e0 : me.mem = md.mem) (er : ∀ j, j ∉ [6, 4, 11, 12] → me.regs j = md.regs j)
    (r4 : BrRegs4 me m4 A.length (brHdr pb o) (brNp pb o) (PF + brP pb o + 2) (PF + brR pb o) (brEx pb o)
      (brBm pb o) (revSum pb A + (if u8At pb o = 5 then leAt pb (o + 1) 4 else 0))) :
    BrMid cb pb rs R N o A K S m m4 := by
  obtain ⟨g5, g7, g8, g14, g15⟩ := hs.regs
  obtain ⟨q0, q0', q5, q2, q10, q1, q3, q6, q7, q8, q9, q14, q15⟩ := r4
  have hkc : rd32 ma C_KC = K.length := by
    rw [rd32_eq, a0, rdm_wr4_other _ _ _ _ (by left; simp only [C_KC, AR]; omega), ← rd32_eq]
    exact hs.kc rfl
  have hkc' : rd32 me C_KC = K.length := by
    rw [rd32_eq, e0, d0, c0, b0, rdm_wr4_other _ _ _ _ (by left; simp only [C_KC, AR]; omega),
      rdm_wr4_other _ _ _ _ (by left; simp only [C_KC, AR]; omega), ← rd32_eq, hkc]
  have h7 : me.regs 7 = S.length := by
    rw [er 7 (by decide), dr 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      cr 7 (by omega) (by omega) (by omega) (by omega), b7, a7, g7]
  refine ⟨hs.inv, hs.cap, hk, v5, tag, sub, hend, vlen, vzero, ?_, q1, ?_, by rw [q3, hkc'], q5,
    q6, by rw [q7, h7], q8, by rw [q9, er 9 (by decide), dr 9 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), cr 9 (by omega) (by omega) (by omega) (by omega), b9, a9, hs.rE], ?_, q14, q15⟩
  · rw [q0, e0, d0, c0, b0, hkc, a0, hs.mem]; rfl
  · rw [q2]; simp only [brNp]; omega
  · rw [q10]; simp only [brEnd, brR]; omega

end

end ReexecNpai
