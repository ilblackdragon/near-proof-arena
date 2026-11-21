import FinalM5d.S384Chip

/-!
# FinalM5d.S384Out — an `S384` last row's digest bytes are the big-endian bytes of its `hout`

On a last block (`last = 1`), the row sends `SD (id, len, ob[48])`. `s384_out_byte`: for
`w < 6`, `i < 8`, `ob[8w+i]` is byte `i` (big-endian) of word `w` of the row's compression output
(`words r 24 8`, `S384Chip`), from the `outLimbs` constraints and the `R8` / `S2` / `S5` lookups
(which `RNG` answers with `(v, v mod 4, v / 4)` / `(v, v mod 32, v / 32)`).
-/

namespace FinalM5d.S384Out

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.BusMem FinalM5d.Whole
open FinalM5d.HbWhole FinalM5d.S384Chip

variable {tr : Trace Fp} {pub : List Fp}

local notation "PR" => 2013265921

/-! ## `RNG`'s split lookups -/

theorem split8F : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
    let v := b0.val + 2 * b1.val + 4 * b2.val + 8 * b3.val + 16 * b4.val + 32 * b5.val +
      64 * b6.val + 128 * b7.val
    b0.val + 2 * b1.val + 4 * b2.val + 8 * b3.val + 16 * b4.val = v % 32 ∧
      b5.val + 2 * b6.val + 4 * b7.val = v / 32 ∧
      b0.val + 2 * b1.val = v % 4 ∧
      b2.val + 2 * b3.val + 4 * b4.val + 8 * b5.val + 16 * b6.val + 32 * b7.val = v / 4 := by
  decide +kernel

theorem ev_bit_le {r : Nat} (hc : ∀ e ∈ Rng.constraints, e.eval tr 2 r pub = 0) {i : Nat} (hi : i < 8) :
    ev tr 2 r pub (Rng.T.c "bit" i) ≤ 1 :=
  bool_le (hc _ (rng_bit_sub (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))

/-- The value of `bitsVal lo n` (`n ≤ 8 − lo`) as a natural sum. -/
theorem ev_bitsVal {r : Nat} (hc : ∀ e ∈ Rng.constraints, e.eval tr 2 r pub = 0) (lo n : Nat)
    (hn : lo + n ≤ 8) :
    ev tr 2 r pub (Rng.bitsVal lo n) =
      ((List.range n).map fun i => 2 ^ i * ev tr 2 r pub (Rng.T.c "bit" (lo + i))).sum := by
  have hb : ∀ i, i < n → ev tr 2 r pub (Rng.T.c "bit" (lo + i)) ≤ 1 := fun i hi =>
    ev_bit_le hc (by omega)
  have key : ∀ m, m ≤ n → ((List.range m).map fun i =>
      ev tr 2 r pub (K (2 ^ i) * Rng.T.c "bit" (lo + i))).sum =
      ((List.range m).map fun i => 2 ^ i * ev tr 2 r pub (Rng.T.c "bit" (lo + i))).sum ∧
      ((List.range m).map fun i => 2 ^ i * ev tr 2 r pub (Rng.T.c "bit" (lo + i))).sum < 2 ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      obtain ⟨e1, e2⟩ := ih (by omega)
      have hbm := hb m (by omega)
      have h2m : 2 ^ m ≤ 128 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : m ≤ 7)) (by decide)
      have hterm : ev tr 2 r pub (K (2 ^ m) * Rng.T.c "bit" (lo + m)) =
          2 ^ m * ev tr 2 r pub (Rng.T.c "bit" (lo + m)) := by
        rw [FinRow.ev_hmul, FinRow.ev_K, Nat.mod_eq_of_lt (show 2 ^ m < PR by omega)]
        apply Nat.mod_eq_of_lt
        have := Nat.mul_le_mul_left (2 ^ m) hbm
        omega
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, hterm, e1]
      refine ⟨trivial, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ m) hbm
      rw [Nat.pow_succ]; omega
  rw [Rng.bitsVal, ev_sumE, List.map_map]
  obtain ⟨e1, e2⟩ := key n (Nat.le_refl _)
  have h2n : 2 ^ n ≤ 256 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 8)) (by decide)
  simp only [Function.comp_def]
  rw [e1, Nat.mod_eq_of_lt (by omega)]

/-- **The split lookups**: a received `S5 (b, lo, hi)` has `lo = b mod 32`, `hi = b / 32`, `b < 256`;
a received `S2 (b, lo, hi)` has `lo = b mod 4`, `hi = b / 4`. -/
theorem split_lookup (h : Holds finalAirS pub tr) {b : Nat} (hb : b = B_S2 ∨ b = B_S5)
    {x y z : Fp} (ho : Occ finalAirS tr pub b false [x, y, z]) :
    x.toNat < 256 ∧ (b = B_S5 → y.toNat = x.toNat % 32 ∧ z.toNat = x.toNat / 32) ∧
      (b = B_S2 → y.toNat = x.toNat % 4 ∧ z.toNat = x.toNat / 4) := by
  have hs := recv_sent h ho
  have hon : onlyIn finalAirS b true [2] = true := by
    rcases hb with rfl | rfl
    · exact only_S2_send
    · exact only_S5_send
  obtain ⟨t, ht2, ht, r, hr, i, hi, hbus, -, -, hmv⟩ := occ_in hon hs
  simp only [List.mem_singleton] at ht2
  subst ht2
  rw [tab2] at hi
  have hc : ∀ e ∈ Rng.constraints, e.eval tr 2 r pub = 0 := by
    have := h.constr 2 (by decide) r hr
    rw [tab2] at this; exact this
  have hv := ev_sub_eq (ev_of_eval (hc _ rng_v_mem))
  have bs := fun j (hj : j < 8) => ev_bit_le hc (i := j) hj
  simp only [Rng.table, Rng.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  have e8 := ev_bitsVal hc 0 8 (by omega)
  have b0 := bs 0 (by omega); have b1 := bs 1 (by omega); have b2 := bs 2 (by omega)
  have b3 := bs 3 (by omega); have b4 := bs 4 (by omega); have b5 := bs 5 (by omega)
  have b6 := bs 6 (by omega); have b7 := bs 7 (by omega)
  have sp := split8F ⟨_, Nat.lt_succ_of_le b0⟩ ⟨_, Nat.lt_succ_of_le b1⟩ ⟨_, Nat.lt_succ_of_le b2⟩
    ⟨_, Nat.lt_succ_of_le b3⟩ ⟨_, Nat.lt_succ_of_le b4⟩ ⟨_, Nat.lt_succ_of_le b5⟩
    ⟨_, Nat.lt_succ_of_le b6⟩ ⟨_, Nat.lt_succ_of_le b7⟩
  simp only at sp
  have hvv : ev tr 2 r pub (Rng.T.c "v") = ev tr 2 r pub (Rng.T.c "bit" 0) +
      2 * ev tr 2 r pub (Rng.T.c "bit" 1) + 4 * ev tr 2 r pub (Rng.T.c "bit" 2) +
      8 * ev tr 2 r pub (Rng.T.c "bit" 3) + 16 * ev tr 2 r pub (Rng.T.c "bit" 4) +
      32 * ev tr 2 r pub (Rng.T.c "bit" 5) + 64 * ev tr 2 r pub (Rng.T.c "bit" 6) +
      128 * ev tr 2 r pub (Rng.T.c "bit" 7) := by
    rw [hv, e8]; simp [List.range_succ]; omega
  rcases hi with rfl | rfl | rfl
  · rcases hb with rfl | rfl <;> exact absurd hbus (by decide)
  · -- S2
    have hbus' : b = B_S2 := hbus.symm
    simp only [Interaction.msgVal, sndBits, List.map_cons, List.map_nil, List.cons.injEq] at hmv
    obtain ⟨m1, m2, m3, -⟩ := hmv
    have l1 := ev_bitsVal hc 0 2 (by omega)
    have l2 := ev_bitsVal hc 2 6 (by omega)
    simp [List.range_succ] at l1 l2
    refine ⟨?_, fun h5 => absurd (hbus'.symm.trans h5) (by decide), fun _ => ⟨?_, ?_⟩⟩
    · rw [← m1]; show ev tr 2 r pub _ < 256; omega
    · rw [← m1, ← m2]; show ev tr 2 r pub _ = ev tr 2 r pub _ % 4; rw [l1, hvv]; omega
    · rw [← m1, ← m3]; show ev tr 2 r pub _ = ev tr 2 r pub _ / 4; rw [l2, hvv]; omega
  · -- S5
    have hbus' : b = B_S5 := hbus.symm
    simp only [Interaction.msgVal, sndBits, List.map_cons, List.map_nil, List.cons.injEq] at hmv
    obtain ⟨m1, m2, m3, -⟩ := hmv
    have l1 := ev_bitsVal hc 0 5 (by omega)
    have l2 := ev_bitsVal hc 5 3 (by omega)
    simp [List.range_succ] at l1 l2
    refine ⟨?_, fun _ => ⟨?_, ?_⟩, fun h2 => absurd (hbus'.symm.trans h2) (by decide)⟩
    · rw [← m1]; show ev tr 2 r pub _ < 256; omega
    · rw [← m1, ← m2]; show ev tr 2 r pub _ = ev tr 2 r pub _ % 32; rw [l1, hvv]; omega
    · rw [← m1, ← m3]; show ev tr 2 r pub _ = ev tr 2 r pub _ / 32; rw [l2, hvv]; omega

/-! ## The last row -/

theorem s384_last_sub :
    (List.range 6).flatMap (fun w => (List.range 3).map fun l =>
      S384.last * ((S384.outLimbs w).getD l 0 - S384.T.c "hout" (3 * w + l))) ⊆ S384.constraints := by
  intro e he; unfold S384.constraints
  simp only [List.mem_append]; simp only [he, true_or, or_true]

theorem s384_lastact_mem : S384.last * (1 - S384.act) ∈ S384.constraints := by
  unfold S384.constraints
  simp only [List.mem_append, List.mem_cons]
  simp only [true_or, or_true]

theorem s384_olk_sub :
    ((List.range 6).flatMap fun w =>
      [rcv B_S5 S384.last [S384.T.c "ob" (8 * w + 5), S384.T.c "o5lo" w, S384.T.c "o5hi" w],
       rcv B_S2 S384.last [S384.T.c "ob" (8 * w + 2), S384.T.c "o2lo" w, S384.T.c "o2hi" w]] ++
      ([0, 1, 3, 4, 6, 7].map fun i => rcv B_R8 S384.last [S384.T.c "ob" (8 * w + i)])) ⊆
      S384.interactions := by
  intro e he; unfold S384.interactions
  simp only [List.mem_append]; simp only [he, true_or, or_true]

/-- **The digest bytes of a last row.** Byte `i` of word `w < 6` of the compression output. -/
theorem s384_out_byte (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 1)
    (hl : ev tr 1 r pub S384.last = 1) {w i : Nat} (hw : w < 6) (hi : i < 8) :
    ev tr 1 r pub (S384.T.c "ob" (8 * w + i)) = (words tr r pub 24 8).getD w 0 / 256 ^ (7 - i) % 256 := by
  have hc := s384_constr h hr
  have hl' := evalOne hl
  -- the lookups of word `w`'s bytes
  have occ : ∀ (b : Nat) (es : List Expr), rcv b S384.last es ∈ S384.interactions →
      Occ finalAirS tr pub b false (es.map fun e => e.eval tr 1 r pub) := by
    intro b es hm
    have hm' : rcv b S384.last es ∈ (finalAirS.tables[1]'(by decide)).interactions := by
      rw [tab1]; exact hm
    exact occ_of (by decide) hr hm' ((multNat_one rfl).2 hl')
  have sub := fun e (he : e ∈ _) => s384_olk_sub (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, he⟩)
  have r8 : ∀ j, j ∈ [0, 1, 3, 4, 6, 7] → ev tr 1 r pub (S384.T.c "ob" (8 * w + j)) < 256 := by
    intro j hj
    exact lookup_lt h (.inl rfl) rfl (occ _ _ (sub _ (List.mem_append_right _ (List.mem_map.2 ⟨j, hj, rfl⟩))))
  obtain ⟨s5b, s5, -⟩ := split_lookup h (.inr rfl)
    (occ _ _ (sub _ (List.mem_append_left _ List.mem_cons_self)))
  obtain ⟨s2b, -, s2⟩ := split_lookup h (.inl rfl)
    (occ _ _ (sub _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain ⟨lo5, hi3⟩ := s5 rfl
  obtain ⟨lo2, hi6⟩ := s2 rfl
  -- the three limbs of the word
  have lim : ∀ l, l < 3 → ev tr 1 r pub ((S384.outLimbs w).getD l 0) =
      ev tr 1 r pub (S384.T.c "hout" (3 * w + l)) := fun l hl3 =>
    ev_sub_eq (gated (hc _ (s384_last_sub (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw,
      List.mem_map.2 ⟨l, List.mem_range.2 hl3, rfl⟩⟩))) hl)
  have hw0 := lim 0 (by omega); have hw1 := lim 1 (by omega); have hw2 := lim 2 (by omega)
  simp only [S384.outLimbs, S384.wordLimbs, List.getD_cons_zero, List.getD_cons_succ,
    FinRow.ev_hadd, FinRow.ev_hmul, FinRow.ev_K] at hw0 hw1 hw2
  -- the word
  have hword : (words tr r pub 24 8).getD w 0 = ev tr 1 r pub (S384.T.c "hout" (3 * w)) +
      2 ^ 21 * ev tr 1 r pub (S384.T.c "hout" (3 * w + 1)) +
      2 ^ 42 * ev tr 1 r pub (S384.T.c "hout" (3 * w + 2)) := by
    simp only [words, triples, List.getD_eq_getElem?_getD]
    rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, unl, List.getD_cons_zero, List.getD_cons_succ]
    simp only [← List.getD_eq_getElem?_getD]
    rw [show 3 * (24 + w) = 72 + 3 * w by omega, Nat.add_assoc 72 (3 * w) 1,
      Nat.add_assoc 72 (3 * w) 2, ifLimbs_hout _ (by omega), ifLimbs_hout _ (by omega),
      ifLimbs_hout _ (by omega)]
  generalize ev tr 1 r pub (S384.T.c "hout" (3 * w)) = H0 at hw0 hword
  generalize ev tr 1 r pub (S384.T.c "hout" (3 * w + 1)) = H1 at hw1 hword
  generalize ev tr 1 r pub (S384.T.c "hout" (3 * w + 2)) = H2 at hw2 hword
  have b0 := r8 0 (by simp); have b1 := r8 1 (by simp); have b3 := r8 3 (by simp)
  have b4 := r8 4 (by simp); have b6 := r8 6 (by simp); have b7 := r8 7 (by simp)
  dsimp only at s5b s2b lo5 hi3 lo2 hi6
  simp only [ev] at b0 b1 b3 b4 b6 b7 hw0 hw1 hw2 ⊢
  simp only [Nat.add_zero, Nat.mul_zero] at b0 hw0 hw1 hw2 ⊢
  simp (disch := omega) only [Nat.mod_eq_of_lt] at hw0 hw1 hw2
  rw [hword]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero] at *) <;> omega

end FinalM5d.S384Out
