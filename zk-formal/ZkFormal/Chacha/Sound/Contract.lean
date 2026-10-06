import ZkFormal.Chacha.Sound.Block

/-!
# ZkFormal.Chacha.Sound.Contract — feed-forward rows, one block, the bus contract

* `ff_row`: an `F j` row's output words are `add32 (state) (input)`;
* `ff_block`: every `F j` row ends a full block, and its outputs are words
  `j, 4+j, 8+j, 12+j` of `chachaBlock key ctr` for the block's key/counter;
* `chacha_contract`: every active `busChacha` message of the table is
  `chachaMsg key ctr idx ((chachaBlock key ctr)[idx]!)`.
-/

namespace ZkFormal.Chacha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- The `busChacha` message for word `idx` (`w`) of block `ctr` of `key`: key limbs, counter,
index, word limbs. -/
def chachaMsg (key : List Nat) (ctr idx w : Nat) : List Fp :=
  (List.range 16).map (fun q => Fp.ofNat ((key.getD (q / 2) 0 / 2 ^ (16 * (q % 2))) % 65536)) ++
    [Fp.ofNat ctr, Fp.ofNat idx, Fp.ofNat (w % 65536), Fp.ofNat (w / 65536 % 65536)]

theorem zev_limbL {Z : ZEnv} {f : Nat → Expr} {w : Nat} (h : BitsOf Z f w) {l : Nat} (hl : l < 2) :
    zev Z (E.limb f l) = Lm w l := zev_limb h hl

theorem zev_selF (hL : ChLocal tr t pub) {r j : Nat} (hr : r < tr.height t) (hj : j < 4)
    (hF : nv tr t r (colF j) = 1) (f : Nat → Expr) :
    zev (tenv tr t r pub) (E.sel colF 4 f) = zev (tenv tr t r pub) (f j) :=
  zev_sel _ colF 4 f j hj hF (fun x hx hxj => flag_unique hL hr (mem_flag_F hj) (mem_flag_F hx)
    (fun h => hxj (by unfold colF at h; omega)) hF)

/-- **A feed-forward row.** -/
theorem ff_row (hL : ChLocal tr t pub) {r j : Nat} (hr : r < tr.height t) (hj : j < 4)
    (hF : nv tr t r (colF j) = 1) (hR : Ranged tr t r) (hK : KOk tr t r) {kk : Nat} (hkk : kk < 4) :
    xw tr t r kk = add32 (sw tr t r (4 * kk + j)) (inW tr t r (4 * kk + j)) := by
  have hz := fun l (hl : l < 2) => by
    have h := zc hL hr (mem_cFF (List.mem_append_left _
      (List.mem_map.mpr ⟨2 * kk + l, List.mem_range.mpr (by omega), rfl⟩)))
    rw [zev_selF hL hr hj hF] at h
    have e2 : (2 * kk + l) / 2 = kk := by omega
    have e3 : (2 * kk + l) % 2 = l := by omega
    simp only [ffC, e2, e3, zev_addE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      sC, zev_c, cur_eq, zev_initLimb r hK (by omega : 4 * kk + j < 16) hl,
      zev_limbL (bitsX hL hr (show kk < 6 by omega)) hl] at h
    rw [zev_cin _ kk l hl, cur_eq] at h
    exact h
  have h0 := hz 0 (by decide); have h1 := hz 1 (by decide)
  simp only [show (0 : Nat) = 0 from rfl, if_true, show ¬ ((1 : Nat) = 0) by decide, if_false] at h0 h1
  have c0 := bC hL hr hkk (show 0 < 2 by decide); have c1 := bC hL hr hkk (show 1 < 2 by decide)
  have s0 := hR (4 * kk + j) (by omega) 0 (by decide); have s1 := hR (4 * kk + j) (by omega) 1 (by decide)
  have L0 := Lm_lt (inW tr t r (4 * kk + j)) 0; have L1 := Lm_lt (inW tr t r (4 * kk + j)) 1
  have X0 := Lm_lt (xw tr t r kk) 0; have X1 := Lm_lt (xw tr t r kk) 1
  have e0 := h0 (by omega) (by omega); have e1 := h1 (by omega) (by omega)
  exact add_limbs' s0 s1 (inW_lt r hK (by omega)) (xw_lt hL hr (by omega)) c0 c1 (by omega) (by omega)

/-- Rows of a block from position `m₀` on keep the key of the block. -/
theorem block_K (hL : ChLocal tr t pub) {s n : Nat} (hn : s + n < tr.height t)
    (hpos : ∀ m, m ≤ n → AtPos tr t (s + m) m) (hn85 : n ≤ 85) :
    ∀ m, m ≤ n → ∀ j l, j < 9 → l < 2 → nv tr t (s + m) (colK j l) = nv tr t s (colK j l) := by
  intro m hm
  induction m with
  | zero => intro j l _ _; rfl
  | succ m ih =>
    intro j l hj hl
    rw [← ih (by omega) j l hj hl]
    have hp := hpos m (by omega)
    have hr : s + m + 1 < tr.height t := by omega
    rw [show s + (m + 1) = s + m + 1 by omega]
    unfold AtPos at hp
    split at hp
    · exact copyK_of hL hr mem_flag_I0 hp (by decide) hj hl
    split at hp
    · exact copyK_of hL hr mem_flag_I1 hp (by decide) hj hl
    split at hp
    · exact copyK_of hL hr (mem_flag_P (Nat.mod_lt _ (by decide))) hp.1
        (by unfold colP colF; have := Nat.mod_lt (m - 2) (show 8 > 0 by decide); omega) hj hl
    split at hp
    · exact copyK_of hL hr (mem_flag_F (by omega)) hp (by unfold colF; omega) hj hl
    · exact hp.elim

/-- **One block.** -/
theorem ff_block (hL : ChLocal tr t pub) {f j : Nat} (hf : f < tr.height t) (hj : j < 4)
    (hF : nv tr t f (colF j) = 1) :
    KOk tr t f ∧ ∀ kk, kk < 4 →
      xw tr t f kk = (chachaBlock (keyOf tr t f) (kw tr t f 8))[4 * kk + j]! := by
  have hat : AtPos tr t f (82 + j) := by
    unfold AtPos; simp only [show 82 + j ≠ 0 by omega, show 82 + j ≠ 1 by omega,
      show ¬ (82 + j < 82) by omega, show 82 + j < 86 by omega, if_false, if_true]
    rw [show 82 + j - 82 = j by omega]; exact hF
  obtain ⟨hle, hall⟩ := atPos_walk hL (82 + j) f hf hat
  obtain ⟨s, rfl⟩ : ∃ s, f = s + (82 + j) := ⟨f - (82 + j), by omega⟩
  have hpos : ∀ m, m ≤ 82 + j → AtPos tr t (s + m) m := fun m hm => by
    have := hall m hm; rwa [show s + (82 + j) - (82 + j) + m = s + m by omega] at this
  have h0 : nv tr t s colI0 = 1 := by have := hpos 0 (by omega); unfold AtPos at this; simpa using this
  have h1 : nv tr t (s + 1) colI1 = 1 := by have := hpos 1 (by omega); unfold AtPos at this; simpa using this
  obtain ⟨hK, hR2, _, hst⟩ := init_rows hL (by omega) h0 h1
  have hKb := block_K hL (by omega) hpos (by omega)
  -- the quarter-round rows
  have hq : ∀ q, q ≤ 80 → Ranged tr t (s + 2 + q) ∧
      stA tr t (s + 2 + q) = stBefore (initArr (keyOf tr t s) (kw tr t s 8)) q := by
    intro q hq
    induction q with
    | zero => exact ⟨hR2, hst⟩
    | succ q ih =>
      obtain ⟨hR, hA⟩ := ih (by omega)
      have hp := hpos (2 + q) (by omega)
      unfold AtPos at hp
      simp only [show 2 + q ≠ 0 by omega, show 2 + q ≠ 1 by omega, show 2 + q < 82 by omega,
        if_false, if_true, show 2 + q - 2 = q by omega] at hp
      rw [show s + (2 + q) = s + 2 + q by omega] at hp
      obtain ⟨hR', hget⟩ := qr_row hL (show s + 2 + q + 1 < _ by omega) (Nat.mod_lt _ (by decide)) hp.1 hR
      refine ⟨by rw [show s + 2 + (q + 1) = s + 2 + q + 1 by omega]; exact hR', ?_⟩
      rw [show s + 2 + (q + 1) = s + 2 + q + 1 by omega, stBefore, ← hA]
      exact stA_eq_of (by rw [size_qrStep, stA_size]) hget
  -- the feed-forward rows before `f`
  have hfr : ∀ j', j' ≤ j → Ranged tr t (s + 82 + j') ∧
      stA tr t (s + 82 + j') = stBefore (initArr (keyOf tr t s) (kw tr t s 8)) 80 := by
    intro j' hj'
    induction j' with
    | zero => have := hq 80 (by decide); rw [show s + 2 + 80 = s + 82 + 0 by omega] at this; exact this
    | succ j' ih =>
      obtain ⟨hR, hA⟩ := ih (by omega)
      have hp := hpos (82 + j') (by omega)
      unfold AtPos at hp
      simp only [show 82 + j' ≠ 0 by omega, show 82 + j' ≠ 1 by omega, show ¬ (82 + j' < 82) by omega,
        show 82 + j' < 86 by omega, if_false, if_true, show 82 + j' - 82 = j' by omega] at hp
      rw [show s + (82 + j') = s + 82 + j' by omega] at hp
      have hx : colF j' = colI0 ∨ colF j' = colI1 ∨ colF j' = colF 0 ∨ colF j' = colF 1 ∨
          colF j' = colF 2 := by
        rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 by omega) with rfl | rfl | rfl <;> simp
      have hc := fun i l (hi : i < 16) (hl : l < 2) =>
        copyS_of hL (show s + 82 + j' + 1 < _ by omega) hx hp hi hl
      rw [show s + 82 + (j' + 1) = s + 82 + j' + 1 by omega]
      refine ⟨fun i hi l hl => by rw [hc i l hi hl]; exact hR i hi l hl, ?_⟩
      rw [← hA]
      apply stA_eq_of (stA_size _)
      intro i hi; rw [stA_get hi]; unfold sw; rw [hc i 0 hi (by decide), hc i 1 hi (by decide)]
  obtain ⟨hRf, hAf⟩ := hfr j (Nat.le_refl _)
  rw [show s + 82 + j = s + (82 + j) by omega] at hRf hAf
  -- keys at `f` equal keys at `s`
  have hkw : ∀ jj, jj < 9 → kw tr t (s + (82 + j)) jj = kw tr t s jj := fun jj hjj => by
    unfold kw; rw [hKb (82 + j) (Nat.le_refl _) jj 0 hjj (by decide),
      hKb (82 + j) (Nat.le_refl _) jj 1 hjj (by decide)]
  have hkey : keyOf tr t (s + (82 + j)) = keyOf tr t s := by
    unfold keyOf; apply List.map_congr_left; intro x hx; exact hkw x (by simp at hx; omega)
  have hKf : KOk tr t (s + (82 + j)) := ⟨fun jj hjj l hl => by
    rw [hKb (82 + j) (Nat.le_refl _) jj l hjj hl]; exact hK.1 jj hjj l hl, by rw [hkw 8 (by decide)]; exact hK.2⟩
  refine ⟨hKf, fun kk hkk => ?_⟩
  rw [ff_row hL hf hj hF hRf hKf hkk, hkey, hkw 8 (by decide), chachaBlock_eq]
  have hi : 4 * kk + j < 16 := by omega
  rw [← stA_get hi, hAf]
  unfold inW; rw [hkey, hkw 8 (by decide)]
  simp [hi]

/-! ## The bus contract -/

theorem eval_of_zev {r : Nat} {e : Expr} {n : Nat} (h : zev (tenv tr t r pub) e = (n : Int)) :
    e.eval tr t r pub = Fp.ofNat n := by
  rw [eval_eq, h, intCast_ofNat]

/-- An active multiplicity bit is on an `F` row. -/
theorem mult_F (hL : ChLocal tr t pub) {r kk : Nat} (hr : r < tr.height t) (hkk : kk < 4)
    (hm : nv tr t r (colM kk) = 1) : ∃ j, j < 4 ∧ nv tr t r (colF j) = 1 := by
  have hz := zc hL hr (mem_cFF (List.mem_append_right _
    (List.mem_map.mpr ⟨kk, List.mem_range.mpr hkk, rfl⟩)))
  simp only [zev_mul, zev_c, cur_eq, hm, zev_sub, zev_k, sumF, zev_sum, List.range_succ,
    List.range_zero, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, List.nil_append] at hz
  have b := fun j (hj : j < 4) => bHi hL hr (x := colF j) (by unfold colF; omega) (by unfold colF; omega)
  have b0 := b 0 (by decide); have b1 := b 1 (by decide); have b2 := b 2 (by decide); have b3 := b 3 (by decide)
  have := hz (by omega) (by omega)
  by_cases e0 : nv tr t r (colF 0) = 1
  · exact ⟨0, by decide, e0⟩
  by_cases e1 : nv tr t r (colF 1) = 1
  · exact ⟨1, by decide, e1⟩
  by_cases e2 : nv tr t r (colF 2) = 1
  · exact ⟨2, by decide, e2⟩
  exact ⟨3, by decide, by omega⟩

theorem multNat_eq (i : Interaction) (hi : i.mult.length = 1) {r : Nat} :
    i.multNat tr t r pub ≠ 0 → (i.mult.head!).eval tr t r pub = 1 := by
  intro h
  match i, hi with
  | ⟨_, [b], _, _⟩, _ =>
    unfold Interaction.multNat Interaction.multNat.go Interaction.multNat.go at h
    simp only at h ⊢
    by_cases e : b.eval tr t r pub = 1
    · exact e
    · rw [if_neg e] at h; simp at h

/-- **`chacha_contract`**: every active message the table provides on `busChacha` is a word of
`chachaBlock` for its key (8 words `< 2^32`, as limbs) and counter (`< 2^30`). -/
theorem chacha_contract (hL : ChLocal tr t pub) (busChacha : Nat) {r : Nat} (hr : r < tr.height t)
    {i : Interaction} (hi : i ∈ interactions busChacha) (hm : i.multNat tr t r pub ≠ 0) :
    ∃ key ctr idx, key.length = 8 ∧ (∀ x ∈ key, x < 2 ^ 32) ∧ ctr < 2 ^ 30 ∧ idx < 16 ∧
      i.bus = busChacha ∧ i.send = true ∧
      i.msgVal tr t r pub = chachaMsg key ctr idx ((chachaBlock key ctr)[idx]!) := by
  obtain ⟨kk, hkk, rfl⟩ := List.mem_map.mp hi
  have hkk' : kk < 4 := List.mem_range.mp hkk
  have h1 := multNat_eq _ rfl hm
  have hM : nv tr t r (colM kk) = 1 := by
    simp only [List.head!] at h1
    have : (tr.cell t r (colM kk)) = 1 := h1
    unfold nv; rw [this]; rfl
  obtain ⟨j, hj, hF⟩ := mult_F hL hr hkk' hM
  obtain ⟨hK, hw⟩ := ff_block hL hr hj hF
  refine ⟨keyOf tr t r, kw tr t r 8, 4 * kk + j, keyOf_length r, ?_, hK.2, by omega, rfl, rfl, ?_⟩
  · intro x hx
    obtain ⟨jj, hjj, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hjj
    unfold kw; have := hK.1 jj (by omega) 0 (by decide); have := hK.1 jj (by omega) 1 (by decide); omega
  rw [← hw kk hkk']
  unfold Interaction.msgVal chachaMsg outMsg
  rw [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro q hq
    have hq' := List.mem_range.mp hq
    simp only [Function.comp]
    apply eval_of_zev
    rw [zev_c, cur_eq]
    have hg : (keyOf tr t r).getD (q / 2) 0 = kw tr t r (q / 2) := by
      simp [keyOf, show q / 2 < 8 by omega]
    rw [hg]; unfold kw
    have := hK.1 (q / 2) (by omega) 0 (by decide); have := hK.1 (q / 2) (by omega) 1 (by decide)
    rcases (show q % 2 = 0 ∨ q % 2 = 1 by omega) with h | h <;> rw [h] <;> simp <;> omega
  · simp only [List.map_cons, List.map_nil]
    have hX := bitsX hL hr (pub := pub) (m := kk) (by omega)
    rw [eval_of_zev (n := kw tr t r 8) (by simp [ctrE, kw, cur_eq]),
      eval_of_zev (n := 4 * kk + j) (by rw [idxE, zev_selF hL hr hj hF]; simp),
      eval_of_zev (n := xw tr t r kk % 65536) (by rw [zev_limb hX (by decide)]; simp),
      eval_of_zev (n := xw tr t r kk / 65536 % 65536) (by rw [zev_limb hX (by decide)])]

end ZkFormal.Chacha.Sound
