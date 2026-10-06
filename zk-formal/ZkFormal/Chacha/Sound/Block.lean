import ZkFormal.Chacha.Sound.Row

/-!
# ZkFormal.Chacha.Sound.Block — input rows, copies, feed-forward, one block

* `init_rows`: an `I0, I1` pair holds a range-checked key and counter (`< 2^30`), and the
  next row's state is `initArr key ctr`;
* `block_state`: the state before quarter-round `q ≤ 80` of a block is
  `stBefore (initArr key ctr) q`, so the `F` rows see `rounds 10 (initArr key ctr)`;
* `ff_row`: an `F j` row outputs words `j, 4+j, 8+j, 12+j` of `chachaBlock key ctr`.
-/

namespace ZkFormal.Chacha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- Key word `j` (`j = 8`: the counter) of row `r`. -/
def kw (tr : Trace Fp) (t r j : Nat) : Nat := nv tr t r (colK j 0) + 65536 * nv tr t r (colK j 1)

/-- The key of row `r`. -/
def keyOf (tr : Trace Fp) (t r : Nat) : List Nat := (List.range 8).map (kw tr t r)

theorem keyOf_length (r : Nat) : (keyOf tr t r).length = 8 := by simp [keyOf]

theorem arr_ext16 {a b : Array Nat} (ha : a.size = 16) (hb : b.size = 16)
    (h : ∀ i, i < 16 → a[i]! = b[i]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro i h1 h2
  have := h i (by omega)
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

theorem stA_eq_of {r : Nat} {s : Array Nat} (hs : s.size = 16)
    (h : ∀ i, i < 16 → sw tr t r i = s[i]!) : stA tr t r = s :=
  arr_ext16 (stA_size r) hs (fun i hi => by rw [stA_get hi]; exact h i hi)

section
variable (hL : ChLocal tr t pub) {r : Nat} (hr : r + 1 < tr.height t)
include hL hr

theorem hr1 : r < tr.height t := by omega

/-! ## Copies -/

theorem copyS (hg : zev (tenv tr t r pub) gCopy = 1)
    (hP : ∀ p, p < 8 → nv tr t r (colP p) = 0) {i l : Nat} (hi : i < 16) (hl : l < 2) :
    nv tr t (r + 1) (colS i l) = nv tr t r (colS i l) := by
  have hz := zc hL (hr1 hL hr) (mem_cCopy (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩)))
  have hs := zev_sel_zero (tenv tr t r pub) colP 8 (fun p => E.sub (sN i l) (newS (grp p) i l))
    (fun p hp => by rw [cur_eq]; exact hP p hp)
  rw [zev_add, zev_mul, hg, Int.one_mul, hs, Int.add_zero] at hz
  simp only [zev_sub, sN, sC, zev_n, zev_c, nxt_eq hr, cur_eq] at hz
  have := nv_lt (tr := tr) (t := t) (r + 1) (colS i l); have := nv_lt (tr := tr) (t := t) r (colS i l)
  have := hz (by omega) (by omega); omega

theorem copyK (hg : zev (tenv tr t r pub) (.add gCopy sumP) = 1) {j l : Nat} (hj : j < 9) (hl : l < 2) :
    nv tr t (r + 1) (colK j l) = nv tr t r (colK j l) := by
  have hz := zc hL (hr1 hL hr) (mem_cCopy (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩)))
  rw [zev_mul, hg, Int.one_mul] at hz
  simp only [zev_sub, zev_n, zev_c, nxt_eq hr, cur_eq] at hz
  have := nv_lt (tr := tr) (t := t) (r + 1) (colK j l); have := nv_lt (tr := tr) (t := t) r (colK j l)
  have := hz (by omega) (by omega); omega

end

/-- Flags of a row with exactly the flag `x` set. -/
theorem flags_of (hL : ChLocal tr t pub) {r x : Nat} (hr : r < tr.height t) (hx : x ∈ flagCols)
    (h1 : nv tr t r x = 1) : ∀ y ∈ flagCols, nv tr t r y = if y = x then 1 else 0 := by
  intro y hy
  by_cases e : y = x
  · rw [if_pos e, e, h1]
  · rw [if_neg e]; exact flag_unique hL hr hx hy e h1

theorem zev_gCopy (r : Nat) : zev (tenv tr t r pub) gCopy =
    (nv tr t r colI0 + nv tr t r colI1 + nv tr t r (colF 0) + nv tr t r (colF 1) + nv tr t r (colF 2) : Nat) := by
  simp [gCopy, zev_sum, cur_eq]; omega

theorem zev_sumP (r : Nat) : zev (tenv tr t r pub) sumP =
    (nv tr t r (colP 0) + nv tr t r (colP 1) + nv tr t r (colP 2) + nv tr t r (colP 3) +
      nv tr t r (colP 4) + nv tr t r (colP 5) + nv tr t r (colP 6) + nv tr t r (colP 7) : Nat) := by
  simp [sumP, zev_sum, List.range_succ, cur_eq]; omega

theorem flag_vals (hL : ChLocal tr t pub) {r x : Nat} (hr : r < tr.height t) (hx : x ∈ flagCols)
    (h1 : nv tr t r x = 1) :
    nv tr t r colI0 = (if colI0 = x then 1 else 0) ∧ nv tr t r colI1 = (if colI1 = x then 1 else 0) ∧
    (∀ p, p < 8 → nv tr t r (colP p) = if colP p = x then 1 else 0) ∧
    (∀ j, j < 4 → nv tr t r (colF j) = if colF j = x then 1 else 0) :=
  ⟨flags_of hL hr hx h1 _ mem_flag_I0, flags_of hL hr hx h1 _ mem_flag_I1,
   fun p hp => flags_of hL hr hx h1 _ (mem_flag_P hp), fun j hj => flags_of hL hr hx h1 _ (mem_flag_F hj)⟩

/-- `K` is copied from every row of a block but the last (`I0, I1, Q, F0..F2`). -/
theorem copyK_of (hL : ChLocal tr t pub) {r x : Nat} (hr : r + 1 < tr.height t) (hx : x ∈ flagCols)
    (h1 : nv tr t r x = 1) (hx3 : x ≠ colF 3) {j l : Nat} (hj : j < 9) (hl : l < 2) :
    nv tr t (r + 1) (colK j l) = nv tr t r (colK j l) := by
  apply copyK hL hr _ hj hl
  rw [zev_add, zev_gCopy, zev_sumP]
  obtain ⟨a, b, c, d⟩ := flag_vals hL (by omega) hx h1
  rw [a, b, c 0 (by decide), c 1 (by decide), c 2 (by decide), c 3 (by decide), c 4 (by decide),
    c 5 (by decide), c 6 (by decide), c 7 (by decide), d 0 (by decide), d 1 (by decide), d 2 (by decide)]
  rw [flagCols_eq] at hx
  unfold colI0 colI1 colP colF at *
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

/-- `S` is copied from `I0, I1, F0, F1, F2` rows. -/
theorem copyS_of (hL : ChLocal tr t pub) {r x : Nat} (hr : r + 1 < tr.height t)
    (hx : x = colI0 ∨ x = colI1 ∨ x = colF 0 ∨ x = colF 1 ∨ x = colF 2) (h1 : nv tr t r x = 1)
    {i l : Nat} (hi : i < 16) (hl : l < 2) : nv tr t (r + 1) (colS i l) = nv tr t r (colS i l) := by
  have hxf : x ∈ flagCols := by
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact mem_flag_I0
    · exact mem_flag_I1
    · exact mem_flag_F (by decide)
    · exact mem_flag_F (by decide)
    · exact mem_flag_F (by decide)
  obtain ⟨a, b, c, d⟩ := flag_vals hL (by omega) hxf h1
  apply copyS hL hr _ (fun p hp => by rw [c p hp]; rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    (rw [if_neg (by simp only [colI0, colI1, colP, colF]; omega)])) hi hl
  rw [zev_gCopy, a, b, d 0 (by decide), d 1 (by decide), d 2 (by decide)]
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> (unfold colI0 colI1 colF; simp)

/-! ## The input state -/

theorem initArr_get {key : List Nat} (hk : key.length = 8) (ctr : Nat) {i : Nat} (hi : i < 16) :
    (initArr key ctr)[i]! =
      if i < 4 then consts.getD i 0 else if i < 12 then key.getD (i - 4) 0
      else if i = 12 then ctr % M32 else if i = 13 then ctr / M32 % M32 else 0 := by
  match key, hk with
  | [k0, k1, k2, k3, k4, k5, k6, k7], _ =>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [initArr, consts]

/-- `K` limbs ranged and counter `< 2^30` on row `r`. -/
def KOk (tr : Trace Fp) (t r : Nat) : Prop :=
  (∀ j, j < 9 → ∀ l, l < 2 → nv tr t r (colK j l) < 65536) ∧ kw tr t r 8 < 2 ^ 30

/-- The input word of slot `i` on row `r`. -/
def inW (tr : Trace Fp) (t r i : Nat) : Nat := (initArr (keyOf tr t r) (kw tr t r 8))[i]!

theorem inW_eq (r : Nat) (hK : KOk tr t r) {i : Nat} (hi : i < 16) :
    inW tr t r i = if i < 4 then consts.getD i 0 else if i < 12 then kw tr t r (i - 4)
      else if i = 12 then kw tr t r 8 else 0 := by
  unfold inW
  rw [initArr_get (keyOf_length r) _ hi]
  have hc := hK.2
  split
  · rfl
  split
  · simp [keyOf, show i - 4 < 8 by omega]
  split
  · unfold M32; omega
  split
  · unfold M32; rw [Nat.div_eq_of_lt (by omega)]
  · rfl

theorem inW_lt (r : Nat) (hK : KOk tr t r) {i : Nat} (hi : i < 16) : inW tr t r i < 2 ^ 32 := by
  rw [inW_eq r hK hi]
  have hk : ∀ j, j < 9 → kw tr t r j < 2 ^ 32 := fun j hj => by
    unfold kw; have := hK.1 j hj 0 (by decide); have := hK.1 j hj 1 (by decide); omega
  have hc : ∀ i, consts.getD i 0 < 2 ^ 32 := fun i => by
    unfold consts
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i by omega) with h | h | h | h | h
    all_goals (try subst h)
    all_goals (try decide)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; decide
  split
  · exact hc i
  split
  · exact hk _ (by omega)
  split
  · exact hk 8 (by decide)
  · decide

theorem zev_initLimb (r : Nat) (hK : KOk tr t r) {i l : Nat} (hi : i < 16) (hl : l < 2) :
    zev (tenv tr t r pub) (initLimb i l) = Lm (inW tr t r i) l := by
  rw [inW_eq r hK hi]
  unfold initLimb Lm
  have hk : ∀ j, j < 9 → ((kw tr t r j / 2 ^ (16 * l)) % 65536) = nv tr t r (colK j l) := by
    intro j hj
    unfold kw; have := hK.1 j hj 0 (by decide); have := hK.1 j hj 1 (by decide)
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> simp <;> omega
  split
  · simp [constLimb]
  split
  · rw [zev_c, cur_eq, hk _ (by omega)]
  split
  · rw [zev_c, cur_eq, hk 8 (by decide)]
  · simp

/-- **The input rows.** -/
theorem init_rows (hL : ChLocal tr t pub) {s : Nat} (hs : s + 2 < tr.height t)
    (h0 : nv tr t s colI0 = 1) (h1 : nv tr t (s + 1) colI1 = 1) :
    KOk tr t s ∧ Ranged tr t (s + 2) ∧ (∀ j l, j < 9 → l < 2 → nv tr t (s + 2) (colK j l) = nv tr t s (colK j l)) ∧
    stA tr t (s + 2) = initArr (keyOf tr t s) (kw tr t s 8) := by
  have hs0 : s < tr.height t := by omega
  have hs1 : s + 1 < tr.height t := by omega
  -- K copies
  have kc1 : ∀ j l, j < 9 → l < 2 → nv tr t (s + 1) (colK j l) = nv tr t s (colK j l) :=
    fun j l hj hl => copyK_of hL hs1 mem_flag_I0 h0 (by decide) hj hl
  have kc2 : ∀ j l, j < 9 → l < 2 → nv tr t (s + 2) (colK j l) = nv tr t (s + 1) (colK j l) :=
    fun j l hj hl => copyK_of hL hs mem_flag_I1 h1 (by decide) hj hl
  -- range checks
  have rI0 : ∀ m l, m < 6 → l < 2 → Lm (xw tr t s m) l = nv tr t s (colK m l) := by
    intro m l hm hl
    have hz := zc hL hs0 (mem_cInit (e := .mul (E.c colI0) (E.sub (E.limb (xb m) l) (E.c (colK m l))))
      (by unfold cInit; apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_left; apply List.mem_append_right
          exact List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩))
    rw [zev_mul, zev_c, cur_eq, h0, zev_sub, zev_limb (bitsX hL hs0 hm) hl, zev_c, cur_eq] at hz
    rw [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at hz
    have := Lm_lt (xw tr t s m) l; have := nv_lt (tr := tr) (t := t) s (colK m l)
    have := hz (by unfold Lm at *; omega) (by unfold Lm at *; omega); unfold Lm; omega
  have rI1 : ∀ m l, m < 3 → l < 2 → Lm (xw tr t (s + 1) m) l = nv tr t (s + 1) (colK (6 + m) l) := by
    intro m l hm hl
    have hz := zc hL hs1 (mem_cInit (e := .mul (E.c colI1) (E.sub (E.limb (xb m) l) (E.c (colK (6 + m) l))))
      (by unfold cInit; apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩))
    rw [zev_mul, zev_c, cur_eq, h1, zev_sub, zev_limb (bitsX hL hs1 (by omega : m < 6)) hl, zev_c, cur_eq] at hz
    rw [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at hz
    have := Lm_lt (xw tr t (s + 1) m) l; have := nv_lt (tr := tr) (t := t) (s + 1) (colK (6 + m) l)
    have := hz (by unfold Lm at *; omega) (by unfold Lm at *; omega); unfold Lm; omega
  have top : ∀ b, b = 30 ∨ b = 31 → nv tr t (s + 1) (colX 2 b) = 0 := by
    intro b hb
    have hz := zc hL hs1 (mem_cInit (e := .mul (E.c colI1) (E.c (colX 2 b)))
      (by unfold cInit; apply List.mem_append_left
          apply List.mem_append_right; rcases hb with rfl | rfl <;> simp))
    rw [zev_mul, zev_c, cur_eq, h1, zev_c, cur_eq] at hz
    rw [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at hz
    have := bX hL hs1 (m := 2) (b := b) (by decide) (by omega)
    have := hz (by omega) (by omega); omega
  have hK : KOk tr t s := by
    refine ⟨fun j hj l hl => ?_, ?_⟩
    · rcases Nat.lt_or_ge j 6 with h6 | h6
      · have := rI0 j l h6 hl; have := Lm_lt (xw tr t s j) l; omega
      · rw [← kc1 j l hj hl, show j = 6 + (j - 6) by omega]
        have := rI1 (j - 6) l (by omega) hl
        have := Lm_lt (xw tr t (s + 1) (j - 6)) l; omega
    · have e0 := rI1 2 0 (by decide) (by decide); have e1 := rI1 2 1 (by decide) (by decide)
      rw [kc1 8 0 (by decide) (by decide)] at e0; rw [kc1 8 1 (by decide) (by decide)] at e1
      unfold kw; unfold Lm at e0 e1
      have hx : xw tr t (s + 1) 2 < 2 ^ 30 := by
        have hb : ∀ b, b < 32 → nv tr t (s + 1) (colX 2 b) ≤ 1 := fun b hb => bX hL hs1 (by decide) hb
        unfold xw
        rw [show (32 : Nat) = 30 + 1 + 1 from rfl, nbits, nbits, show 30 + 1 = 31 from rfl,
          top 30 (by omega), top 31 (by omega)]
        have := nbits_lt (f := fun b => nv tr t (s + 1) (colX 2 b)) (n := 30) (fun b h => hb b (by omega))
        omega
      simp at e0 e1; omega
  -- the state
  have sI0 : ∀ i l, i < 16 → i ≠ 12 → l < 2 → (nv tr t s (colS i l) : Int) = Lm (inW tr t s i) l := by
    intro i l hi h12 hl
    have hz := zc hL hs0 (mem_cInit (e := .mul (E.c colI0) (E.sub (sC i l) (initLimb i l)))
      (by unfold cInit; apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_left; apply List.mem_append_left
          exact List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [h12]⟩,
            List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩))
    rw [zev_mul, zev_c, cur_eq, h0, zev_sub, sC, zev_c, cur_eq, zev_initLimb s hK hi hl] at hz
    rw [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at hz
    have := Lm_lt (inW tr t s i) l; have := nv_lt (tr := tr) (t := t) s (colS i l)
    have := hz (by omega) (by omega); omega
  have s12 : ∀ l, l < 2 → nv tr t (s + 1) (colS 12 l) = nv tr t s (colK 8 l) := by
    intro l hl
    have hz := zc hL hs1 (mem_cInit (e := .mul (E.c colI1) (E.sub (sC 12 l) (E.c (colK 8 l))))
      (by unfold cInit; apply List.mem_append_right
          exact List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))
    rw [zev_mul, zev_c, cur_eq, h1, zev_sub, sC, zev_c, cur_eq, zev_c, cur_eq] at hz
    rw [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at hz
    have := nv_lt (tr := tr) (t := t) (s + 1) (colS 12 l); have := nv_lt (tr := tr) (t := t) (s + 1) (colK 8 l)
    have := hz (by omega) (by omega); rw [← kc1 8 l (by decide) hl]; omega
  have sc1 : ∀ i l, i < 16 → l < 2 → nv tr t (s + 2) (colS i l) = nv tr t (s + 1) (colS i l) :=
    fun i l hi hl => copyS_of hL hs (Or.inr (Or.inl rfl)) h1 hi hl
  have sc0 : ∀ i l, i < 16 → l < 2 → nv tr t (s + 1) (colS i l) = nv tr t s (colS i l) :=
    fun i l hi hl => copyS_of hL hs1 (Or.inl rfl) h0 hi hl
  -- slot values at s + 2
  have hv : ∀ i l, i < 16 → l < 2 → (nv tr t (s + 2) (colS i l) : Int) = Lm (inW tr t s i) l := by
    intro i l hi hl
    rw [sc1 i l hi hl]
    by_cases h12 : i = 12
    · subst h12; rw [s12 l hl, inW_eq s hK (by decide)]
      simp only [show ¬ (12 < 4) by decide, show ¬ (12 < 12) by decide, if_false, if_true]
      unfold Lm kw; have := hK.1 8 (by decide) 0 (by decide); have := hK.1 8 (by decide) 1 (by decide)
      rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> simp <;> omega
    · rw [sc0 i l hi hl]; exact sI0 i l hi h12 hl
  refine ⟨hK, fun i hi l hl => ?_, fun j l hj hl => by rw [kc2 j l hj hl, kc1 j l hj hl], ?_⟩
  · have := hv i l hi hl; have := Lm_lt (inW tr t s i) l; omega
  · apply stA_eq_of (initArr_size (keyOf_length s) _)
    intro i hi
    have e0 := hv i 0 hi (by decide); have e1 := hv i 1 hi (by decide)
    have := word_limbs (inW_lt s hK hi)
    unfold Lm at e0 e1; unfold sw; unfold inW at *
    omega

end ZkFormal.Chacha.Sound
