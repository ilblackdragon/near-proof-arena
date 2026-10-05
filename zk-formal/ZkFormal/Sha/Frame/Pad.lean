import ArenaCore

/-!
# ZkFormal.Sha.Frame.Pad — the padding argument, on plain `Nat` data

`pad_of_frame`: per-byte data flags `FL g` and bytes `BY g` over `k` blocks of
64 bytes, together with the block flags `seen/p80/last` and the local rules the
SHA table enforces, force the byte stream to be FIPS 180-4 `pad m` of the data
bytes `m`.  No trace appears here; ZkFormal.Sha.Frame.Frame instantiates it.
-/

namespace ZkFormal.Sha.Frame

open ArenaCore

/-- The local framing rules (`g = 64 i + kk`, `kk < 64`, `i < k`). -/
structure FrameRules (k L : Nat) (FL BY : Nat → Nat) (seen p80 last : Nat → Bool) : Prop where
  fl_le : ∀ g, g < 64 * k → FL g ≤ 1
  by_lt : ∀ g, g < 64 * k → BY g < 256
  mono : ∀ i kk, i < k → kk + 1 < 64 → FL (64 * i + kk + 1) ≤ FL (64 * i + kk)
  /-- non-data bytes: `0x80` right after the data of a `p80` block, else `0`
  (except the length bytes `56..63` of the last block) -/
  byte : ∀ i kk, i < k → kk < 64 → FL (64 * i + kk) = 0 → (kk < 56 ∨ last i = false) →
    BY (64 * i + kk) =
      if p80 i = true ∧ (kk = 0 ∨ FL (64 * i + kk - 1) = 1) then 128 else 0
  p80_end : ∀ i, i < k → p80 i = true → FL (64 * i + 63) = 0
  full : ∀ i, i < k → seen i = false → p80 i = false → FL (64 * i + 63) = 1
  seen_start : ∀ i, i < k → seen i = true → FL (64 * i) = 0
  not_both : ∀ i, i < k → ¬ (seen i = true ∧ p80 i = true)
  last_done : ∀ i, i < k → last i = true → (seen i = true ∨ p80 i = true)
  seen_last : ∀ i, i < k → seen i = true → last i = true
  last_56 : ∀ i, i < k → last i = true → FL (64 * i + 56) = 0
  last_55 : ∀ i, i < k → last i = true → p80 i = true → FL (64 * i + 55) = 0
  pn_55 : ∀ i, i < k → p80 i = true → last i = false → FL (64 * i + 55) = 1
  seen0 : seen 0 = false
  seen_succ : ∀ i, i + 1 < k → seen (i + 1) = (seen i || p80 i)
  last_iff : ∀ i, i < k → (last i = true ↔ i + 1 = k)
  /-- `L` is the number of data bytes -/
  count : L = ((List.range (64 * k)).filter fun g => FL g = 1).length
  /-- length bytes of the last block: big-endian 64-bit `8·L` -/
  len : ∀ j, j < 8 → BY (64 * k - 8 + j) = 8 * L / 256 ^ (7 - j) % 256
  k_pos : 0 < k

/-! ## A monotone 0/1 sequence is an indicator of a prefix -/

theorem prefix_of_mono (N : Nat) (f : Nat → Nat) (hle : ∀ g, g < N → f g ≤ 1)
    (hmono : ∀ g, g + 1 < N → f (g + 1) ≤ f g) :
    ∀ g, g < N → (f g = 1 ↔ g < ((List.range N).filter fun g => f g = 1).length) := by
  induction N with
  | zero => intro g h; omega
  | succ N ih =>
    intro g hg
    have ih' := ih (fun g h => hle g (by omega)) (fun g h => hmono g (by omega))
    have hcnt : ((List.range N).filter fun g => f g = 1).length ≤ N := by
      have := List.length_filter_le (fun g => decide (f g = 1)) (List.range N)
      simpa using this
    rw [List.range_succ, List.filter_append]
    by_cases hN : f N = 1
    · -- all earlier values are 1
      have hall : ∀ g, g ≤ N → f g = 1 := by
        intro g hgN
        have : ∀ d, ∀ g, g + d = N → f g = 1 := by
          intro d
          induction d with
          | zero => intro g h; rw [show g = N by omega]; exact hN
          | succ d ihd =>
            intro g h
            have h1 := ihd (g + 1) (by omega)
            have h2 := hmono g (by omega)
            have h3 := hle g (by omega)
            omega
        exact this (N - g) g (by omega)
      have hf : (List.range N).filter (fun g => f g = 1) = List.range N := by
        rw [List.filter_eq_self]; intro a ha; simp at ha; simp [hall a (by omega)]
      simp [hf, hN, hall g (by omega)]
      omega
    · have hf : [N].filter (fun g => f g = 1) = [] := by simp [hN]
      rw [hf, List.append_nil]
      by_cases hgN : g < N
      · exact ih' g hgN
      · have : g = N := by omega
        subst this; simp [hN]; omega

/-! ## Big-endian bytes -/

theorem beN_getElem (w n j : Nat) (hj : j < w) :
    ((Bytes.beN w n)[j]'(by rw [Bytes.beN_length]; exact hj)).toNat = n / 256 ^ (w - 1 - j) % 256 := by
  induction w generalizing n j with
  | zero => omega
  | succ w ih =>
    simp only [Bytes.beN]
    by_cases hjw : j < w
    · rw [List.getElem_append_left (by rw [Bytes.beN_length]; exact hjw), ih (n / 256) j hjw]
      rw [Nat.div_div_eq_div_mul, show w + 1 - 1 - j = (w - 1 - j) + 1 by omega, Nat.pow_succ,
        Nat.mul_comm 256]
    · have : j = w := by omega
      subst this
      rw [List.getElem_append_right (by rw [Bytes.beN_length]; omega)]
      simp

/-! ## The padding theorem -/

section
variable {k L : Nat} {FL BY : Nat → Nat} {seen p80 last : Nat → Bool}

theorem FrameRules.mono_global (hR : FrameRules k L FL BY seen p80 last) :
    ∀ g, g + 1 < 64 * k → FL (g + 1) ≤ FL g := by
  intro g hg
  have hi : g / 64 < k := by omega
  by_cases hkk : g % 64 + 1 < 64
  · have := hR.mono (g / 64) (g % 64) hi hkk
    rwa [show 64 * (g / 64) + g % 64 = g by omega] at this
  · -- block boundary: g = 64 i + 63
    have hle := hR.fl_le g (by omega)
    have hle' := hR.fl_le (g + 1) hg
    by_cases h1 : FL (g + 1) = 1
    · have hi1 : (g + 1) / 64 < k := by omega
      have hs := hR.seen_succ (g / 64) (by omega)
      rw [show g / 64 + 1 = (g + 1) / 64 by omega] at hs
      cases hsn : seen ((g + 1) / 64)
      · rw [hsn] at hs
        have h2 : seen (g / 64) = false := by
          cases h : seen (g / 64) <;> simp_all
        have h3 : p80 (g / 64) = false := by
          cases h : p80 (g / 64) <;> simp_all
        have := hR.full (g / 64) hi h2 h3
        rw [show 64 * (g / 64) + 63 = g by omega] at this
        omega
      · have := hR.seen_start _ hi1 hsn
        rw [show 64 * ((g + 1) / 64) = g + 1 by omega] at this
        omega
    · omega

theorem FrameRules.fl_iff (hR : FrameRules k L FL BY seen p80 last) :
    ∀ g, g < 64 * k → (FL g = 1 ↔ g < L) := by
  intro g hg
  rw [hR.count]
  exact prefix_of_mono (64 * k) FL hR.fl_le hR.mono_global g hg

theorem FrameRules.L_lt (hR : FrameRules k L FL BY seen p80 last) : L ≤ 64 * (k - 1) + 56 := by
  have hk := hR.k_pos
  have h56 := hR.last_56 (k - 1) (by omega) ((hR.last_iff (k - 1) (by omega)).2 (by omega))
  have := hR.fl_iff (64 * (k - 1) + 56) (by omega)
  rw [h56] at this
  simp at this
  omega

theorem FrameRules.seen_false (hR : FrameRules k L FL BY seen p80 last) :
    ∀ i, i < k → i ≤ L / 64 → seen i = false := by
  intro i
  induction i with
  | zero => intro _ _; exact hR.seen0
  | succ i ih =>
    intro hi hiL
    rw [hR.seen_succ i hi, ih (by omega) (by omega)]
    cases h : p80 i
    · rfl
    · have := hR.p80_end i (by omega) h
      have h2 := (hR.fl_iff (64 * i + 63) (by omega)).2 (by omega)
      omega

theorem FrameRules.p80_drop (hR : FrameRules k L FL BY seen p80 last) : p80 (L / 64) = true := by
  have hL := hR.L_lt
  have hk := hR.k_pos
  have hp : L / 64 < k := by omega
  cases h : p80 (L / 64)
  · have := hR.full _ hp (hR.seen_false _ hp (Nat.le_refl _)) h
    have h2 := (hR.fl_iff (64 * (L / 64) + 63) (by omega)).1 this
    omega
  · rfl

theorem FrameRules.seen_true (hR : FrameRules k L FL BY seen p80 last) :
    ∀ i, i < k → L / 64 < i → seen i = true := by
  intro i
  induction i with
  | zero => intro _ h; omega
  | succ i ih =>
    intro hi hiL
    rw [hR.seen_succ i hi]
    by_cases hi' : L / 64 < i
    · rw [ih (by omega) hi']; rfl
    · have : i = L / 64 := by omega
      subst this; rw [hR.p80_drop]; simp

theorem FrameRules.p80_iff (hR : FrameRules k L FL BY seen p80 last) :
    ∀ i, i < k → (p80 i = true ↔ i = L / 64) := by
  intro i hi
  constructor
  · intro h
    by_cases h1 : i < L / 64
    · have := hR.p80_end i hi h
      have h2 := (hR.fl_iff (64 * i + 63) (by omega)).2 (by omega)
      omega
    by_cases h2 : L / 64 < i
    · exact absurd ⟨hR.seen_true i hi h2, h⟩ (hR.not_both i hi)
    omega
  · intro h; subst h; exact hR.p80_drop

/-- Either the drop block is the last block (`L mod 64 ≤ 55`) or the last
block follows it (`L mod 64 ≥ 56`). -/
theorem FrameRules.shape (hR : FrameRules k L FL BY seen p80 last) :
    (k = L / 64 + 1 ∧ L % 64 ≤ 55) ∨ (k = L / 64 + 2 ∧ 56 ≤ L % 64) := by
  have hL := hR.L_lt
  have hk := hR.k_pos
  have hp : L / 64 < k := by omega
  have hk2 : k ≤ L / 64 + 2 := by
    by_cases h : L / 64 + 1 < k
    · have := hR.seen_last _ h (hR.seen_true _ h (by omega))
      have := (hR.last_iff _ h).1 this
      omega
    · omega
  by_cases h : k = L / 64 + 1
  · left
    refine ⟨h, ?_⟩
    have hl := (hR.last_iff (L / 64) hp).2 (by omega)
    have := hR.last_55 _ hp hl hR.p80_drop
    have h2 := hR.fl_iff (64 * (L / 64) + 55) (by omega)
    rw [this] at h2; simp at h2; omega
  · right
    refine ⟨by omega, ?_⟩
    have hl : last (L / 64) = false := by
      cases h' : last (L / 64)
      · rfl
      · have := (hR.last_iff _ hp).1 h'; omega
    have := hR.pn_55 _ hp hR.p80_drop hl
    have h2 := (hR.fl_iff (64 * (L / 64) + 55) (by omega)).1 this
    omega

/-- Bytes after the data. -/
theorem FrameRules.by_after (hR : FrameRules k L FL BY seen p80 last) :
    ∀ g, L ≤ g → g < 64 * k - 8 → BY g = if g = L then 128 else 0 := by
  intro g hg1 hg2
  have hk := hR.k_pos
  have hi : g / 64 < k := by omega
  have hfl : FL g = 0 := by
    have := hR.fl_le g (by omega)
    have h2 := hR.fl_iff g (by omega)
    omega
  have hcond : g % 64 < 56 ∨ last (g / 64) = false := by
    by_cases h : g / 64 + 1 = k
    · left; omega
    · right
      cases h' : last (g / 64)
      · rfl
      · exact absurd ((hR.last_iff _ hi).1 h') h
  have hb := hR.byte (g / 64) (g % 64) hi (by omega)
    (by rwa [show 64 * (g / 64) + g % 64 = g by omega]) hcond
  rw [show 64 * (g / 64) + g % 64 = g by omega] at hb
  rw [hb]
  by_cases hgL : g = L
  · subst hgL
    simp only [ite_true]
    rw [if_pos]
    refine ⟨hR.p80_drop, ?_⟩
    by_cases h0 : g % 64 = 0
    · exact Or.inl h0
    · right
      exact (hR.fl_iff (g - 1) (by omega)).2 (by omega)
  · simp only [hgL, ite_false]
    rw [if_neg]
    rintro ⟨hp, h0⟩
    have := (hR.p80_iff _ hi).1 hp
    rcases h0 with h0 | h0
    · omega
    · have := (hR.fl_iff (g - 1) (by omega)).1 h0
      omega

theorem filterMap_eq_map_of {f : Nat → Option Nat} {h : Nat → Nat} :
    ∀ (l : List Nat), (∀ x ∈ l, f x = some (h x)) → l.filterMap f = l.map h
  | [], _ => rfl
  | x :: xs, hx => by
    rw [List.filterMap_cons, hx x (List.mem_cons_self ..), List.map_cons,
      filterMap_eq_map_of xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

theorem range_map_append (f : Nat → Nat) (a b : Nat) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun i => f (a + i)) := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

/-- The data bytes are the first `L` bytes. -/
theorem FrameRules.data_eq (hR : FrameRules k L FL BY seen p80 last) :
    ((List.range (64 * k)).filterMap fun g => if FL g = 1 then some (BY g) else none) =
      (List.range L).map BY := by
  have hL := hR.L_lt
  rw [show 64 * k = L + (64 * k - L) by omega, List.range_add, List.filterMap_append]
  have e1 : (List.range L).filterMap (fun g => if FL g = 1 then some (BY g) else none) =
      (List.range L).map BY := by
    apply filterMap_eq_map_of
    intro g hg; simp at hg
    simp [(hR.fl_iff g (by omega)).2 hg]
  have e2 : ((List.range (64 * k - L)).map (L + ·)).filterMap
      (fun g => if FL g = 1 then some (BY g) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro g hg; simp at hg
    obtain ⟨a, ha, rfl⟩ := hg
    have hne : FL (L + a) ≠ 1 := by intro h; have := (hR.fl_iff (L + a) (by omega)).1 h; omega
    simp [hne]
  rw [e1, e2, List.append_nil]

/-- **Padding.** The byte stream of the blocks is `pad` of the data bytes. -/
theorem pad_of_frame (hR : FrameRules k L FL BY seen p80 last) :
    SHA256.pad ((List.range (64 * k)).filterMap fun g => if FL g = 1 then some (BY g) else none) =
      (List.range (64 * k)).map BY ∧
    ((List.range (64 * k)).filterMap fun g => if FL g = 1 then some (BY g) else none).length = L := by
  have hL := hR.L_lt
  have hk := hR.k_pos
  have hshape := hR.shape
  -- the data bytes are the first L bytes
  have hm : ((List.range (64 * k)).filterMap fun g => if FL g = 1 then some (BY g) else none) =
      (List.range L).map BY := by
    rw [show 64 * k = L + (64 * k - L) by omega, List.range_add, List.filterMap_append]
    have e1 : (List.range L).filterMap (fun g => if FL g = 1 then some (BY g) else none) =
        (List.range L).map BY := by
      apply filterMap_eq_map_of
      intro g hg; simp at hg
      simp [(hR.fl_iff g (by omega)).2 hg]
    have e2 : ((List.range (64 * k - L)).map (L + ·)).filterMap
        (fun g => if FL g = 1 then some (BY g) else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro g hg; simp at hg
      obtain ⟨a, ha, rfl⟩ := hg
      have := (hR.fl_iff (L + a) (by omega))
      have := hR.fl_le (L + a) (by omega)
      have hne : FL (L + a) ≠ 1 := by intro h; have := (hR.fl_iff (L + a) (by omega)).1 h; omega
      simp [hne]
    rw [e1, e2, List.append_nil]
  rw [hm, List.length_map, List.length_range]
  refine ⟨?_, rfl⟩
  -- z zero bytes, then the length
  have hz : L + 1 + (119 - L % 64) % 64 + 8 = 64 * k := by omega
  simp only [SHA256.pad, List.length_map, List.length_range]
  rw [← hz, range_map_append, range_map_append, range_map_append]
  congr 1
  congr 1
  congr 1
  · -- the 0x80 byte
    simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
    have := hR.by_after L (Nat.le_refl _) (by omega)
    simp at this; rw [this]
  · apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_replicate, List.getElem_map, List.getElem_range]
      have := hR.by_after (L + 1 + j) (by omega) (by simp at h1; omega)
      rw [this, if_neg (by omega)]
  · apply List.ext_getElem
    · simp [Bytes.beN_length]
    · intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      simp only [List.length_map, Bytes.beN_length] at h1
      rw [beN_getElem 8 (8 * L) j h1]
      have := hR.len j h1
      rw [show 64 * k - 8 + j = L + 1 + (119 - L % 64) % 64 + j by omega] at this
      rw [this]

end

end ZkFormal.Sha.Frame
