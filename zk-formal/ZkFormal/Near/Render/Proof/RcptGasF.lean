import ZkFormal.Near.Render.Proof.RcptNat

/-!
# ZkFormal.Near.Render.Proof.RcptGasF — the `GP` arithmetic of the generator (pure `Nat`)

Under `GasOk d bg B` (numeric facts of a receipt's gas data: `bg` are the bytes of
the block gas price `B`, the spec's `burnt`/`ramt`/`ge`/`hr`, no overflow):

* `gp − bgp` with borrow: digits `gdv`, final borrow `[gp < bgp]`;
* `p = min gp bgp` and the surplus as bytes (`pB_eq`, `surB_eq`), both `< 256^12`;
* `burnt = G·p`, `ramt = G·surplus`, tokens `tok0 + burnt` byte by byte, no
  final carry (`sb_*`, `sr_*`, `tt_*`).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen

/-- Numeric facts of a receipt's gas data. -/
structure GasOk (d : RD) (bg : Nat → Nat) (B : Nat) : Prop where
  bg : ∀ i, bg i = (leBytes 16 B).getD i 0
  B_lt : B < 256 ^ 16
  gp_lt : d.gp < 256 ^ 16
  ge : d.ge = decide (B ≤ d.gp)
  burnt : d.burnt = Params.G * min d.gp B
  burnt_lt : d.burnt < 256 ^ 16
  ramt : d.ramt = Params.G * (d.gp - min d.gp B)
  ramt_lt : d.ramt < 256 ^ 16
  tok_lt : d.tok0 + d.burnt < 256 ^ 16
  hr : d.hr = decide (d.ramt ≠ 0)

theorem G_val : Params.G = 223182562500 := rfl

/-- `(G_LE.take 5)` as a convolution kernel: `Σ g_j 256^j V v (n − j)`. -/
theorem V_convG (v : Nat → Nat) (n : Nat) : V (conv (Rcpt.G_LE.take 5) v) n =
    196 * V v n + 164 * 256 * V v (n - 1) + 183 * 65536 * V v (n - 2) + 246 * 16777216 * V v (n - 3) +
      51 * 4294967296 * V v (n - 4) := by
  rw [V_conv]; simp [sumR, Rcpt.G_LE]

theorem convG_le (v : Nat → Nat) (hv : ∀ i, v i ≤ 255) (i : Nat) : conv (Rcpt.G_LE.take 5) v i ≤ 214200 :=
  Nat.le_trans (conv_le _ v hv i) (by simp [sumR, Rcpt.G_LE])

section
variable {d : RD} {bg : Nat → Nat} {B : Nat} (h : GasOk d bg B)
include h

theorem gpB_lt (i : Nat) : Seg.gpB d i < 256 := leBytes_getD_lt _ _ _
theorem bg_lt (i : Nat) : bg i < 256 := by rw [h.bg]; exact leBytes_getD_lt _ _ _

theorem V_gpB : V (Seg.gpB d) 16 = d.gp := V_leBytes_of (Nat.le_refl _) h.gp_lt
theorem V_bg : V bg 16 = B := by
  rw [V_congr (y := fun i => (leBytes 16 B).getD i 0) 16 (fun i _ => h.bg i)]
  exact V_leBytes_of (Nat.le_refl _) h.B_lt

theorem gbr_lt (i : Nat) : Seg.gbr d bg i ≤ 1 := bchain_le _ _ _ i (by decide)
theorem gdv_lt (i : Nat) : Seg.gdv d bg i < 256 := bdig_lt _ _ _ (gpB_lt h) (bg_lt h) (by decide) i

/-- One digit of `gp − bgp`. -/
theorem gdv_step (i : Nat) :
    Seg.gpB d i + 256 * Seg.gbr d bg (i + 1) = bg i + Seg.gbr d bg i + Seg.gdv d bg i :=
  (bdig_step _ _ _ (gpB_lt h) (bg_lt h) (by decide) i).1

theorem gbr_zero : Seg.gbr d bg 0 = 0 := rfl

/-- The final borrow is `¬ ge`. -/
theorem gbr_final : Seg.gbr d bg 16 = b2n (!d.ge) := by
  have := bchain_final (Seg.gpB d) bg 0 (gpB_lt h) (bg_lt h) (by decide) 16
  rw [V_gpB h, V_bg h] at this
  simp only [Seg.gbr, this, h.ge]
  by_cases hb : B ≤ d.gp <;> simp [hb, b2n] <;> omega

theorem burnt_eq : d.burnt = Params.G * min d.gp B := h.burnt

/-- `p` as bytes. -/
theorem pB_eq (i : Nat) : Seg.pB d bg i = (leBytes 16 (min d.gp B)).getD i 0 := by
  simp only [Seg.pB, h.ge]
  by_cases hb : B ≤ d.gp
  · simp only [hb, decide_true, ↓reduceIte, h.bg, Nat.min_eq_right hb]
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, Seg.gpB, Nat.min_eq_left (by omega : d.gp ≤ B)]

theorem p_lt : min d.gp B < 256 ^ 12 := by
  have h1 := h.burnt_lt; rw [h.burnt, G_val] at h1
  have : (256 : Nat) ^ 16 = 340282366920938463463374607431768211456 := by decide
  have : (256 : Nat) ^ 12 = 79228162514264337593543950336 := by decide
  omega

theorem sur_lt : d.gp - min d.gp B < 256 ^ 12 := by
  have h1 := h.ramt_lt; rw [h.ramt, G_val] at h1
  have : (256 : Nat) ^ 16 = 340282366920938463463374607431768211456 := by decide
  have : (256 : Nat) ^ 12 = 79228162514264337593543950336 := by decide
  omega

theorem pB_lt (i : Nat) : Seg.pB d bg i < 256 := by rw [pB_eq h]; exact leBytes_getD_lt _ _ _

theorem pB_hi {i : Nat} (hi : 12 ≤ i) : Seg.pB d bg i = 0 := by
  rw [pB_eq h, leBytes_getD]
  split
  · have := p_lt h
    have : 256 ^ 12 ≤ 256 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.div_eq_of_lt (by omega)]
  · rfl

theorem V_pB {k : Nat} (hk : 12 ≤ k) : V (Seg.pB d bg) k = min d.gp B := by
  rw [V_congr (y := fun i => (leBytes 16 (min d.gp B)).getD i 0) k (fun i _ => pB_eq h i), V_leBytes]
  apply Nat.mod_eq_of_lt
  have := p_lt h
  have : 256 ^ 12 ≤ 256 ^ (min k 16) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The surplus `gp − p` as bytes (digits of `gp − bgp` when `ge`). -/
theorem surB_eq {i : Nat} (hi : i < 16) : Seg.surB d bg i = (leBytes 16 (d.gp - min d.gp B)).getD i 0 := by
  simp only [Seg.surB, h.ge]
  by_cases hb : B ≤ d.gp
  · simp only [hb, decide_true, ↓reduceIte, Nat.min_eq_right hb]
    have hV := V_bdig (Seg.gpB d) bg 0 (gpB_lt h) (bg_lt h) (by decide) (n := 16) (by rw [V_gpB h, V_bg h]; omega)
    rw [V_gpB h, V_bg h, Nat.sub_zero] at hV
    rw [leBytes_getD, if_pos hi, ← hV]
    exact (V_digit _ (gdv_lt h) hi).symm
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left (by omega : d.gp ≤ B),
      Nat.sub_self, leBytes_getD, Nat.zero_div, Nat.zero_mod, ite_self]

theorem surB_lt (i : Nat) : Seg.surB d bg i < 256 := by
  simp only [Seg.surB]; split
  · exact gdv_lt h i
  · omega

theorem surB_hi {i : Nat} (hi : 12 ≤ i) (hi' : i < 16) : Seg.surB d bg i = 0 := by
  rw [surB_eq h hi', leBytes_getD, if_pos hi']
  have := sur_lt h
  have : 256 ^ 12 ≤ 256 ^ i := Nat.pow_le_pow_right (by decide) hi
  rw [Nat.div_eq_of_lt (by omega)]

theorem V_surB {k : Nat} (hk : 12 ≤ k) (hk' : k ≤ 16) : V (Seg.surB d bg) k = d.gp - min d.gp B := by
  rw [V_congr (y := fun i => (leBytes 16 (d.gp - min d.gp B)).getD i 0) k (fun i hi => surB_eq h (by omega)),
    V_leBytes]
  apply Nat.mod_eq_of_lt
  have := sur_lt h
  have : 256 ^ 12 ≤ 256 ^ (min k 16) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ## `burnt = G·p` -/

theorem V_x2 : V (Seg.x2 d bg) 16 = d.burnt := by
  simp only [Seg.x2]
  rw [V_convG, V_pB h (by omega), V_pB h (by omega), V_pB h (by omega), V_pB h (by omega), V_pB h (by omega),
    h.burnt, G_val]
  omega

theorem sb_mod {i : Nat} (hi : i < 16) : Seg.sb d bg i % 256 = (leBytes 16 d.burnt).getD i 0 :=
  chain_byte _ hi (V_x2 h)

theorem x2_le (i : Nat) : Seg.x2 d bg i ≤ 214200 :=
  convG_le _ (fun i => Nat.le_of_lt_succ (pB_lt h i)) i

theorem c2_le (i : Nat) : chain (Seg.x2 d bg) i ≤ 840 :=
  chain_le _ (fun j => by have := x2_le h j; omega) i

theorem sb_div (i : Nat) : Seg.sb d bg i / 256 = chain (Seg.x2 d bg) (i + 1) := by
  simp only [Seg.sb, chain]

theorem c2_final : chain (Seg.x2 d bg) 16 = 0 := chain_zero_of _ (by rw [V_x2 h]; exact h.burnt_lt)

/-! ## `ramt = G·surplus` -/

theorem V_x3 : V (Seg.x3 d bg) 16 = d.ramt := by
  simp only [Seg.x3]
  rw [V_convG]
  rw [V_surB h (by omega) (by omega), V_surB h (by omega) (by omega), V_surB h (by omega) (by omega),
    V_surB h (by omega) (by omega), V_surB h (by omega) (by omega), h.ramt, G_val]
  omega

theorem sr_mod {i : Nat} (hi : i < 16) : Seg.sr d bg i % 256 = (leBytes 16 d.ramt).getD i 0 :=
  chain_byte _ hi (V_x3 h)

theorem x3_le (i : Nat) : Seg.x3 d bg i ≤ 214200 :=
  convG_le _ (fun i => Nat.le_of_lt_succ (surB_lt h i)) i

theorem c3_le (i : Nat) : chain (Seg.x3 d bg) i ≤ 840 :=
  chain_le _ (fun j => by have := x3_le h j; omega) i

theorem sr_div (i : Nat) : Seg.sr d bg i / 256 = chain (Seg.x3 d bg) (i + 1) := by
  simp only [Seg.sr, chain]

theorem c3_final : chain (Seg.x3 d bg) 16 = 0 := chain_zero_of _ (by rw [V_x3 h]; exact h.ramt_lt)

/-! ## Tokens -/

theorem V_x4 : V (Seg.x4 d bg) 16 = d.tok0 + d.burnt := by
  rw [V_congr (y := fun i => (leBytes 16 d.tok0).getD i 0 + (leBytes 16 d.burnt).getD i 0) 16
    (fun i hi => by simp only [Seg.x4, Seg.tokOld, sb_mod h hi]), V_add,
    V_leBytes_of (Nat.le_refl _) (by have := h.tok_lt; omega),
    V_leBytes_of (Nat.le_refl _) h.burnt_lt]

theorem tt_mod {i : Nat} (hi : i < 16) : Seg.tt d bg i % 256 = Seg.tokNew d i :=
  chain_byte _ hi (V_x4 h)

theorem x4_le (i : Nat) : Seg.x4 d bg i ≤ 510 := by
  simp only [Seg.x4, Seg.tokOld]
  have := leBytes_getD_lt 16 d.tok0 i; have := Nat.mod_lt (Seg.sb d bg i) (show 0 < 256 by decide)
  omega

theorem c4_le (i : Nat) : chain (Seg.x4 d bg) i ≤ 1 :=
  chain_le _ (fun j => by have := x4_le h j; omega) i

theorem tt_div (i : Nat) : Seg.tt d bg i / 256 = chain (Seg.x4 d bg) (i + 1) := by
  simp only [Seg.tt, chain]

theorem c4_final : chain (Seg.x4 d bg) 16 = 0 := chain_zero_of _ (by rw [V_x4 h]; exact h.tok_lt)

/-! ## Refund flag -/

/-- Without a refund the surplus digits vanish. -/
theorem gdv_noref (hr : d.hr = false) (hge : d.ge = true) {i : Nat} (hi : i < 16) : Seg.gdv d bg i = 0 := by
  have := surB_eq h hi
  simp only [Seg.surB, hge, ↓reduceIte] at this
  rw [this, leBytes_getD, if_pos hi]
  have hr' := h.hr; rw [hr] at hr'
  simp only [false_eq_decide_iff, ne_eq, Decidable.not_not] at hr'
  rw [h.ramt, G_val] at hr'
  have : d.gp - min d.gp B = 0 := by omega
  rw [this]; simp

/-- With a refund some surplus digit is nonzero. -/
theorem gdv_ref (hr : d.hr = true) : runSum (Seg.gdv d bg) 15 ≠ 0 := by
  intro h0
  have hz := runSum_eq0 _ 15 h0
  have hr' := h.hr; rw [hr] at hr'
  simp only [true_eq_decide_iff, ne_eq] at hr'
  rw [h.ramt] at hr'
  have hge : B ≤ d.gp := by
    apply Classical.byContradiction; intro hn
    rw [Nat.min_eq_left (by omega)] at hr'; simp at hr'
  have hV := V_bdig (Seg.gpB d) bg 0 (gpB_lt h) (bg_lt h) (by decide) (n := 16) (by rw [V_gpB h, V_bg h]; omega)
  rw [V_gpB h, V_bg h, V_zero (bdig (Seg.gpB d) bg 0) 16 (fun i hi => hz i (by omega))] at hV
  rw [Nat.min_eq_right hge] at hr'
  apply hr'; rw [show d.gp - B = 0 by omega]; rfl

theorem runSum_gdv_lt (i : Nat) (hi : i < 16) : runSum (Seg.gdv d bg) i < 4096 := by
  have := runSum_le (Seg.gdv d bg) (M := 255) (fun j => Nat.le_of_lt_succ (gdv_lt h j)) i
  have : (i + 1) * 255 ≤ 16 * 255 := Nat.mul_le_mul_right _ (by omega)
  omega

end

end RcptP

end ZkFormal.Near.Render
