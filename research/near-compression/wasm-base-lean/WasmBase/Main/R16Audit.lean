import WasmBase.Main.SegRows
import WasmBase.Main.M2RegAbsentFacts
/-!
# WasmBase.Main.R16Audit — what a scaled R16 query `r16 (2^k · x)` actually bounds

An R16 query proves `(2^k·x mod P) < 2^16`, **not** `x < 2^(16−k)`: `P = 15·2^27 + 1 ≡ 1 (mod 2^27)`,
so `x = (P + 2^k − 1)/2^k` has `2^k·x ≡ 2^k − 1` (`scaled_counterexample`, for every `k` used).
Each use is therefore sound only through **how `x` is consumed**.  Four patterns cover every use in
the AIRs (`docs`: the table at the end of this header).

1. **Exact** (`scaled_exact`): `x` is also bounded some other way (`r16 x`, or `x` equals a small
   expression), so `2^k·x < P` and the query is the intended `x < 2^(16−k)`.
2. **Combined** (`combined_sound`): only `lo + 2^16·x` is used, with `r16 lo`.  Then
   `2^16·x = 2^(16−k)·(2^k·x) ≡ 2^(16−k)·u` with `u < 2^16` (`big_of_r16`), so the combined value is
   a natural `< 2^16 + 2^(32−k)` — the intended range plus `2^16`.  The decomposition `(lo, x)` is not
   canonical, but every consumer compares the combined value, which stays far below `P`.
3. **Time check** (`timeChk_sound`): `timeChk ts tp hi` (`r16 (ts − tp − 1 − 2^16·hi)`,
   `r16 (4·hi)`) with `hi` arbitrary still gives `tp < ts` for `ts, tp < 2^29` (pattern 2 with
   `k = 2`: the difference is `< 2^16 + 2^30 < P − 2^29`).
4. **Sign split** (`sign_split_sound`): `top = 2^m·s + r` with `s` a bit, `top < 2^(m+1)` and
   `r16 (2^(16−m)·r)`: a negative `r` would make `2^(16−m)·r ≡ P − 2^(16−m)·(2^m − top) > 2^16`,
   so `s = top / 2^m` and `r = top % 2^m`.

| AIR use | query | consumer | verdict |
|---|---|---|---|
| every `timeChk` (all chips, REG `hp`, REG' `mhp`, HOSTB, IF, M3) | `4·hi` | `ts − tp − 1 − 2^16·hi` | sound, pattern 3 |
| REG-A `atp ≤ ts` | `4·ahp` | `ts − atp − 2^16·ahp` | sound (`time_le_of_r16`, `hp` arbitrary) |
| MEMINIT `ghi`, `ahi`, `mhi`, `dhi` | `32·x` | `lo + 2^16·x` only | sound, pattern 2: values `< 2^27 + 2^16` (not `< 2^27`); `ad < pubMem` and the gaps are exact comparisons |
| LOAD / STORE `e1` | `32·e1` | `e1 = a1 + off1 + cyE` | sound, pattern 1: `e1` equals a value `< 2^17 + 1` (`load_e1_sound`), given the stack/record limbs `< 2^16` |
| LOAD `low7` | `512·low7` | `topB = 128·sbit + low7` | sound, pattern 4 (`m = 7`) |
| CMP `ra`, `rb`; DIV `ra`, `rb`, `rq`; CONV `rl` | `2·r` | `top = 2^15·s + r` | sound, pattern 4 (`m = 15`), given `top < 2^16` (a stack limb) |
| CALL `n1`, `sbn1`, `ts1`; RET `n1` | `4·n1`, `16·x` | also `r16 x` | sound, pattern 1 |
| REG' / HOSTB `ptrHi` | `32·ptrHi` | `ptr + 2^16·ptrHi` only | sound, pattern 2: base `< 2^27 + 2^16` |
| M3 `n1`, `e1`, GINIT `ghi`/`dhi`/`ehi` | `32·x` | also `r16 x` | sound, pattern 1 |
| SegAir CUTO `chi` | `8·chi` | `space − 16 = clo + 2^16·chi` only | sound, pattern 2: cid `< 2^29 + 2^16` |
| SegAir CUTO `dhi`, `rhi` | `8·dhi`, `16·rhi` | order differences | sound, pattern 2 (`cut_order`, `cut_rec_order` take `dhi`, `rhi : F`) |
| SegAir CUT `hi_k` | `4·hi_k` | `F_k = lo + 2^16·hi`, and `hi_k` is a SHA limb | sound given the chip's limb range `hi < 2^21` (`cut_hi`) |
| SegAir MEMB split `s5`, `s2` | `8192·s5`, `1024·s2` | the data limbs | **unsound without the byte query** (`memb_split_counterexample`); fixed by `byteQ s5 s2` |
| SegAir CUT padding `gl` | `32·gl` | the length limb `1024·gl` and `gi = gl + 2048·gh` | **not as intended** (`gl_padding_counterexample`): `gi = 1` with `gh = 30720` and `gl ≡ 1 − 2048·30720` passes, and the padding block then encodes the length `1056 + 2^21·30720` instead of `1024`, so the digest is not the standard SHA-384 of the stream.  Fix: add `r16 gl`. |
-/

namespace WasmBase

open ZkFormal.Algebra Chips
set_option maxRecDepth 100000

/-- **`r16 (2^k·x)` does not bound `x`**: `x = (P + 2^k − 1)/2^k` passes for every scale used
(`k = 1, 2, 3, 4, 5, 9`), with `x ≥ 2^16`. -/
theorem scaled_counterexample :
    ∀ k ∈ [1, 2, 3, 4, 5, 9],
      let x := (P + 2 ^ k - 1) / 2 ^ k
      (((2 ^ k : Nat) : F) * ((x : Nat) : F)).toNat = 2 ^ k - 1 ∧ 2 ^ 16 ≤ x ∧ x < P := by
  rw [P_val]; decide

/-- **Pattern 1 (exact).**  If `2^k·x < P` (e.g. `x < 2^16` from another query), the scaled query
gives `x < 2^(16−k)`. -/
theorem scaled_exact {k x : Nat} (hk : k ≤ 16) (hx : 2 ^ k * x < P)
    (h : (((2 ^ k : Nat) : F) * ((x : Nat) : F)).toNat < 2 ^ 16) : x < 2 ^ (16 - k) := by
  rw [mulq_toNat hx] at h
  have h2 : 2 ^ k * 2 ^ (16 - k) = 2 ^ 16 := by rw [← Nat.pow_add]; congr 1; omega
  refine Nat.lt_of_not_le fun hc => ?_
  have : 2 ^ k * 2 ^ (16 - k) ≤ 2 ^ k * x := Nat.mul_le_mul_left _ hc
  omega

/-- **Pattern 2 (combined).**  With `lo < 2^16` and `r16 (2^k·hi)`, the combined `lo + 2^16·hi` is
the natural `lo + 2^(16−k)·u` for some `u < 2^16`, hence `< 2^16 + 2^(32−k)`. -/
theorem combined_sound {lo k : Nat} (hk : k ≤ 16) (hlo : lo < 2 ^ 16) (hi : F)
    (h : (((2 ^ k : Nat) : F) * hi).toNat < 2 ^ 16) :
    ∃ u, u < 2 ^ 16 ∧ ((lo : Nat) : F) + ((65536 : Nat) : F) * hi = ((lo + 2 ^ (16 - k) * u : Nat) : F) ∧
      lo + 2 ^ (16 - k) * u < 2 ^ 16 + 2 ^ (32 - k) := by
  refine ⟨_, h, ?_, ?_⟩
  · rw [big_of_r16 hi k hk, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  · generalize (((2 ^ k : Nat) : F) * hi).toNat = u at h ⊢
    have e : 2 ^ (16 - k) * 2 ^ 16 = 2 ^ (32 - k) := by rw [← Nat.pow_add]; congr 1; omega
    have : 2 ^ (16 - k) * (u + 1) ≤ 2 ^ (16 - k) * 2 ^ 16 := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this
    have : 0 < 2 ^ (16 - k) := Nat.two_pow_pos _
    omega

/-- **Pattern 3 (time check).**  `timeChk ts tp hi` with `hi` an arbitrary field element: the two
R16 answers give `tp < ts` for `ts, tp < 2^29`. -/
theorem timeChk_sound {ts tp x y : Nat} (hi : F) (hts : ts < 2 ^ 29) (htp : tp < 2 ^ 29)
    (hx : x < 65536) (hy : y < 65536)
    (h1 : ((x : Nat) : F) = ((ts : Nat) : F) - ((tp : Nat) : F) - ((1 : Nat) : F) - ((65536 : Nat) : F) * hi)
    (h2 : ((y : Nat) : F) = ((4 : Nat) : F) * hi) : tp < ts :=
  regw_time_lt (hp := hi.toNat) hts htp hx hy (by rw [Fp.cast_toNat]; exact h1) (by rw [Fp.cast_toNat]; exact h2)

/-- **Pattern 4 (sign split).**  `top = 2^m·s + r` (field) with `s` a bit, `top < 2^(m+1)` and
`r16 (2^(16−m)·r)`: then `r` is the natural `top % 2^m` and `s = top / 2^m`. -/
theorem sign_split_sound {m top s : Nat} (hm : m ≤ 15) (htop : top < 2 ^ (m + 1)) (hs : s ≤ 1) (r : F)
    (he : ((top : Nat) : F) = ((2 ^ m : Nat) : F) * ((s : Nat) : F) + r)
    (h : (((2 ^ (16 - m) : Nat) : F) * r).toNat < 2 ^ 16) :
    r = ((top % 2 ^ m : Nat) : F) ∧ s = top / 2 ^ m := by
  have hP := P_val
  have hpm : 2 ^ m ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hm
  have hpm1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  have h16 : 2 ^ (16 - m) * 2 ^ m = 2 ^ 16 := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos _
  have hpos' : 0 < 2 ^ (16 - m) := Nat.two_pow_pos _
  have hz : ((P : Nat) : F) = 0 := by rw [← Fp.cast_toNat 0]; rfl
  -- the scaled query is exact on a natural `t < 2^(m+1)`
  have exact : ∀ t, t < 2 ^ (m + 1) → r = ((t : Nat) : F) → t < 2 ^ m := by
    intro t ht hr
    rw [hr] at h
    have hb : 2 ^ (16 - m) * t < P := by
      have : 2 ^ (16 - m) * t ≤ 2 ^ (16 - m) * 2 ^ (m + 1) := Nat.mul_le_mul_left _ (by omega)
      have : 2 ^ (16 - m) * 2 ^ (m + 1) = 2 ^ 17 := by rw [← Nat.pow_add]; congr 1; omega
      omega
    rw [mulq_toNat hb] at h
    refine Nat.lt_of_not_le fun hc => ?_
    have : 2 ^ (16 - m) * 2 ^ m ≤ 2 ^ (16 - m) * t := Nat.mul_le_mul_left _ hc
    omega
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · have hr : r = ((top : Nat) : F) := by have := he; grind
    have ht := exact top htop hr
    exact ⟨by rw [hr, Nat.mod_eq_of_lt ht], (Nat.div_eq_of_lt ht).symm⟩
  · by_cases hge : 2 ^ m ≤ top
    · have hr : r = ((top - 2 ^ m : Nat) : F) := by
        rw [natCast_sub_of_le hge, he, cast_one]; grind
      refine ⟨?_, ?_⟩
      · rw [hr, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
    · exfalso
      have hr : r = ((P - (2 ^ m - top) : Nat) : F) := by
        rw [natCast_sub_of_le (by omega), hz, natCast_sub_of_le (by omega)]
        have := he; rw [cast_one] at this; grind
      rw [hr, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast] at h
      have hd1 : 0 < 2 ^ (16 - m) * (2 ^ m - top) := Nat.mul_pos hpos' (by omega)
      have hd2 : 2 ^ (16 - m) * (2 ^ m - top) ≤ 2 ^ 16 := by
        rw [← h16]; exact Nat.mul_le_mul_left _ (by omega)
      have e : 2 ^ (16 - m) * (P - (2 ^ m - top)) =
          (P - 2 ^ (16 - m) * (2 ^ m - top)) + (2 ^ (16 - m) - 1) * P := by
        rw [Nat.mul_sub, Nat.sub_one_mul]
        have : P ≤ 2 ^ (16 - m) * P := Nat.le_mul_of_pos_left _ hpos'
        omega
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- **LOAD/STORE `e1`** (pattern 1): `e1 = a1 + off1 + cyE` in the field with `a1, off1 < 2^16`
and `cyE ≤ 1` makes `e1` a natural `< 2^17 + 1`, so `r16 (32·e1)` is exact: `e1 < 2^11`. -/
theorem load_e1_sound {a1 off1 cy : Nat} (ha : a1 < 2 ^ 16) (ho : off1 < 2 ^ 16) (hc : cy ≤ 1)
    (h : (((2 ^ 5 : Nat) : F) * ((a1 + off1 + cy : Nat) : F)).toNat < 2 ^ 16) : a1 + off1 + cy < 2 ^ 11 := by
  have := scaled_exact (k := 5) (x := a1 + off1 + cy) (by decide) (by rw [P_val]; omega) h
  simpa using this

/-- **The CUT padding counterexample.**  `gi = 1` (one block) with `gh = 30720` and
`gl = 1 − 2048·30720` satisfies `gi = gl + 2048·gh` and `r16 (32·gl)` (`32·gl ≡ 33`), and the
padding limb `1024·gl` is then `1056`: the length word `1056 + 2^21·30720` instead of `1024·1`. -/
theorem gl_padding_counterexample :
    let gh : F := ((30720 : Nat) : F)
    let gl : F := 1 - ((2048 : Nat) : F) * gh
    gl + ((2048 : Nat) : F) * gh = 1 ∧
      (((32 : Nat) : F) * gl).toNat = 33 ∧
      (((1024 : Nat) : F) * gl).toNat = 1056 ∧ gh.toNat = 30720 ∧
      1056 + 2 ^ 21 * 30720 ≠ 1024 * 1 := by
  decide

end WasmBase

#print axioms WasmBase.scaled_counterexample
#print axioms WasmBase.scaled_exact
#print axioms WasmBase.combined_sound
#print axioms WasmBase.timeChk_sound
#print axioms WasmBase.sign_split_sound
#print axioms WasmBase.load_e1_sound
#print axioms WasmBase.gl_padding_counterexample
