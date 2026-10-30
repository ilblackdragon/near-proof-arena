import NearSpecV3.Wasm.Float

/-!
# `NearSpecV3.Wasm.FloatRange` — fuel and range obligations of the float kernel (W04)

`Wasm/Float.lean` computes IEEE-754 results with two fuel-bounded helpers and bit-level encoders.
The L2 log (`docs/logs/lean-chunk-L2-2026-10-23.md` §7.5) recorded the fuel as an argument, not a
theorem: "`bitLen`'s 4096 fuel bounds every operand formed here; an operand beyond that would
silently truncate the bit length". This module proves the fuel and range facts the kernel relies on:

* `bitLenF_spec`, `bitLen_spec`: with fuel `F`, `bitLenF F n` is the binary length of every
  `n < 2^F` (`n < 2^len` and `2^(len-1) ≤ n` for `n ≠ 0`); so `bitLen` (fuel 4096) is exact below
  `2^4096`. `bitLen_lt_iff` restates it as the characterisation the rounding uses.
* `isqrt_spec`: the 64-step binary search returns `⌊√n⌋` for every `n < 2^128`
  (`s² ≤ n < (s+1)²`); `sqrt` calls it on arguments below `2^115`.
* Range of the bit-level operators: `neg`, `abs`, `copysign` map `[0, 2^w)` into `[0, 2^w)` for
  every format; `qnan`, `inf`, `zero` are below `2^w` for `f32`/`f64`; and the two encoders
  (`encodeNormal_lt`, `encodeSub_lt`) produce a `w`-bit pattern whenever their significand has at
  most `p` bits, which is the invariant the rounding (`roundPackS`) maintains.

* `roundPackS_lt`: the rounding hands the encoders at most `p` significand bits in every branch
  (subnormal, exact, rounded, carry into the next binade), so every rounded result is a `w`-bit
  pattern for every significand below the `bitLen` fuel bound; `add_lt`, `sub_lt`, `mul_lt`,
  `div_lt`, `sqrt_lt` discharge that bound for the five arithmetic operators (the aligned `add`
  operands stay below `2^(p + 2^eb)`, i.e. `2^2101` for `f64`), so **every arithmetic result is a
  `w`-bit pattern**, whatever the inputs (`sqrt`: on `w`-bit inputs).

* `min_lt`, `max_lt`, `roundToInt_lt` (`ceil`/`floor`/`trunc`/`nearest`), `convertInt_lt`,
  `demote_lt`, `promote_lt`, `truncSat_lt`: the remaining value-producing float operators also
  stay in range (on `w`-bit inputs where the operator returns an input).

So every float operator of the kernel maps `w`-bit inputs to `w`-bit results. What is **not**
claimed: that the results agree with nearcore — that stays a differential obligation
(`oracle/wasm-d3/tests/difftest_float.py`, `float_nearcore.py`) — and the chunk-level float overlap
(`checkD3 ⊆ checkD3F` on float-free chunks), which is tier obligation O1 (`Successor/TierMono.lean`,
another lane).

Axioms: `propext`, `Classical.choice`, `Quot.sound` (audit in
`docs/logs/lean-proof-debt-2026-10-29.md`).
-/

namespace NearSpecV3.Wasm

/-! ## `bitLen`: the fuel suffices below `2^fuel` -/

theorem bitLenF_zero (fuel : Nat) : Fmt.bitLenF fuel 0 = 0 := by
  cases fuel <;> simp [Fmt.bitLenF]

/-- **`bitLenF` is the binary length below `2^fuel`.** -/
theorem bitLenF_spec : ∀ (fuel n : Nat), n < 2 ^ fuel →
    n < 2 ^ Fmt.bitLenF fuel n ∧ (n ≠ 0 → 2 ^ (Fmt.bitLenF fuel n - 1) ≤ n)
  | 0, n, h => by simp at h; subst h; simp [Fmt.bitLenF]
  | fuel + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [Fmt.bitLenF]
    have hh : n / 2 < 2 ^ fuel := by
      rw [Nat.pow_succ] at h; omega
    obtain ⟨ih1, ih2⟩ := bitLenF_spec fuel (n / 2) hh
    simp only [Fmt.bitLenF, hn, ite_false]
    constructor
    · rw [Nat.add_comm, Nat.pow_succ]; omega
    · intro _
      by_cases h2 : n / 2 = 0
      · rw [h2, bitLenF_zero]; simp; omega
      · have := ih2 h2
        have hb : Fmt.bitLenF fuel (n / 2) ≠ 0 := by
          intro e; rw [e] at ih1; simp at ih1; omega
        have : 1 + Fmt.bitLenF fuel (n / 2) - 1 = (Fmt.bitLenF fuel (n / 2) - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; omega

/-- `bitLen` (fuel 4096) is exact for every operand below `2^4096`. -/
theorem bitLen_spec (n : Nat) (h : n < 2 ^ 4096) :
    n < 2 ^ Fmt.bitLen n ∧ (n ≠ 0 → 2 ^ (Fmt.bitLen n - 1) ≤ n) :=
  bitLenF_spec 4096 n h

/-- Equivalent form: below the fuel bound, `n < 2^k` exactly when `bitLen n ≤ k`. -/
theorem bitLen_lt_iff (n k : Nat) (h : n < 2 ^ 4096) : n < 2 ^ k ↔ Fmt.bitLen n ≤ k := by
  obtain ⟨h1, h2⟩ := bitLen_spec n h
  constructor
  · intro hk
    by_cases hn : n = 0
    · subst hn; simp [Fmt.bitLen, bitLenF_zero]
    have := h2 hn
    apply Classical.byContradiction
    intro hc
    have : 2 ^ k ≤ 2 ^ (Fmt.bitLen n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · intro hk
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hk)

/-! ## `isqrt`: the 64-step binary search is `⌊√n⌋` below `2^128` -/

theorem isqrtGo_spec (n : Nat) : ∀ (j r : Nat), r * r ≤ n → n < (r + 2 ^ (j + 1)) * (r + 2 ^ (j + 1)) →
    let s := Fmt.isqrtGo n (j + 1) (2 ^ j) r
    s * s ≤ n ∧ n < (s + 1) * (s + 1)
  | 0, r, h1, h2 => by
    simp only [Fmt.isqrtGo, Nat.pow_zero, Nat.one_ne_zero, ite_false]
    split
    · rename_i hc
      try simp only [Fmt.isqrtGo]
      exact ⟨hc, by
        have : r + 1 + 1 = r + 2 := by omega
        rw [this]; exact h2⟩
    · rename_i hc
      try simp only [Fmt.isqrtGo]
      exact ⟨h1, Nat.lt_of_not_le hc⟩
  | j + 1, r, h1, h2 => by
    have hb : 2 ^ (j + 1) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
    have hdiv : 2 ^ (j + 1) / 2 = 2 ^ j := by rw [Nat.pow_succ]; omega
    simp only [Fmt.isqrtGo, hb, ite_false, hdiv]
    split
    · rename_i hc
      apply isqrtGo_spec n j (r + 2 ^ (j + 1)) hc
      have : r + 2 ^ (j + 1) + 2 ^ (j + 1) = r + 2 ^ (j + 1 + 1) := by
        have e : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) * 2 := Nat.pow_succ ..
        omega
      rw [this]; exact h2
    · rename_i hc
      exact isqrtGo_spec n j r h1 (Nat.lt_of_not_le hc)

/-- **`isqrt` is the floor square root below `2^128`.** -/
theorem isqrt_spec (n : Nat) (h : n < 2 ^ 128) :
    Fmt.isqrt n * Fmt.isqrt n ≤ n ∧ n < (Fmt.isqrt n + 1) * (Fmt.isqrt n + 1) := by
  have := isqrtGo_spec n 63 0 (by simp) (by
    simp only [Nat.zero_add]
    have : (2 : Nat) ^ (63 + 1) * 2 ^ (63 + 1) = 2 ^ 128 := by rw [← Nat.pow_add]
    rw [this]; exact h)
  exact this

/-! ## Range of the bit-level operators -/

/-- `neg` is a `w`-bit pattern for every format and every input. -/
theorem neg_lt (f : Fmt) (a : Nat) : Fmt.neg f a < 2 ^ f.w :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- `abs` clears the sign bit: a `w`-bit pattern below `2^(w-1)`. -/
theorem abs_lt (f : Fmt) (a : Nat) (hw : 0 < f.w) : Fmt.abs f a < 2 ^ (f.w - 1) := by
  unfold Fmt.abs
  have := Nat.and_le_right (n := a) (m := 2 ^ (f.w - 1) - 1)
  have hp := Nat.two_pow_pos (f.w - 1)
  omega

theorem abs_lt_w (f : Fmt) (a : Nat) (hw : 0 < f.w) : Fmt.abs f a < 2 ^ f.w := by
  have := abs_lt f a hw
  have : 2 ^ (f.w - 1) ≤ 2 ^ f.w := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- `copysign` is a `w`-bit pattern for every format and every input. -/
theorem copysign_lt (f : Fmt) (a b : Nat) (hw : 0 < f.w) : Fmt.copysign f a b < 2 ^ f.w := by
  unfold Fmt.copysign
  have h1 := abs_lt f a hw
  have h2 : Fmt.signNat f b ≤ 1 := by unfold Fmt.signNat; omega
  have h3 : 2 ^ f.w = 2 ^ (f.w - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have : Fmt.signNat f b * 2 ^ (f.w - 1) ≤ 2 ^ (f.w - 1) := by
    calc Fmt.signNat f b * 2 ^ (f.w - 1) ≤ 1 * 2 ^ (f.w - 1) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (f.w - 1) := Nat.one_mul _
  omega

/-- The special values are `w`-bit patterns. -/
theorem specials_lt : (∀ s, Fmt.inf f32 s < 2 ^ 32 ∧ Fmt.zero f32 s < 2 ^ 32) ∧ Fmt.qnan f32 < 2 ^ 32 ∧
    (∀ s, Fmt.inf f64 s < 2 ^ 64 ∧ Fmt.zero f64 s < 2 ^ 64) ∧ Fmt.qnan f64 < 2 ^ 64 := by
  refine ⟨fun s => ?_, by decide, fun s => ?_, by decide⟩ <;> cases s <;> decide

/-! ## The encoders produce `w`-bit patterns from `p`-bit significands -/

/-- The two pinned formats: one sign bit, `eb` exponent bits, `p - 1` fraction bits. -/
def StdFmt (f : Fmt) : Prop := f = f32 ∨ f = f64

theorem StdFmt.layout {f : Fmt} (h : StdFmt f) :
    f.w = Fmt.fracBits f + f.eb + 1 ∧ 2 ≤ f.p ∧ 1 ≤ f.eb ∧ Fmt.bias f + Fmt.bias f + 1 < 2 ^ f.eb := by
  rcases h with rfl | rfl <;> decide

theorem or_lt_pow {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : a ||| b < 2 ^ n :=
  Nat.or_lt_two_pow ha hb

theorem signPart_or_lt (f : Fmt) (s : Bool) (x : Nat) (hw : 0 < f.w) (hx : x < 2 ^ (f.w - 1)) :
    Fmt.signPart f s ||| x < 2 ^ f.w := by
  have hsplit : 2 ^ f.w = 2 ^ (f.w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  cases s
  · simp only [Fmt.signPart, Bool.false_eq_true, ite_false, Nat.zero_or]; omega
  · simp only [Fmt.signPart, ite_true]
    exact Nat.or_lt_two_pow (by omega) (by omega)

/-- **`encodeNormal` yields a `w`-bit pattern** when the significand has exactly `p` bits
(`2^(p-1) ≤ q < 2^p`) and the binade is at least `emin` (an overflowing binade gives `inf`). -/
theorem encodeNormal_lt (f : Fmt) (hf : StdFmt f) (s : Bool) (q : Nat) (eTop : Int)
    (hq : q < 2 ^ f.p) (he : Fmt.emin f ≤ eTop) : Fmt.encodeNormal f s q eTop < 2 ^ f.w := by
  obtain ⟨hw, hp, heb, hbias⟩ := hf.layout
  unfold Fmt.encodeNormal
  split
  · rcases hf with rfl | rfl <;> cases s <;> decide
  · rename_i hle
    have hle : eTop ≤ Fmt.emax f := Int.not_lt.mp hle
    simp only [Fmt.emax, Fmt.emin] at hle he
    have hef : (eTop + (Fmt.bias f : Int)).toNat < 2 ^ f.eb := by omega
    have hfrac : q - 2 ^ (f.p - 1) < 2 ^ Fmt.fracBits f := by
      have : 2 ^ f.p = 2 ^ (f.p - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
      unfold Fmt.fracBits; omega
    have hshift : (eTop + (Fmt.bias f : Int)).toNat <<< Fmt.fracBits f < 2 ^ (f.eb + Fmt.fracBits f) := by
      rw [Nat.shiftLeft_eq, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hef (Nat.two_pow_pos _)
    have hlow : 2 ^ Fmt.fracBits f ≤ 2 ^ (f.eb + Fmt.fracBits f) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hbody : (eTop + (Fmt.bias f : Int)).toNat <<< Fmt.fracBits f ||| (q - 2 ^ (f.p - 1)) <
        2 ^ (f.w - 1) := by
      have : f.w - 1 = f.eb + Fmt.fracBits f := by omega
      rw [this]
      exact or_lt_pow hshift (by omega)
    rw [Nat.or_assoc]
    exact signPart_or_lt f s _ (by omega) hbody

/-- **`encodeSub` yields a `w`-bit pattern** for every significand of at most `p` bits. -/
theorem encodeSub_lt (f : Fmt) (hf : StdFmt f) (s : Bool) (r : Nat) (hr : r < 2 ^ f.p) :
    Fmt.encodeSub f s r < 2 ^ f.w := by
  obtain ⟨hw, hp, heb, hbias⟩ := hf.layout
  unfold Fmt.encodeSub
  split
  · rcases hf with rfl | rfl <;> cases s <;> decide
  · split
    · rename_i _ hlt
      apply signPart_or_lt f s r (by omega)
      have : 2 ^ (f.p - 1) ≤ 2 ^ (f.w - 1) := Nat.pow_le_pow_right (by decide) (by unfold Fmt.fracBits at hw; omega)
      omega
    · exact encodeNormal_lt f hf s r (Fmt.emin f) hr (Int.le_refl _)


/-! ## `roundPackS` yields a `w`-bit pattern

Only the upper half of `bitLen_spec` is needed: the rounded significand has at most `p` bits in
every branch (subnormal, exact, rounded, and the carry into the next binade). -/

theorem shl_lt {m a k : Nat} (h : m < 2 ^ a) : m <<< k < 2 ^ (a + k) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)

theorem shr_lt {m a d : Nat} (h : m < 2 ^ a) (hd : d ≤ a) : m >>> d < 2 ^ (a - d) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    Nat.sub_add_cancel hd]
  exact h

theorem pow_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h

/-- **Every rounding result is a `w`-bit pattern** (for `f32`/`f64`), for every significand below
the `bitLen` fuel bound. -/
theorem roundPackS_lt (f : Fmt) (hf : StdFmt f) (s : Bool) (m : Nat) (e : Int) (st : Bool)
    (hm : m < 2 ^ 4096) : Fmt.roundPackS f s m e st < 2 ^ f.w := by
  obtain ⟨hw, hp, heb, hbias⟩ := hf.layout
  have hbl := (bitLen_spec m hm).1
  have hge : Fmt.gridExp f = Fmt.emin f - ((f.p : Int) - 1) := rfl
  unfold Fmt.roundPackS
  split
  · rcases hf with rfl | rfl <;> cases s <;> decide
  · rename_i hm0
    simp only
    split
    · -- gradual underflow
      rename_i hlow
      split
      · rename_i hge'
        apply encodeSub_lt f hf s _
        have h1 := shl_lt (k := (e - Fmt.gridExp f).toNat) hbl
        have : Fmt.bitLen m + (e - Fmt.gridExp f).toNat ≤ f.p := by omega
        exact Nat.lt_of_lt_of_le h1 (pow_mono this)
      · rename_i hge'
        apply encodeSub_lt f hf s _
        have hq : m >>> (Fmt.gridExp f - e).toNat < 2 ^ (f.p - 1) := by
          by_cases hd : (Fmt.gridExp f - e).toNat ≤ Fmt.bitLen m
          · have := shr_lt hbl hd
            exact Nat.lt_of_lt_of_le this (pow_mono (by omega))
          · have : m >>> (Fmt.gridExp f - e).toNat = 0 := by
              rw [Nat.shiftRight_eq_div_pow]
              apply Nat.div_eq_of_lt
              exact Nat.lt_of_lt_of_le hbl (pow_mono (by omega))
            rw [this]; exact Nat.two_pow_pos _
        have h2 : 2 ^ (f.p - 1) < 2 ^ f.p := Nat.pow_lt_pow_right (by decide) (by omega)
        generalize m >>> (Fmt.gridExp f - e).toNat = q at hq ⊢
        have key : ∀ b : Bool, (if b = true then q + 1 else q) < 2 ^ f.p := by
          intro b; cases b <;> simp <;> omega
        exact key _
    · rename_i hhi
      have hhi : Fmt.emin f ≤ e + (Fmt.bitLen m : Int) - 1 := Int.not_lt.mp hhi
      split
      · rename_i hd
        apply encodeNormal_lt f hf s _ _ _ hhi
        have := shl_lt (k := f.p - Fmt.bitLen m) hbl
        exact Nat.lt_of_lt_of_le this (pow_mono (by omega))
      · rename_i hd
        have hq : m >>> (Fmt.bitLen m - f.p) < 2 ^ f.p := by
          have := shr_lt hbl (Nat.sub_le (Fmt.bitLen m) f.p)
          exact Nat.lt_of_lt_of_le this (pow_mono (by omega))
        generalize m >>> (Fmt.bitLen m - f.p) = q at hq ⊢
        have key : ∀ b : Bool,
            (if (if b = true then q + 1 else q) = 2 ^ f.p then
                Fmt.encodeNormal f s (2 ^ (f.p - 1)) (e + (Fmt.bitLen m : Int) - 1 + 1)
              else Fmt.encodeNormal f s (if b = true then q + 1 else q) (e + (Fmt.bitLen m : Int) - 1))
              < 2 ^ f.w := by
          intro b
          have hq' : (if b = true then q + 1 else q) ≤ 2 ^ f.p := by cases b <;> simp <;> omega
          generalize (if b = true then q + 1 else q) = q' at hq' ⊢
          split
          · apply encodeNormal_lt f hf s _ _ _ (by omega)
            exact Nat.pow_lt_pow_right (by decide) (by omega)
          · rename_i hne
            apply encodeNormal_lt f hf s _ _ _ hhi
            omega
        exact key _

theorem roundPack_lt (f : Fmt) (hf : StdFmt f) (s : Bool) (m : Nat) (e : Int) (hm : m < 2 ^ 4096) :
    Fmt.roundPack f s m e < 2 ^ f.w :=
  roundPackS_lt f hf s m e false hm


/-! ## `mul` and `div` results are `w`-bit patterns -/

theorem decode_m_lt (f : Fmt) (hf : StdFmt f) (b : Nat) : (Fmt.decode f b).2.1 < 2 ^ f.p := by
  obtain ⟨hw, hp, heb, hbias⟩ := hf.layout
  have hfr : Fmt.fracField f b < 2 ^ Fmt.fracBits f := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpf : 2 ^ f.p = 2 ^ Fmt.fracBits f * 2 := by
    unfold Fmt.fracBits; rw [← Nat.pow_succ]; congr 1; omega
  unfold Fmt.decode
  simp only
  split <;> simp only <;> omega

theorem specials_lt' (f : Fmt) (hf : StdFmt f) (s : Bool) :
    Fmt.inf f s < 2 ^ f.w ∧ Fmt.zero f s < 2 ^ f.w ∧ Fmt.qnan f < 2 ^ f.w := by
  rcases hf with rfl | rfl <;> cases s <;> decide

theorem pow_p_lt (f : Fmt) (hf : StdFmt f) : 3 * f.p + 2 ≤ 4096 := by
  rcases hf with rfl | rfl <;> decide

/-- **`mul` returns a `w`-bit pattern** for every pair of inputs. -/
theorem mul_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) : Fmt.mul f a b < 2 ^ f.w := by
  have hs := specials_lt' f hf
  have hpp := pow_p_lt f hf
  unfold Fmt.mul
  simp only
  split; · exact (hs false).2.2
  split; · exact (hs false).2.2
  split; · exact (hs _).1
  split; · exact (hs _).2.1
  apply roundPack_lt f hf
  have ha := decode_m_lt f hf a
  have hb := decode_m_lt f hf b
  have : (Fmt.decode f a).2.1 * (Fmt.decode f b).2.1 < 2 ^ f.p * 2 ^ f.p :=
    Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (Nat.two_pow_pos _)
  rw [← Nat.pow_add] at this
  exact Nat.lt_of_lt_of_le this (pow_mono (by omega))

/-- **`div` returns a `w`-bit pattern** for every pair of inputs. -/
theorem div_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) : Fmt.div f a b < 2 ^ f.w := by
  have hs := specials_lt' f hf
  have hpp := pow_p_lt f hf
  unfold Fmt.div
  simp only
  split; · exact (hs false).2.2
  split; · exact (hs false).2.2
  split; · exact (hs _).1
  split; · exact (hs _).2.1
  split; · exact (hs _).1
  split; · exact (hs _).2.1
  apply roundPackS_lt f hf
  have ha := decode_m_lt f hf a
  have hb := decode_m_lt f hf b
  have hblb : Fmt.bitLen (Fmt.decode f b).2.1 ≤ f.p :=
    (bitLen_lt_iff _ f.p (Nat.lt_of_lt_of_le hb (pow_mono (by omega)))).mp hb
  generalize (Fmt.decode f a).2.1 = ma at ha ⊢
  generalize (Fmt.decode f b).2.1 = mb at hb hblb ⊢
  generalize hs' : Fmt.bitLen mb + f.p + 2 - Fmt.bitLen ma = sh
  have hsh : sh ≤ 2 * f.p + 2 := by omega
  have hnum : ma <<< sh < 2 ^ (f.p + sh) := shl_lt ha
  have : (ma <<< sh) / mb ≤ ma <<< sh := Nat.div_le_self _ _
  exact Nat.lt_of_le_of_lt this (Nat.lt_of_lt_of_le hnum (pow_mono (by omega)))


theorem isqrtGo_le (n : Nat) : ∀ (fuel bit r : Nat), Fmt.isqrtGo n fuel bit r ≤ r + 2 * bit
  | 0, bit, r => by simp [Fmt.isqrtGo]
  | fuel + 1, bit, r => by
    simp only [Fmt.isqrtGo]
    split
    · omega
    · split
      · have := isqrtGo_le n fuel (bit / 2) (r + bit); omega
      · have := isqrtGo_le n fuel (bit / 2) r; omega

/-- **`sqrt` returns a `w`-bit pattern** on every `w`-bit input. -/
theorem sqrt_lt (f : Fmt) (hf : StdFmt f) (a : Nat) (ha : a < 2 ^ f.w) : Fmt.sqrt f a < 2 ^ f.w := by
  have hs := specials_lt' f hf
  unfold Fmt.sqrt
  split; · exact (hs false).2.2
  split; · exact ha
  split; · exact (hs false).2.2
  split; · exact ha
  simp only
  apply roundPackS_lt f hf
  unfold Fmt.isqrt
  generalize (_ : Nat) <<< _ = n
  have := isqrtGo_le n 64 (2 ^ 63) 0
  have h64 : 0 + 2 * 2 ^ 63 < 2 ^ 4096 := by
    rw [Nat.zero_add, ← Nat.pow_succ']
    exact Nat.pow_lt_pow_right (by decide) (by decide)
  exact Nat.lt_of_le_of_lt this h64


/-! ## `add`/`sub`: the aligned operands stay below the fuel bound -/

/-- Decoded exponents lie in `[gridExp, gridExp + 2^eb - 2]`. -/
theorem decode_e_bounds (f : Fmt) (hf : StdFmt f) (b : Nat) :
    Fmt.gridExp f ≤ (Fmt.decode f b).2.2 ∧ (Fmt.decode f b).2.2 ≤ Fmt.gridExp f + (2 ^ f.eb : Nat) - 2 := by
  obtain ⟨hw, hp, heb, hbias⟩ := hf.layout
  have hef : Fmt.expField f b < 2 ^ f.eb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hge : Fmt.gridExp f = 1 - (Fmt.bias f : Int) - (Fmt.fracBits f : Int) := by
    unfold Fmt.gridExp Fmt.emin Fmt.fracBits; omega
  have h2 : (2 : Nat) ≤ 2 ^ f.eb := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f.eb := pow_mono heb
  unfold Fmt.decode
  simp only
  split
  · simp only; omega
  · simp only; rw [hge]; omega

theorem shifted_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) :
    (Fmt.decode f a).2.1 <<< ((Fmt.decode f a).2.2 - min (Fmt.decode f a).2.2 (Fmt.decode f b).2.2).toNat
      < 2 ^ (f.p + 2 ^ f.eb) := by
  have hm := decode_m_lt f hf a
  have ha := decode_e_bounds f hf a
  have hb := decode_e_bounds f hf b
  have h := shl_lt (k := ((Fmt.decode f a).2.2 - min (Fmt.decode f a).2.2 (Fmt.decode f b).2.2).toNat) hm
  exact Nat.lt_of_lt_of_le h (pow_mono (by omega))

theorem eb_bound (f : Fmt) (hf : StdFmt f) : f.p + 2 ^ f.eb + 1 ≤ 4096 := by
  rcases hf with rfl | rfl <;> decide

/-- **`add` returns a `w`-bit pattern** for every pair of inputs. -/
theorem add_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) : Fmt.add f a b < 2 ^ f.w := by
  have hs := specials_lt' f hf
  have hbound := eb_bound f hf
  have hA := shifted_lt f hf a b
  have hB := shifted_lt f hf b a
  rw [Int.min_comm] at hB
  unfold Fmt.add
  split; · exact (hs false).2.2
  split
  · split
    · exact (hs _).1
    · exact (hs false).2.2
  split; · exact (hs _).1
  split; · exact (hs _).1
  simp only
  split; · exact (hs _).2.1
  generalize ((Fmt.decode f a).2.1 <<< _ : Nat) = x at hA ⊢
  generalize ((Fmt.decode f b).2.1 <<< _ : Nat) = y at hB ⊢
  have key : ∀ (ca cb : Int), (ca = 1 ∨ ca = -1) → (cb = 1 ∨ cb = -1) →
      (if ca * (x : Int) + cb * (y : Int) = 0 then Fmt.zero f false
        else Fmt.roundPack f (decide (ca * (x : Int) + cb * (y : Int) < 0))
          (ca * (x : Int) + cb * (y : Int)).natAbs
          (min (Fmt.decode f a).2.2 (Fmt.decode f b).2.2)) < 2 ^ f.w := by
    intro ca cb hca hcb
    split
    · exact (hs false).2.1
    · apply roundPack_lt f hf
      have hxy : (ca * (x : Int) + cb * (y : Int)).natAbs ≤ x + y := by
        rcases hca with rfl | rfl <;> rcases hcb with rfl | rfl <;> omega
      have h2 : x + y < 2 ^ (f.p + 2 ^ f.eb + 1) := by rw [Nat.pow_succ]; omega
      exact Nat.lt_of_le_of_lt hxy (Nat.lt_of_lt_of_le h2 (pow_mono hbound))
  apply key
  · split <;> simp
  · split <;> simp

/-- `sub` is `add` of the negation. -/
theorem sub_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) : Fmt.sub f a b < 2 ^ f.w := add_lt f hf a _


/-! ## `min`/`max`, the integer roundings and the conversions -/

theorem min_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) (ha : a < 2 ^ f.w) (hb : b < 2 ^ f.w) :
    Fmt.min f a b < 2 ^ f.w := by
  have hs := specials_lt' f hf
  unfold Fmt.min
  split; · exact (hs false).2.2
  split; · exact Nat.or_lt_two_pow ha hb
  split <;> assumption

theorem max_lt (f : Fmt) (hf : StdFmt f) (a b : Nat) (ha : a < 2 ^ f.w) (hb : b < 2 ^ f.w) :
    Fmt.max f a b < 2 ^ f.w := by
  have hs := specials_lt' f hf
  unfold Fmt.max
  split; · exact (hs false).2.2
  split; · exact Nat.lt_of_le_of_lt (Nat.and_le_left) ha
  split <;> assumption

/-- `ceil`/`floor`/`trunc`/`nearest` return `w`-bit patterns on `w`-bit inputs. -/
theorem roundToInt_lt (f : Fmt) (hf : StdFmt f) (md : Fmt.RMode) (a : Nat) (ha : a < 2 ^ f.w) :
    Fmt.roundToInt f md a < 2 ^ f.w := by
  have hs := specials_lt' f hf
  have hpp := pow_p_lt f hf
  have hm := decode_m_lt f hf a
  unfold Fmt.roundToInt
  split; · exact (hs false).2.2
  split; · exact ha
  simp only
  split; · exact ha
  have hq : ∀ d, (Fmt.decode f a).2.1 >>> d ≤ (Fmt.decode f a).2.1 := fun d => by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have key : ∀ (q : Nat), q ≤ (Fmt.decode f a).2.1 → ∀ (b s' : Bool),
      (if (if b = true then q + 1 else q) = 0 then Fmt.zero f s'
        else Fmt.roundPack f s' (if b = true then q + 1 else q) 0) < 2 ^ f.w := by
    intro q hq b s'
    have hle : (if b = true then q + 1 else q) ≤ q + 1 := by cases b <;> simp
    generalize (if b = true then q + 1 else q) = q' at hle ⊢
    split
    · exact (hs s').2.1
    · apply roundPack_lt f hf
      have : q' ≤ q + 1 := hle
      have h2 : q + 1 < 2 ^ (f.p + 1) := by rw [Nat.pow_succ]; omega
      exact Nat.lt_of_le_of_lt this (Nat.lt_of_lt_of_le h2 (pow_mono (by omega)))
  exact key _ (hq _) _ _

/-- Integer → float conversions return `w`-bit patterns (every `i32`/`i64` operand is far below
the fuel bound). -/
theorem convertInt_lt (f : Fmt) (hf : StdFmt f) (n : Int) (hn : n.natAbs < 2 ^ 4096) :
    Fmt.convertInt f n < 2 ^ f.w :=
  roundPack_lt f hf _ _ _ hn

theorem demote_lt (a : Nat) : Fmt.demote a < 2 ^ 32 := by
  have hs := specials_lt' f32 (Or.inl rfl)
  unfold Fmt.demote
  split; · exact (hs false).2.2
  split; · exact (hs _).1
  split; · exact (hs _).2.1
  simp only
  apply roundPack_lt f32 (Or.inl rfl)
  have := decode_m_lt f64 (Or.inr rfl) a
  exact Nat.lt_of_lt_of_le this (pow_mono (by decide))

theorem promote_lt (a : Nat) : Fmt.promote a < 2 ^ 64 := by
  have hs := specials_lt' f64 (Or.inr rfl)
  unfold Fmt.promote
  split; · exact (hs false).2.2
  split; · exact (hs _).1
  split; · exact (hs _).2.1
  simp only
  apply roundPack_lt f64 (Or.inr rfl)
  have := decode_m_lt f32 (Or.inl rfl) a
  exact Nat.lt_of_lt_of_le this (pow_mono (by decide))

/-- Saturating truncation yields a `w`-bit two's-complement pattern. -/
theorem truncSat_lt (f : Fmt) (a : Nat) (lo hi : Int) (w : Nat) :
    Fmt.truncSat f a lo hi w < 2 ^ w := by
  have key : ∀ v : Int, (v % (2 ^ w : Int)).toNat < 2 ^ w := by
    intro v
    have hc : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := (Int.natCast_pow 2 w).symm
    have hp := Nat.two_pow_pos w
    rw [hc]
    have h1 : 0 ≤ v % ((2 ^ w : Nat) : Int) := Int.emod_nonneg _ (by omega)
    have h2 : v % ((2 ^ w : Nat) : Int) < ((2 ^ w : Nat) : Int) := Int.emod_lt_of_pos _ (by omega)
    omega
  unfold Fmt.truncSat
  split
  · exact key _
  · split
    · exact Nat.two_pow_pos w
    · split <;> exact key _

end NearSpecV3.Wasm
