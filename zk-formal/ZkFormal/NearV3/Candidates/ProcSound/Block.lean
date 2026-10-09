import ZkFormal.NearV3.Candidates.ProcSound.Row

/-!
# ZkFormal.NearV3.Sched.View.ProcBlock — the key block of an instance of `sprV3`

A key block starts at a key row `f` with `kc = 0` (the first row, or the row after a block end /
round end, `blk_next`). **`proc_keys`**: the 16 rows `f … f + 15` are key rows with `kc = i` on
row `f + i` and the τ of row `f`; row `f + i` receives the public record
`SPUBB (τ, 3, i, lo_i, hi_i, 0, 0)` (`lo_i, hi_i` = `sbIn, sbOut` of the row); the row `f + 16`
after the block exists and holds the limbs `L_i ≡ lo_i + 256·hi_i`; it is padding, a new key
block (`kc = 0`, `τ + 1`), or the first header of the instance (`T = T0`, `kq = 0`,
`Kq = KSENT`, `zq = 0`, same τ).
-/

namespace ZkFormal.NearV3.Candidates.ProcSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Proc

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

/-! ## Evaluation of messages and multiplicities -/

theorem ev_c (w col : Nat) : (c col).eval tr tp w pub = Fp.ofNat (cv tr tp w col) :=
  (Fp.ofNat_toNat _).symm

theorem ev_k (w v : Nat) : (k v).eval tr tp w pub = Fp.ofNat v := rfl

theorem ev_of {e : Expr} {w v : Nat} (h : zev (tenv tr tp w pub) e = (v : Int)) :
    e.eval tr tp w pub = Fp.ofNat v := by
  rw [eval_eq, h, intCast_ofNat]

theorem mult_of {i : Interaction} {e : Expr} {w : Nat} (hm : i.mult = [e])
    (h : zev (tenv tr tp w pub) e = 1) : i.multNat tr tp w pub = 1 := by
  unfold Interaction.multNat
  rw [hm]
  simp only [Interaction.multNat.go]
  rw [ev_of (v := 1) (by rw [h]; rfl)]
  rfl

theorem mult_zero {i : Interaction} {e : Expr} {w : Nat} (hm : i.mult = [e])
    (h : zev (tenv tr tp w pub) e = 0) : i.multNat tr tp w pub = 0 := by
  unfold Interaction.multNat
  rw [hm]
  simp only [Interaction.multNat.go]
  rw [ev_of (v := 0) (by rw [h]; rfl)]
  decide

theorem mult_bit {i : Interaction} {e : Expr} {w col : Nat} (hm : i.mult = [e])
    (h : zev (tenv tr tp w pub) e = (cv tr tp w col : Int)) (hx : cv tr tp w col ≤ 1) :
    i.multNat tr tp w pub = cv tr tp w col := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with h0 | h1
  · rw [h0]; exact mult_zero hm (by rw [h, h0]; rfl)
  · rw [h1]; exact mult_of hm (by rw [h, h1]; rfl)

theorem ofNat_mod (a : Nat) : Fp.ofNat (a % 2013265921) = Fp.ofNat a :=
  Fp.ext (by rw [Fp.toNat_ofNat, Fp.toNat_ofNat, P_val, Nat.mod_mod])

theorem i0_def : interactions[0]! = Interaction.mk B_SPUBB [c kK]
    [c tau, k TAG_KEY, c kc, c sbIn, c sbOut, k 0, k 0] false := rfl

/-! ## The key block -/

theorem key_rows (hL : PLocal tr tp pub) {f : Nat} (hf : f < tr.height tp)
    (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0) :
    ∀ i, i < 16 → f + i < tr.height tp ∧ cv tr tp (f + i) kK = 1 ∧ cv tr tp (f + i) kc = i ∧
      cv tr tp (f + i) tau = cv tr tp f tau := by
  intro i
  induction i with
  | zero => intro _; exact ⟨hf, hk, hc, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨hw, hk', hc', ht'⟩ := ih (by omega)
    have hl : cv tr tp (f + i) kl = 0 := by
      have h := (kl_iff hL hw).2 hk'
      have := (kinds hL hw).2.2.2.2.1
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with e | e
      · exact e
      · have := h.1 e; omega
    obtain ⟨hw1, k1, c1, t1⟩ := key_next hL hw hk' hl
    rw [show f + (i + 1) = f + i + 1 by omega]
    exact ⟨hw1, k1, by rw [c1, hc']; omega, by rw [t1, ht']⟩

/-- **Key block.** -/
theorem proc_keys (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0) :
    (∀ i, i < 16 → f + i < tr.height tp ∧ cv tr tp (f + i) kK = 1 ∧ cv tr tp (f + i) kc = i ∧
      cv tr tp (f + i) tau = cv tr tp f tau ∧
      (interactions[0]!).multNat tr tp (f + i) pub = 1 ∧
      (interactions[0]!).msgVal tr tp (f + i) pub =
        [cv tr tp f tau, TAG_KEY, i, cv tr tp (f + i) sbIn, cv tr tp (f + i) sbOut, 0, 0].map
          Fp.ofNat) ∧
    cv tr tp (f + 15) kl = 1 ∧ f + 16 < tr.height tp ∧
    (cv tr tp (f+16) kK=0 → ∀ i, i < 16 → cv tr tp (f + 16) (colL i) =
      (cv tr tp (f + i) sbIn + 256 * cv tr tp (f + i) sbOut) % 2013265921) ∧
    (cv tr tp (f + 16) act = 0 ∨
      (cv tr tp (f + 16) kK = 1 ∧ cv tr tp (f + 16) kc = 0 ∧
        cv tr tp (f + 16) tau = cv tr tp f tau + 1) ∨
      (cv tr tp (f + 16) kH = 1 ∧ cv tr tp (f + 16) tau = cv tr tp f tau ∧
        cv tr tp (f + 16) T = T0 ∧ cv tr tp (f + 16) kq = 0 ∧ cv tr tp (f + 16) Kq = KSENT ∧
        cv tr tp (f + 16) zq = 0)) := by
  have KR := key_rows hL hf hk hc
  obtain ⟨h15, k15, c15, t15⟩ := KR 15 (by omega)
  have l15 : cv tr tp (f + 15) kl = 1 := ((kl_iff hL h15).2 k15).2 c15
  obtain ⟨h16, -, -⟩ := key_reg hL h15 k15
  rw [show f + 15 + 1 = f + 16 by omega] at h16
  -- the rotation
  have rot (hn : cv tr tp (f+16) kK=0) : ∀ d, d ≤ 15 → ∀ i, i < 16 →
      cv tr tp (f + 16) (colL i) = cv tr tp (f + 15 - d) (colL ((i + 1 + d) % 16)) := by
    intro d
    induction d with
    | zero =>
      intro _ i hi
      have := (key_reg hL h15 k15).2.2 i hi (Or.inr (by simpa [Nat.add_assoc] using hn))
      rw [show f + 15 + 1 = f + 16 by omega] at this
      rw [this]; rfl
    | succ d ih =>
      intro hd i hi
      obtain ⟨hw, kw, cw, -⟩ := KR (14 - d) (by omega)
      rw [show f + (14 - d) = f + 15 - (d + 1) by omega] at hw kw cw
      have hz : cv tr tp (f+15-(d+1)) kl=0 := by
        have hb := (kinds hL hw).2.2.2.2.1
        have he := (kl_iff hL hw).2 kw
        omega
      have := (key_reg hL hw kw).2.2 ((i + 1 + d) % 16) (Nat.mod_lt _ (by omega)) (Or.inl hz)
      rw [show f + 15 - (d + 1) + 1 = f + 15 - d by omega] at this
      rw [ih (by omega) i hi, this, show ((i + 1 + d) % 16 + 1) % 16 = (i + 1 + (d + 1)) % 16 by omega]
  have limbs : cv tr tp (f+16) kK=0 → ∀ i, i < 16 → cv tr tp (f + 16) (colL i) =
      (cv tr tp (f + i) sbIn + 256 * cv tr tp (f + i) sbOut) % 2013265921 := by
    intro hn i hi
    rw [rot hn (15 - i) (by omega) i hi, show f + 15 - (15 - i) = f + i by omega,
      show (i + 1 + (15 - i)) % 16 = 0 by omega]
    obtain ⟨hw, kw, -, -⟩ := KR i hi
    exact (key_reg hL hw kw).2.1
  refine ⟨fun i hi => ?_, l15, h16, limbs, ?_⟩
  · obtain ⟨hw, kw, cw, tw⟩ := KR i hi
    refine ⟨hw, kw, cw, tw, mult_of rfl (by simp only [zev_c, cur_cv, kw]; rfl), ?_⟩
    rw [i0_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, tw, cw]
  · have K := kinds hL h16
    have K15 := kinds hL h15
    have htf : cv tr tp f tau ≤ f := tau_le hL f hf (act_of hL hf (Or.inl hk))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.1 with ha | ha
    · exact Or.inl ha
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.1 with kk | kk
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.2.1 with kh | kh
        · -- an entry cannot follow a key row
          have he : cv tr tp (f + 16) kE = 1 := by omega
          have := prev_ent hL (by rw [show f + 15 + 1 = f + 16 by omega]; exact h16)
            (by rw [show f + 15 + 1 = f + 16 by omega]; exact he)
          omega
        · -- the first header
          have IC := inst_next hL h15 (Or.inr k15) (by rw [show f + 15 + 1 = f + 16 by omega]; exact h16)
            (by rw [show f + 15 + 1 = f + 16 by omega]; exact kk)
          rw [show f + 15 + 1 = f + 16 by omega] at IC
          obtain ⟨i1, i2, i3, i4⟩ := key_init hL h15 k15
          have hT := (hdr_valid hL h16 kh).1
          refine Or.inr (Or.inr ⟨kh, ?_, ?_, ?_, ?_, ?_⟩)
          · rw [IC tau (by simp [instCols]), t15]
          · rw [hT, IC Tq (by simp [instCols]), i2]
          · rw [IC kq (by simp [instCols]), i1]
          · rw [IC Kq (by simp [instCols]), i3]
          · rw [IC zq (by simp [instCols]), i4]
      · -- a new key block
        have := blk_next hL h15 (Or.inl l15) (by rw [show f + 15 + 1 = f + 16 by omega]; exact h16)
          (by rw [show f + 15 + 1 = f + 16 by omega]; exact kk)
        rw [show f + 15 + 1 = f + 16 by omega, t15] at this
        refine Or.inr (Or.inl ⟨kk, this.1, ?_⟩)
        rw [this.2]; omega

end

end ZkFormal.NearV3.Candidates.ProcSound
