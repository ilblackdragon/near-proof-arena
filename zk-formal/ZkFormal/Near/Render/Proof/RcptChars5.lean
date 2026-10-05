import ZkFormal.Near.Render.Proof.RcptChars4

/-!
# ZkFormal.Near.Render.Proof.RcptChars5 — `cChars` on the honest rows (`chars_ok`)
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

section
variable {c : Claim} {e : Ext} {r s i : Nat} (hs : s = 6 ∨ s = 8 ∨ s = 12) (hi : i < fLen (Df c e r) s)
  (hS : StrOk (strOf (Df c e r) s))
include hs hi hS

theorem len_lo {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {st Lc : Nat}
    (hst : cF c e (.seg r s i) st = 1) (hL : cF c e (.seg r s i) Lc = Fp.ofNat (strOf (Df c e r) s).length) :
    evR (cF c e (.seg r s i)) nx fst lst pub
      (mul3 (Dsl.c Rcpt.fe) (Dsl.c st) (sub (sub (Dsl.c Lc) (Dsl.k 2)) (Rcpt.bitsX 0 6))) = 0 := by
  have hl := hS.len
  simp only [evR_mul3, evR_sub, evR_k, fe_val hs hi hS]
  simp only [evR_c, hst, hL]
  by_cases hfe : i + 1 = (strOf (Df c e r) s).length
  · rw [(len_bits hs hi hS hfe).1, ofNat_sub (by omega : 2 ≤ (strOf (Df c e r) s).length)]
    simp only [hfe, decide_true, b2n_true, natCast_eq, ofNat1]; grind
  · simp only [hfe, decide_false, b2n_false, ofNat0]; grind

theorem len_hi {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {st Lc : Nat}
    (hst : cF c e (.seg r s i) st = 1) (hL : cF c e (.seg r s i) Lc = Fp.ofNat (strOf (Df c e r) s).length) :
    evR (cF c e (.seg r s i)) nx fst lst pub
      (mul3 (Dsl.c Rcpt.fe) (Dsl.c st) (sub (sub (Dsl.k 64) (Dsl.c Lc)) (Rcpt.bitsX 6 6))) = 0 := by
  have hl := hS.len
  simp only [evR_mul3, evR_sub, evR_k, fe_val hs hi hS]
  simp only [evR_c, hst, hL]
  by_cases hfe : i + 1 = (strOf (Df c e r) s).length
  · rw [(len_bits hs hi hS hfe).2, ofNat_sub (by omega : (strOf (Df c e r) s).length ≤ 64)]
    simp only [hfe, decide_true, b2n_true, natCast_eq, ofNat1]; grind
  · simp only [hfe, decide_false, b2n_false, ofNat0]; grind

end

open ZkFormal.Near.Rcpt in
/-- The boolean part of `cChars`. -/
def cA : List Expr := ([h2, h3, h5, h6, h7, z, hx6] ++ (List.range 4).map lb).map (fun x => Dsl.bool (Dsl.c x))

open ZkFormal.Near.Rcpt in
/-- The non-boolean part of `cChars`. -/
def cB : List Expr :=
  [ .mul SS (sub (c b) (.add (smul 16 hiE) loE)),
    .mul SS (sub (sum [c h2, c h3, c h5, c h6, c h7]) (k 1)),
    -- low nibble ranges per high nibble
    mul3 (c h3) (lb' 3) (lb' 2), mul3 (c h3) (lb' 3) (lb' 1),
    .mul (c z) loE, mul3 SS (not (c z)) (sub (.mul loE (c linv)) (k 1)),
    .mul (c h6) (c z),
    mul3 (c h7) (lb' 3) (lb' 2), .mul (mul3 (c h7) (lb' 3) (lb' 1)) (lb' 0),
    .mul (c h2) (not (lb' 3)), .mul (c h2) (not (lb' 2)), .mul (c h2) (sub (.add (lb' 1) (lb' 0)) (k 1)),
    .mul (c h5) (not (lb' 0)), .mul (c h5) (not (lb' 1)), .mul (c h5) (not (lb' 2)),
    .mul (c h5) (not (lb' 3)),
    -- hex letters a–f
    sub (c l210) (mul3 (lb' 2) (lb' 1) (lb' 0)),
    .mul (c hx6) (not (c h6)), .mul (c hx6) (lb' 3), .mul (c hx6) (c l210),
    mul3 (sub (c h6) (c hx6)) (not (lb' 3)) (not (c l210)),
    -- separators: not first, not last, never doubled
    .mul (mul3 SS (not (c fe)) sepE) sepN, mul3 SS (c fs) sepE, mul3 SS (c fe) sepE,
    -- lengths 2..64
    mul3 (c fe) (c sP) (sub (sub (c Lp) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sV) (sub (sub (c Lv) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sS) (sub (sub (c Ls) (k 2)) (bitsX 0 6)),
    -- … and ≤ 64 (`L − 2 < 64` alone allows 65)
    mul3 (c fe) (c sP) (sub (sub (k 64) (c Lp)) (bitsX 6 6)),
    mul3 (c fe) (c sV) (sub (sub (k 64) (c Lv)) (bitsX 6 6)),
    mul3 (c fe) (c sS) (sub (sub (k 64) (c Ls)) (bitsX 6 6)),
    -- predecessor ≠ "system"
    mul3 (c sP) (c fs) (sub (c acc) (sq (sub (c b) (c (reg 0))))),
    mul3 (c sP) (not (c fe)) (sub (n acc) (.add (c acc) (sq (sub (n b) (n (reg 0)))))),
    mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (sq (sub (c Lp) (k 6))))),
    mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (k 1)),
    -- named receiver
    mul3 (c sV) (c fs) (sub (c acc) hexE),
    mul3 (c sV) (not (c fe)) (sub (n acc) (.add (c acc) hexN)),
    mul3 (c sV) (c fs) (sub (c vc0) (c b)), mul3 (c sV) (c fs) (sub (c vc1) (n b)),
    mul3 (c sV) (c fs) (sub (c h01) (.add hexE hexN)),
    mul3 (c sV) (not (c fe)) (sub (n vc0) (c vc0)), mul3 (c sV) (not (c fe)) (sub (n vc1) (c vc1)),
    mul3 (c sV) (not (c fe)) (sub (n h01) (c h01)),
    mul3 (c sV) (c fe) (sub (c p1) (.add (sq (sub (c Lv) (k 64))) (sq (sub (c acc) (c Lv))))),
    mul3 (c sV) (c fe) (sub (c p2) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 120)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (c p3) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 115)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (.mul (c p1) (c i1)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p2) (c i2)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p3) (c i3)) (k 1)) ]

theorem cChars_eq : Rcpt.cChars = cA ++ cB := rfl

theorem cA_loc : ∀ x ∈ cA, charLoc x = true := by decide

set_option maxHeartbeats 1000000 in
/-- **`cChars` on a string row.** -/
theorem str_rows {c : Claim} {e : Ext} {r s i : Nat} (hs : s = 6 ∨ s = 8 ∨ s = 12) (hi : i < fLen (Df c e r) s)
    (hS : StrOk (strOf (Df c e r) s)) (hP : s = 6 → PredOk (Df c e r)) (hN : s = 8 → NamedOk (Df c e r))
    {fst lst : Bool} {pub : List Fp} :
    ∀ x ∈ Rcpt.cChars, evR (cF c e (.seg r s i)) (cF c e (nextOf (Df c e) (.seg r s i))) fst lst pub x = 0 := by
  have hb := byte_ok hs hi hS
  intro x hx
  have hx0 := hx
  rw [cChars_eq, List.mem_append] at hx
  rcases hx with hA | hB
  · exact chars_loc hs hb hx0 (cA_loc x hA)
  simp only [cB, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact chars_loc hs hb hx0 (by decide)
  · subst h; exact sep_double hs hi hS
  · subst h; exact sep_first hs hi hS
  · subst h; exact sep_last hs hi hS
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact len_lo (Or.inl rfl) hi hS (by simp [cF, rseg, ofNat1]) (by simp [cF, rseg, strOf])
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact len_lo (Or.inr (Or.inl rfl)) hi hS (by simp [cF, rseg, ofNat1]) (by simp [cF, rseg, strOf])
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 12) (by decide) (by decide) (by decide)
    · exact vanish (st := 12) (by decide) (by decide) (by decide)
    · exact len_lo (Or.inr (Or.inr rfl)) hi hS (by simp [cF, rseg, ofNat1]) (by simp [cF, rseg, strOf])
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact len_hi (Or.inl rfl) hi hS (by simp [cF, rseg, ofNat1]) (by simp [cF, rseg, strOf])
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact len_hi (Or.inr (Or.inl rfl)) hi hS (by simp [cF, rseg, ofNat1]) (by simp [cF, rseg, strOf])
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 12) (by decide) (by decide) (by decide)
    · exact vanish (st := 12) (by decide) (by decide) (by decide)
    · exact len_hi (Or.inr (Or.inr rfl)) hi hS (by simp [cF, rseg, ofNat1]) (by simp [cF, rseg, strOf])
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact pred_c1
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact pred_c2 (by simpa [fLen] using hi)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact pred_c3
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact pred_c4 (hP rfl)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
    · exact vanish (st := 6) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_c1 (by simpa [fLen] using hi) hS
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_next (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_first (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_first (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_first (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_next (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_next (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_next (by simpa [fLen] using hi) hS (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_last (by simpa [fLen] using hi) (hN rfl) (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_last (by simpa [fLen] using hi) (hN rfl) (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_last (by simpa [fLen] using hi) (hN rfl) (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_last (by simpa [fLen] using hi) (hN rfl) (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_last (by simpa [fLen] using hi) (hN rfl) (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
  · subst h
    rcases hs with rfl | rfl | rfl
    · exact vanish (st := 8) (by decide) (by decide) (by decide)
    · exact named_last (by simpa [fLen] using hi) (hN rfl) (by simp)
    · exact vanish (st := 8) (by decide) (by decide) (by decide)

/-- Character columns and the string states. -/
def charZ (x : Nat) : Bool := x == 6 || x == 8 || x == 12 || (111 ≤ x && x ≤ 123)

theorem chars_zr : Rcpt.cChars.all (Zr charZ (fun _ => false) false) = true := by decide
theorem chars_zrP : Rcpt.cChars.all (Zr (fun _ => true) (fun _ => false) true) = true := by decide

theorem charZ_cl {c : Claim} {e : Ext} (i : Nat) : ∀ x, charZ x = true → Cc c e (.cl i) x = 0 := by
  intro x hx
  have hr : x = 6 ∨ x = 8 ∨ x = 12 ∨ x = 111 ∨ x = 112 ∨ x = 113 ∨ x = 114 ∨ x = 115 ∨ x = 116 ∨
      x = 117 ∨ x = 118 ∨ x = 119 ∨ x = 120 ∨ x = 121 ∨ x = 122 ∨ x = 123 := by
    simp only [charZ, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hx; omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Cc_cl, clCell, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte,
    ite_self, and_false, false_and, and_true, true_and]

theorem charZ_seg {c : Claim} {e : Ext} {r s i : Nat} (hs : ¬ (s = 6 ∨ s = 8 ∨ s = 12)) :
    ∀ x, charZ x = true → Cc c e (.seg r s i) x = 0 := by
  intro x hx
  have hr : x = 6 ∨ x = 8 ∨ x = 12 ∨ (111 ≤ x ∧ x ≤ 123) := by
    simp only [charZ, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hx; omega
  have hst : isStr s = false := by
    simp only [isStr, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
  rcases hr with rfl | rfl | rfl | ⟨h1, h2⟩
  · exact Cc_state0 (show 5 ≤ 6 by decide) (show 6 ≤ 26 by decide) (fun h => hs (Or.inl h.symm))
  · exact Cc_state0 (show 5 ≤ 8 by decide) (show 8 ≤ 26 by decide) (fun h => hs (Or.inr (Or.inl h.symm)))
  · exact Cc_state0 (show 5 ≤ 12 by decide) (show 12 ≤ 26 by decide) (fun h => hs (Or.inr (Or.inr h.symm)))
  · rw [Cc_seg _ _ _ _ _ _ (by omega)]
    simp only [segCell, show ¬ x < 31 by omega, show ¬ x < 43 by omega, show ¬ x < 63 by omega,
      show ¬ x < 95 by omega, show ¬ x < 111 by omega, show x < 124 by omega, hst, if_false, if_true]
    rfl

/-- **`cChars` on the honest rows.** -/
theorem chars_ok {c : Claim} {e : Ext} (hg : Good c e) {pub : List Fp} :
    ∀ x ∈ Rcpt.cChars, ∀ q, q < (render c e).height T_RCPT → x.eval (render c e) T_RCPT q pub = 0 := by
  intro x hx
  apply allRows_of hg
  · intro ρ hρ _ _
    have hok := RL_ok hg ρ hρ
    cases ρ with
    | cl i =>
      have hz := List.all_eq_true.1 chars_zr x hx
      exact zr_rec (f0 := false) (charZ_cl i) (zn := fun _ => false) (fun _ h => by cases h) (fun h => by cases h) hz
    | seg r s i =>
      obtain ⟨hr, -, hi⟩ := hok
      by_cases h : s = 6 ∨ s = 8 ∨ s = 12
      · have hS : StrOk (strOf (Df c e r) s) := by
          rcases h with rfl | rfl | rfl
          · exact pred_ok hg hr
          · exact recv_ok hg hr
          · exact signer_ok hg hr
        exact str_rows h hi hS (fun h6 => by subst h6; exact predOk hg hr) (fun h8 => by subst h8; exact namedOk hg hr)
          x hx
      · have hz := List.all_eq_true.1 chars_zr x hx
        exact zr_rec (f0 := false) (charZ_seg h) (zn := fun _ => false) (fun _ h => by cases h) (fun h => by cases h) hz
  · obtain ⟨r, s, i, he, hs⟩ := lastRec_eq c e
    rw [he]
    have hz := List.all_eq_true.1 chars_zr x hx
    exact zr_last (f0 := false) (charZ_seg (by omega)) (fun h => by cases h) (Zr_mono_n (fun _ _ => rfl) hz)
  · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 chars_zrP x hx)
  · exact zr_pad (zn := fun _ => false) (fun _ h => by cases h) (List.all_eq_true.1 chars_zrP x hx)

end RcptP

end ZkFormal.Near.Render
