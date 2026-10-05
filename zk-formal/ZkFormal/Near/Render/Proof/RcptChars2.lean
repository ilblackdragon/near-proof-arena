import ZkFormal.Near.Render.Proof.RcptChars1

/-!
# ZkFormal.Near.Render.Proof.RcptChars2 — separators and lengths of the account ids

On a string row (`P`, `V`, `S`): no leading, trailing or doubled separator,
and the length bits `L − 2`, `64 − L` on the field's last row.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

section
variable {c : Claim} {e : Ext} {r s i : Nat} (hs : s = 6 ∨ s = 8 ∨ s = 12) (hi : i < fLen (Df c e r) s)
  (hS : StrOk (strOf (Df c e r) s))
include hs hi hS

theorem byte_ok : segByte (Df c e r) (PA c e) s i < 256 ∧ vch (segByte (Df c e r) (PA c e) s i) = true := by
  rw [segByte_str hs]; rw [fLen_str hs] at hi; exact ⟨hS.byte i hi, hS.ch i hi⟩

omit hi hS in
theorem sepE_eq {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub Rcpt.sepE =
      Fp.ofNat (charCell (segByte (Df c e r) (PA c e) s i) 111 + charCell (segByte (Df c e r) (PA c e) s i) 113) := by
  simp only [Rcpt.sepE, evR_add, evR_c, cF, rseg, isStr_of hs, ↓reduceIte, ofNat_add']

theorem sepE_val {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub Rcpt.sepE = Fp.ofNat (b2n (sepB ((strOf (Df c e r) s).getD i 0))) := by
  rw [sepE_eq hs, sep_char _ (byte_ok hs hi hS).1 (byte_ok hs hi hS).2, segByte_str hs]

theorem SS_one {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub Rcpt.SS = 1 := by
  rcases hs with rfl | rfl | rfl <;>
  simp only [Rcpt.SS, evR_sum_cons, evR_sum_nil, evR_c, cF, rseg, Nat.reduceEqDiff, ↓reduceIte, ofNat0, ofNat1] <;>
  grind

theorem fs_val {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub (Dsl.c Rcpt.fs) = Fp.ofNat (b2n (decide (i = 0))) := by
  simp only [evR_c, cF, rseg]

theorem fe_val {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub (Dsl.c Rcpt.fe) =
      Fp.ofNat (b2n (decide (i + 1 = (strOf (Df c e r) s).length))) := by
  simp only [evR_c, cF, rseg, fLen_str hs]

/-- No doubled separator. -/
theorem sep_double {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) (cF c e (nextOf (Df c e) (.seg r s i))) fst lst pub
      (.mul (mul3 Rcpt.SS (Dsl.not (Dsl.c Rcpt.fe)) Rcpt.sepE) Rcpt.sepN) = 0 := by
  have hL := hi; rw [fLen_str hs] at hL
  simp only [evR_mul, evR_mul3, evR_not, SS_one hs hi hS, fe_val hs hi hS, sepE_val hs hi hS]
  by_cases hfe : i + 1 < (strOf (Df c e r) s).length
  · rw [nextOf_in (by rw [fLen_str hs]; exact hfe)]
    have hn : evR (cF c e (.seg r s (i + 1))) (fun _ => 0) fst lst pub Rcpt.sepE =
        Fp.ofNat (b2n (sepB ((strOf (Df c e r) s).getD (i + 1) 0))) :=
      sepE_val hs (by rw [fLen_str hs]; exact hfe) hS
    have hN : evR (cF c e (.seg r s i)) (cF c e (.seg r s (i + 1))) fst lst pub Rcpt.sepN =
        evR (cF c e (.seg r s (i + 1))) (fun _ => 0) fst lst pub Rcpt.sepE := by
      simp only [Rcpt.sepN, Rcpt.sepE, evR_add, evR_n, evR_c]
    rw [hN, hn]
    cases h1 : sepB ((strOf (Df c e r) s).getD i 0)
    · simp only [b2n_false, ofNat0]; grind
    · rw [(hS.sep i hL h1).2.2]; simp only [b2n_false, ofNat0]; grind
  · simp only [show i + 1 = (strOf (Df c e r) s).length by omega, decide_true, b2n_true, ofNat1]; grind

/-- No leading separator. -/
theorem sep_first {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub (mul3 Rcpt.SS (Dsl.c Rcpt.fs) Rcpt.sepE) = 0 := by
  have hL := hi; rw [fLen_str hs] at hL
  simp only [evR_mul3, SS_one hs hi hS, fs_val hs hi hS, sepE_val hs hi hS]
  by_cases h0 : i = 0
  · cases h1 : sepB ((strOf (Df c e r) s).getD i 0)
    · simp only [b2n_false, ofNat0]; grind
    · exact absurd h0 (hS.sep i hL h1).1
  · simp only [h0, decide_false, b2n_false, ofNat0]; grind

/-- No trailing separator. -/
theorem sep_last {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c e (.seg r s i)) nx fst lst pub (mul3 Rcpt.SS (Dsl.c Rcpt.fe) Rcpt.sepE) = 0 := by
  have hL := hi; rw [fLen_str hs] at hL
  simp only [evR_mul3, SS_one hs hi hS, fe_val hs hi hS, sepE_val hs hi hS]
  by_cases h0 : i + 1 = (strOf (Df c e r) s).length
  · cases h1 : sepB ((strOf (Df c e r) s).getD i 0)
    · simp only [b2n_false, ofNat0]; grind
    · exact absurd (hS.sep i hL h1).2.1 (by omega)
  · simp only [h0, decide_false, b2n_false, ofNat0]; grind

/-- The length bits on the last row. -/
theorem len_bits {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} (hfe : i + 1 = (strOf (Df c e r) s).length) :
    evR (cF c e (.seg r s i)) nx fst lst pub (Rcpt.bitsX 0 6) = Fp.ofNat ((strOf (Df c e r) s).length - 2) ∧
    evR (cF c e (.seg r s i)) nx fst lst pub (Rcpt.bitsX 6 6) = Fp.ofNat (64 - (strOf (Df c e r) s).length) := by
  have hL := hS.len
  have hx : ∀ j, j < 12 → cF c e (.seg r s i) (Rcpt.xb j) =
      Fp.ofNat (if j < 6 then bitOf ((strOf (Df c e r) s).length - 2) j
        else bitOf (64 - (strOf (Df c e r) s).length) (j - 6)) := by
    intro j hj
    simp only [cF, S_xb _ _ _ _ _ (show j < 66 by omega), segXb]
    have h15 : s ≠ 15 := by omega
    have h17 : s ≠ 17 := by omega
    rw [if_neg h15, if_neg h17, if_pos ⟨isStr_of hs, by rw [fLen_str hs]; exact hfe⟩, fLen_str hs]
    by_cases h6 : j < 6
    · simp [h6]
    · simp [h6, show j < 12 by omega]
  constructor
  · rw [evR_bitsX (v := fun j => if j < 6 then bitOf ((strOf (Df c e r) s).length - 2) j
        else bitOf (64 - (strOf (Df c e r) s).length) (j - 6)) 0 6 (fun j _ h => hx j (by omega))]
    congr 1
    exact bitsVal_pool (fun j hj => by simp [show j < 6 by omega]) (by
      have : (strOf (Df c e r) s).length - 2 < 64 := by omega
      exact this)
  · rw [evR_bitsX (v := fun j => if j < 6 then bitOf ((strOf (Df c e r) s).length - 2) j
        else bitOf (64 - (strOf (Df c e r) s).length) (j - 6)) 6 6 (fun j h1 h2 => hx j (by omega))]
    congr 1
    exact bitsVal_pool (fun j hj => by simp [show ¬ (6 + j < 6) by omega]) (by
      have : 64 - (strOf (Df c e r) s).length < 64 := by omega
      exact this)

end

end RcptP

end ZkFormal.Near.Render
