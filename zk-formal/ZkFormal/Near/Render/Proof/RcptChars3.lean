import ZkFormal.Near.Render.Proof.RcptChars2

/-!
# ZkFormal.Near.Render.Proof.RcptChars3 — predecessor ≠ `system`, named receiver

The running sums of the predecessor (`Σ (p_j − "system"_j)²`) and receiver
(hex count) rows, and the final inverses, given that the three sums are
nonzero (`PredOk`, `NamedOk`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- The predecessor is not `system`. -/
def PredOk (d : RD) : Prop := Fp.ofNat (pP d) ≠ 0
/-- The receiver is named. -/
def NamedOk (d : RD) : Prop := Fp.ofNat (pV1 d) ≠ 0 ∧ Fp.ofNat (pV2 d) ≠ 0 ∧ Fp.ofNat (pV3 d) ≠ 0

theorem Cc_state0 {c : Claim} {e : Ext} {r s i st : Nat} (h1 : 5 ≤ st) (h2 : st ≤ 26) (hne : st ≠ s) :
    Cc c e (.seg r s i) st = 0 := by
  rw [Cc_seg _ _ _ _ _ _ (by omega)]
  simp only [segCell, show st < 31 by omega, if_true, show st ≠ 0 by omega, show st ≠ 1 by omega,
    show st ≠ 2 by omega, show st ≠ 3 by omega, show st ≠ 27 by omega, show st ≠ 28 by omega,
    show st ≠ 29 by omega, show st ≠ 30 by omega, show st ≠ 4 by omega, hne, if_false]

theorem cF_state0 {c : Claim} {e : Ext} {r s i st : Nat} (h1 : 5 ≤ st) (h2 : st ≤ 26) (hne : st ≠ s) :
    cF c e (.seg r s i) st = 0 := by
  simp only [cF, Cc_state0 h1 h2 hne]; rfl

/-- A constraint gated by another field's state vanishes. -/
theorem vanish {c : Claim} {e : Ext} {r s i st : Nat} (h1 : 5 ≤ st ∧ st ≤ 26) (hne : st ≠ s) {nx : Nat → Fp}
    {fst lst : Bool} {pub : List Fp} {x : Expr} (hz : Zr (· == st) (fun _ => false) false x = true) :
    evR (cF c e (.seg r s i)) nx fst lst pub x = 0 :=
  Zr_sound (fun y hy => by simp only [beq_iff_eq] at hy; subst hy; exact cF_state0 h1.1 h1.2 hne)
    (fun _ h => by cases h) (fun h => by cases h) x hz

theorem accP_zero (d : RD) : accP d 0 = sqd (d.pred.getD 0 0) (sysB 0) := runSum_zero _
theorem accP_succ (d : RD) (i : Nat) : accP d (i + 1) = accP d i + sqd (d.pred.getD (i + 1) 0) (sysB (i + 1)) :=
  runSum_succ _ i
theorem accV_zero (d : RD) : accV d 0 = b2n (isHexC (d.recv.getD 0 0)) := runSum_zero _
theorem accV_succ (d : RD) (i : Nat) : accV d (i + 1) = accV d i + b2n (isHexC (d.recv.getD (i + 1) 0)) :=
  runSum_succ _ i

theorem fLd_6 (d : RD) (pub : Array Nat) : fLd d pub 6 = [115, 121, 115, 116, 101, 109] := rfl
theorem sysB_eq (j : Nat) : sysB j = [115, 121, 115, 116, 101, 109].getD j 0 := rfl

section pred
variable {c : Claim} {e : Ext} {r i : Nat} {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp}

theorem pred_c1 :
    evR (cF c e (.seg r 6 i)) nx fst lst pub
      (mul3 (Dsl.c Rcpt.sP) (Dsl.c Rcpt.fs) (sub (Dsl.c Rcpt.acc) (Rcpt.sq (sub (Dsl.c Rcpt.b) (Dsl.c (Rcpt.reg 0)))))) = 0 := by
  simp only [Rcpt.sq, evR_mul3, evR_mul, evR_sub, evR_c, cF, rseg, S_reg _ _ _ _ _ (show 0 < 32 by decide), fLd_6,
    Nat.reduceEqDiff, ↓reduceIte, ofNat1, Nat.add_zero]
  by_cases h0 : i = 0
  · subst h0
    simp only [decide_true, b2n_true, ofNat1, accP_zero, ofNat_mod, ofNat_sqd, sysB_eq, segByte_str (Or.inl rfl),
      strOf, ↓reduceIte]
    grind
  · simp only [h0, decide_false, b2n_false, ofNat0]; grind

theorem pred_c2 (hi : i < (Df c e r).pred.length) :
    evR (cF c e (.seg r 6 i)) (cF c e (nextOf (Df c e) (.seg r 6 i))) fst lst pub
      (mul3 (Dsl.c Rcpt.sP) (Dsl.not (Dsl.c Rcpt.fe)) (sub (Dsl.n Rcpt.acc) (.add (Dsl.c Rcpt.acc)
        (Rcpt.sq (sub (Dsl.n Rcpt.b) (Dsl.n (Rcpt.reg 0))))))) = 0 := by
  by_cases hfe : i + 1 < (Df c e r).pred.length
  · rw [nextOf_in (by simpa [fLen] using hfe)]
    simp only [Rcpt.sq, evR_mul3, evR_mul, evR_add, evR_sub, evR_not, evR_c, evR_n, cF, rseg,
      S_reg _ _ _ _ _ (show 0 < 32 by decide), fLd_6, Nat.reduceEqDiff, ↓reduceIte, ofNat1, Nat.add_zero,
      accP_succ, ofNat_mod, ofNat_sqd, sysB_eq, segByte_str (Or.inl rfl), strOf, ofNat_add_e]
    grind
  · simp only [evR_mul3, evR_not, evR_c, cF, rseg, fLen, Nat.reduceEqDiff, ↓reduceIte,
      show i + 1 = (Df c e r).pred.length by omega, decide_true, b2n_true, ofNat1]
    grind

theorem pred_c3 :
    evR (cF c e (.seg r 6 i)) nx fst lst pub
      (mul3 (Dsl.c Rcpt.sP) (Dsl.c Rcpt.fe) (sub (Dsl.c Rcpt.p1) (.add (Dsl.c Rcpt.acc) (Rcpt.sq (sub (Dsl.c Rcpt.Lp)
        (Dsl.k 6)))))) = 0 := by
  simp only [Rcpt.sq, evR_mul3, evR_mul, evR_add, evR_sub, evR_c, evR_k, cF, rseg, fLen, Nat.reduceEqDiff,
    ↓reduceIte, ofNat1, true_and]
  by_cases hfe : i + 1 = (Df c e r).pred.length
  · have h1 : (Df c e r).pred.length - 1 = i := by omega
    simp only [hfe, decide_true, b2n_true, ↓reduceIte, pP, h1, ofNat_mod, ofNat_add_e, ofNat_sqd, natCast_eq]
    grind
  · simp only [hfe, decide_false, b2n_false, ofNat0]; grind

theorem pred_c4 (hP : PredOk (Df c e r)) :
    evR (cF c e (.seg r 6 i)) nx fst lst pub
      (mul3 (Dsl.c Rcpt.sP) (Dsl.c Rcpt.fe) (sub (.mul (Dsl.c Rcpt.p1) (Dsl.c Rcpt.isys)) (Dsl.k 1))) = 0 := by
  simp only [evR_mul3, evR_mul, evR_sub, evR_c, evR_k, cF, rseg, fLen, Nat.reduceEqDiff, ↓reduceIte, ofNat1,
    true_and]
  by_cases hfe : i + 1 = (Df c e r).pred.length
  · simp only [hfe, decide_true, b2n_true, ↓reduceIte, ofNat_invP hP, natCast_eq, ofNat1]; grind
  · simp only [hfe, decide_false, b2n_false, ofNat0]; grind

end pred

section named
variable {c : Claim} {e : Ext} {r i : Nat} {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp}

theorem hexE_val (hi : i < (Df c e r).recv.length) (hS : StrOk (Df c e r).recv) :
    evR (cF c e (.seg r 8 i)) nx fst lst pub Rcpt.hexE = Fp.ofNat (b2n (isHexC ((Df c e r).recv.getD i 0))) := by
  have hb := byte_ok (c := c) (e := e) (r := r) (i := i) (Or.inr (Or.inl rfl)) (by simpa [fLen] using hi) hS
  simp only [Rcpt.hexE, evR_add, evR_c, cF, rseg, isStr_of (Or.inr (Or.inl rfl) : (8 : Nat) = 6 ∨ 8 = 8 ∨ 8 = 12),
    ↓reduceIte, ofNat_add']
  rw [hex_char _ hb.1 hb.2, segByte_str (Or.inr (Or.inl rfl))]; rfl

theorem hexN_val (hi : i < (Df c e r).recv.length) (hS : StrOk (Df c e r).recv) {cur : Nat → Fp} :
    evR cur (cF c e (.seg r 8 i)) fst lst pub Rcpt.hexN = Fp.ofNat (b2n (isHexC ((Df c e r).recv.getD i 0))) := by
  rw [← hexE_val (nx := fun _ => 0) (fst := fst) (lst := lst) (pub := pub) hi hS]
  simp only [Rcpt.hexN, Rcpt.hexE, evR_add, evR_c, evR_n]

theorem named_c1 (hi : i < (Df c e r).recv.length) (hS : StrOk (Df c e r).recv) :
    evR (cF c e (.seg r 8 i)) nx fst lst pub (mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fs) (sub (Dsl.c Rcpt.acc) Rcpt.hexE)) = 0 := by
  simp only [evR_mul3, evR_sub, hexE_val hi hS]
  simp only [evR_c, cF, rseg, Nat.reduceEqDiff, ↓reduceIte, ofNat1]
  by_cases h0 : i = 0
  · subst h0; simp only [decide_true, b2n_true, ofNat1, accV_zero]; grind
  · simp only [h0, decide_false, b2n_false, ofNat0]; grind

theorem named_next (hi : i < (Df c e r).recv.length) (hS : StrOk (Df c e r).recv) {x : Expr}
    (hx : x ∈ [mul3 (Dsl.c Rcpt.sV) (Dsl.not (Dsl.c Rcpt.fe)) (sub (Dsl.n Rcpt.acc) (.add (Dsl.c Rcpt.acc) Rcpt.hexN)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.not (Dsl.c Rcpt.fe)) (sub (Dsl.n Rcpt.vc0) (Dsl.c Rcpt.vc0)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.not (Dsl.c Rcpt.fe)) (sub (Dsl.n Rcpt.vc1) (Dsl.c Rcpt.vc1)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.not (Dsl.c Rcpt.fe)) (sub (Dsl.n Rcpt.h01) (Dsl.c Rcpt.h01))]) :
    evR (cF c e (.seg r 8 i)) (cF c e (nextOf (Df c e) (.seg r 8 i))) fst lst pub x = 0 := by
  by_cases hfe : i + 1 < (Df c e r).recv.length
  · rw [nextOf_in (by simpa [fLen] using hfe)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [evR_mul3, evR_sub, evR_add, evR_not, hexN_val hfe hS]
      simp only [evR_c, evR_n, cF, rseg, Nat.reduceEqDiff, ↓reduceIte, ofNat1, accV_succ, ofNat_add_e]
      grind
    all_goals simp only [evR_mul3, evR_sub, evR_not, evR_c, evR_n, cF, rseg, Nat.reduceEqDiff, ↓reduceIte]; grind
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [evR_mul3, evR_not, evR_c, cF, rseg, fLen, Nat.reduceEqDiff, ↓reduceIte,
      show i + 1 = (Df c e r).recv.length by omega, decide_true, b2n_true, ofNat1] <;> grind

theorem named_first (hi : i < (Df c e r).recv.length) (hS : StrOk (Df c e r).recv) {x : Expr}
    (hx : x ∈ [mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fs) (sub (Dsl.c Rcpt.vc0) (Dsl.c Rcpt.b)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fs) (sub (Dsl.c Rcpt.vc1) (Dsl.n Rcpt.b)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fs) (sub (Dsl.c Rcpt.h01) (.add Rcpt.hexE Rcpt.hexN))]) :
    evR (cF c e (.seg r 8 i)) (cF c e (nextOf (Df c e) (.seg r 8 i))) fst lst pub x = 0 := by
  by_cases h0 : i = 0
  · subst h0
    have hL := hS.len
    have h1 : 1 < (Df c e r).recv.length := by omega
    rw [nextOf_in (by simpa [fLen] using h1)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [evR_mul3, evR_sub, evR_c, cF, rseg, Nat.reduceEqDiff, ↓reduceIte, segByte_str (Or.inr (Or.inl rfl)),
        strOf]
      grind
    · simp only [evR_mul3, evR_sub, evR_c, evR_n, cF, rseg, Nat.reduceEqDiff, ↓reduceIte,
        segByte_str (Or.inr (Or.inl rfl)), strOf]
      grind
    · simp only [evR_mul3, evR_sub, evR_add, hexE_val (i := 0) (by omega) hS, hexN_val h1 hS]
      simp only [evR_c, cF, rseg, Nat.reduceEqDiff, ↓reduceIte, h01V, ofNat_add_e]
      grind
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
    simp only [evR_mul3, evR_c, cF, rseg, h0, decide_false, b2n_false, ofNat0] <;> grind

theorem named_last (hi : i < (Df c e r).recv.length) (hN : NamedOk (Df c e r)) {x : Expr}
    (hx : x ∈ [mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fe) (sub (Dsl.c Rcpt.p1) (.add (Rcpt.sq (sub (Dsl.c Rcpt.Lv) (Dsl.k 64)))
        (Rcpt.sq (sub (Dsl.c Rcpt.acc) (Dsl.c Rcpt.Lv))))),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fe) (sub (Dsl.c Rcpt.p2) (sum [Rcpt.sq (sub (Dsl.c Rcpt.Lv) (Dsl.k 42)),
        Rcpt.sq (sub (Dsl.c Rcpt.vc0) (Dsl.k 48)), Rcpt.sq (sub (Dsl.c Rcpt.vc1) (Dsl.k 120)),
        Rcpt.sq (sub (sub (Dsl.c Rcpt.acc) (Dsl.c Rcpt.h01)) (Dsl.k 40))])),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fe) (sub (Dsl.c Rcpt.p3) (sum [Rcpt.sq (sub (Dsl.c Rcpt.Lv) (Dsl.k 42)),
        Rcpt.sq (sub (Dsl.c Rcpt.vc0) (Dsl.k 48)), Rcpt.sq (sub (Dsl.c Rcpt.vc1) (Dsl.k 115)),
        Rcpt.sq (sub (sub (Dsl.c Rcpt.acc) (Dsl.c Rcpt.h01)) (Dsl.k 40))])),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fe) (sub (.mul (Dsl.c Rcpt.p1) (Dsl.c Rcpt.i1)) (Dsl.k 1)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fe) (sub (.mul (Dsl.c Rcpt.p2) (Dsl.c Rcpt.i2)) (Dsl.k 1)),
      mul3 (Dsl.c Rcpt.sV) (Dsl.c Rcpt.fe) (sub (.mul (Dsl.c Rcpt.p3) (Dsl.c Rcpt.i3)) (Dsl.k 1))]) :
    evR (cF c e (.seg r 8 i)) nx fst lst pub x = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  by_cases hfe : i + 1 = (Df c e r).recv.length
  · have h1 : (Df c e r).recv.length - 1 = i := by omega
    obtain ⟨n1, n2, n3⟩ := hN
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Rcpt.sq, evR_mul3, evR_mul, evR_add, evR_sub, evR_c, evR_k, evR_sum_cons, evR_sum_nil, cF, rseg, fLen,
      Nat.reduceEqDiff, ↓reduceIte, ofNat1, true_and, false_and, and_true, hfe, decide_true, b2n_true] <;>
    first
    | (simp only [ofNat_invP n1, ofNat_invP n2, ofNat_invP n3, natCast_eq, ofNat1]; grind)
    | (simp only [pV1, pV2, pV3, h1, ofNat_mod, ofNat_add_e, ofNat_sqd, natCast_eq]; grind)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [evR_mul3, evR_c, cF, rseg, fLen, Nat.reduceEqDiff, ↓reduceIte, hfe, decide_false, b2n_false,
      ofNat0] <;> grind

end named

end RcptP

end ZkFormal.Near.Render
