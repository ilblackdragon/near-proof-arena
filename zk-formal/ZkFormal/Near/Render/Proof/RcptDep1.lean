import ZkFormal.Near.Render.Proof.RcptGas3
import ZkFormal.Near.Render.Proof.RcptDepF

/-!
# ZkFormal.Near.Render.Proof.RcptDep1 — cells of the `DEP` rows; the split of `cDep`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

def pA : List Expr :=
  [ .mul Rcpt.dp (sub (sum [c Rcpt.bef, c Rcpt.b, c Rcpt.c1]) (.add Rcpt.aftE (smul 256 (c (Rcpt.xb 8))))),
    .mul (.mul Rcpt.dp (c Rcpt.fs)) (c Rcpt.c1), mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c1) (c (Rcpt.xb 8))),
    mul3 Rcpt.dp (c Rcpt.fe) (c (Rcpt.xb 8)),
    mul3 Rcpt.dp (c Rcpt.fs) (sub (c Rcpt.dsum) (sub (k 255) Rcpt.aftE)),
    mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.dsum) (.add (c Rcpt.dsum) (sub (k 255) (Rcpt.bitsXn 0 8)))),
    mul3 Rcpt.dp (c Rcpt.fe) (sub (.mul (c Rcpt.dsum) (c Rcpt.invB)) (k 1)) ]
def pB : List Expr :=
  [ .mul Rcpt.dp (sub (sum [Rcpt.aftE, c Rcpt.lk, c Rcpt.c2]) (.add (Rcpt.bitsX 9 8) (smul 256 (c (Rcpt.xb 17))))),
    .mul (.mul Rcpt.dp (c Rcpt.fs)) (c Rcpt.c2), mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c2) (c (Rcpt.xb 17))),
    mul3 Rcpt.dp (c Rcpt.fe) (c (Rcpt.xb 17)) ]
def pC : List Expr :=
  [ .mul Rcpt.dp (sub (.add (Rcpt.conv Rcpt.S_LE (c Rcpt.st) dD) (c Rcpt.c3))
      (.add (Rcpt.bitsX 18 8) (smul 256 (Rcpt.bitsX 26 12)))),
    .mul (.mul Rcpt.dp (c Rcpt.fs)) (c Rcpt.c3), mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c3) (Rcpt.bitsX 26 12)),
    mul3 Rcpt.dp (c Rcpt.fe) (Rcpt.bitsX 26 12),
    mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n (Rcpt.dl 0)) (c Rcpt.st)) ]
def pD : List Expr :=
  [ .mul Rcpt.dp (sub (sub (Rcpt.bitsX 9 8) (Rcpt.bitsX 18 8))
      (sub (.add (c Rcpt.c4) (Rcpt.bitsX 38 8)) (smul 256 (c (Rcpt.xb 46))))),
    .mul (.mul Rcpt.dp (c Rcpt.fs)) (c Rcpt.c4), mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c4) (c (Rcpt.xb 46))),
    .mul (mul3 Rcpt.dp (c Rcpt.fe) (c Rcpt.big)) (c (Rcpt.xb 46)) ]
def pE : List Expr :=
  [ .mul (c Rcpt.r1) (Dsl.not Rcpt.dp), mul3 Rcpt.dp (c Rcpt.fs) (c Rcpt.r1),
    mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.r1) (c Rcpt.fs)),
    mul3 (Dsl.not (c Rcpt.big)) (c Rcpt.r1) (sub (k 770) (sum [c (Rcpt.dl 0), smul 256 (c Rcpt.st), Rcpt.bitsX 47 10])),
    mul3 (Dsl.not (c Rcpt.big)) (sub (sub Rcpt.dp (c Rcpt.fs)) (c Rcpt.r1)) (c Rcpt.st),
    mul3 Rcpt.dp (c Rcpt.fs) (sub (sub (c Rcpt.r) (c Rcpt.tprev)) (Rcpt.bitsX 57 9)) ]
def pF : List Expr :=
  (List.range 7).map (fun j => mul3 Rcpt.dp (c Rcpt.fs) (dD j)) ++
  (List.range 6).map (fun j => mul3 Rcpt.dp (Dsl.not (c Rcpt.fe)) (sub (n (Rcpt.dl (j + 1))) (dD j)))

theorem cDep_eq : Rcpt.cDep = pA ++ pB ++ pC ++ pD ++ pE ++ pF := rfl

/-! ## `DEP` pools -/

section
variable {d : RD} {bg : Nat → Nat} {i : Nat}

theorem dx_A {j : Nat} (hj : j < 8) : segXb d bg 17 i (0 + j) = bitOf (Seg.sa d i % 256) j := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte, Nat.zero_add, hj]
theorem dx_8 : segXb d bg 17 i 8 = bitOf (Seg.sa d i / 256) 0 := by simp [segXb]
theorem dx_B {j : Nat} (hj : j < 8) : segXb d bg 17 i (9 + j) = bitOf (Seg.stt d i % 256) j := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem dx_17 : segXb d bg 17 i 17 = bitOf (Seg.stt d i / 256) 0 := by simp [segXb]
theorem dx_C {j : Nat} (hj : j < 8) : segXb d bg 17 i (18 + j) = bitOf (Seg.sq d i % 256) j := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem dx_D {j : Nat} (hj : j < 12) : segXb d bg 17 i (26 + j) = bitOf (Seg.sq d i / 256) j := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem dx_E {j : Nat} (hj : j < 8) : segXb d bg 17 i (38 + j) = bitOf (Seg.ddv d i) j := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem dx_46 : segXb d bg 17 i 46 = bitOf (Seg.dbr d (i + 1)) 0 := by simp [segXb]
theorem dx_F {j : Nat} (hj : j < 10) : segXb d bg 17 i (47 + j) =
    if i = 1 ∧ d.big = false then bitOf (770 - (Seg.stB d 0 + 256 * Seg.stB d 1)) j else 0 := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]
  split <;> simp only [show 47 + j - 47 = j by omega]
theorem dx_G {j : Nat} (hj : j < 9) : segXb d bg 17 i (57 + j) =
    if i = 0 then bitOf (d.r - d.tprev) j else 0 := by
  simp only [segXb, Nat.reduceEqDiff, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]
  split <;> simp only [show 57 + j - 57 = j by omega]

end

/-! ## `DEP` cells -/

section
variable {c : Claim} {e : Ext} {r i : Nat}

theorem dp_one : cF c e (.seg r 17 i) Rcpt.sDEP = 1 := by
  rw [show Rcpt.sDEP = 17 from rfl, cF_st 17 (by omega) (by omega)]; rfl
theorem dp_fe : cF c e (.seg r 17 i) Rcpt.fe = if i = 15 then 1 else 0 := by
  rw [cF_fe, show fLen (Df c e r) 17 = 16 from rfl]
  by_cases h : i = 15
  · subst h; rfl
  · rw [if_neg (by omega), if_neg h]
theorem dp_b : cF c e (.seg r 17 i) Rcpt.b = Fp.ofNat (Seg.depB (Df c e r) i) := by simp only [cF, S_b]; rfl
theorem dp_bef : cF c e (.seg r 17 i) Rcpt.bef = Fp.ofNat (Seg.befB (Df c e r) i) := by simp only [cF, S_bef]; rfl
theorem dp_lk : cF c e (.seg r 17 i) Rcpt.lk = Fp.ofNat (Seg.lkB (Df c e r) i) := by simp only [cF, S_lk]; rfl
theorem dp_st : cF c e (.seg r 17 i) Rcpt.st = Fp.ofNat (Seg.stB (Df c e r) i) := by simp only [cF, S_st]; rfl
theorem dp_c1 : cF c e (.seg r 17 i) Rcpt.c1 = Fp.ofNat (chain (Seg.y1 (Df c e r)) i) := by simp only [cF, S_c1]; rfl
theorem dp_c2 : cF c e (.seg r 17 i) Rcpt.c2 = Fp.ofNat (chain (Seg.y2 (Df c e r)) i) := by simp only [cF, S_c2]; rfl
theorem dp_c3 : cF c e (.seg r 17 i) Rcpt.c3 = Fp.ofNat (chain (Seg.y3 (Df c e r)) i) := by simp only [cF, S_c3]; rfl
theorem dp_c4 : cF c e (.seg r 17 i) Rcpt.c4 = Fp.ofNat (Seg.dbr (Df c e r) i) := by simp only [cF, S_c4]; rfl
theorem dp_dsum : cF c e (.seg r 17 i) Rcpt.dsum = Fp.ofNat (Seg.runA (Df c e r) i) := by simp only [cF, S_dsum]; rfl
theorem dp_invB : cF c e (.seg r 17 i) Rcpt.invB =
    Fp.ofNat (if i + 1 = 16 then invP (Seg.runA (Df c e r) i) else 0) := by simp only [cF, S_invB]; rfl
theorem dp_dl {j : Nat} (hj : j < 7) :
    cF c e (.seg r 17 i) (Rcpt.dl j) = Fp.ofNat (if j < i then Seg.stB (Df c e r) (i - 1 - j) else 0) := by
  simp only [cF, S_dl c e r 17 i (show j < 8 by omega), Nat.reduceEqDiff, ↓reduceIte, show 208 + j < 215 by omega]
theorem dp_r1 : cF c e (.seg r 17 i) Rcpt.r1 = if i = 1 then 1 else 0 := by
  simp only [cF, S_r1]; by_cases h : i = 1 <;> simp [h, b2n] <;> rfl
theorem cF_big {s : Nat} : cF c e (.seg r s i) Rcpt.big = Fp.ofNat (b2n (Df c e r).big) := by simp only [cF, S_big]
theorem cF_r1 {s : Nat} : cF c e (.seg r s i) Rcpt.r1 = Fp.ofNat (b2n (decide (s = 17 ∧ i = 1))) := by simp only [cF, S_r1]
theorem cF_st' {s : Nat} : cF c e (.seg r s i) Rcpt.st = Fp.ofNat (if s = 17 then Seg.stB (Df c e r) i else 0) := by
  simp only [cF, S_st]; by_cases h : s = 15 <;> simp [h]

end

end RcptP

end ZkFormal.Near.Render
