import ZkFormal.Near.Render.Proof.RcptGas1

/-!
# ZkFormal.Near.Render.Proof.RcptGas2 — `cGas`: the split; borrow chain, refund flag, delay lines

On row `i` of a `GP` field (`i < 16`, next row the field's next row when
`i < 15`): `Rcpt.gp − bgp` with borrow (`gA`), the refund flag (`gE`), the delay
lines of `p` and the surplus (`gF`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

def dD (j : Nat) : Expr := c (Rcpt.dl j)

def gA : List Expr :=
  [ .mul Rcpt.gp (sub (sub (c Rcpt.b) (c (Rcpt.reg 0))) (sub (.add (c Rcpt.c1) Rcpt.DE) (smul 256 (c (Rcpt.xb 8))))),
    .mul (.mul Rcpt.gp (c Rcpt.fs)) (c Rcpt.c1), mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c1) (c (Rcpt.xb 8))),
    mul3 Rcpt.gp (c Rcpt.fe) (sub (c (Rcpt.xb 8)) (Dsl.not (c Rcpt.ge))) ]
def gB : List Expr :=
  [ .mul Rcpt.gp (sub (.add (c Rcpt.burnt) (smul 256 (Rcpt.bitsX 9 11))) (.add (Rcpt.conv (Rcpt.G_LE.take 5) Rcpt.pE dD) (c Rcpt.c2))),
    .mul (.mul Rcpt.gp (c Rcpt.fs)) (c Rcpt.c2), mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c2) (Rcpt.bitsX 9 11)),
    mul3 Rcpt.gp (c Rcpt.fe) (Rcpt.bitsX 9 11), mul3 Rcpt.gp (c Rcpt.fe) (Rcpt.ovf Rcpt.pE dD) ]
def gC : List Expr :=
  [ .mul Rcpt.gp (sub (.add (c Rcpt.ramt) (smul 256 (Rcpt.bitsX 20 11)))
      (.add (Rcpt.conv (Rcpt.G_LE.take 5) Rcpt.surE (fun j => dD (4 + j))) (c Rcpt.c3))),
    .mul (.mul Rcpt.gp (c Rcpt.fs)) (c Rcpt.c3), mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c3) (Rcpt.bitsX 20 11)),
    mul3 Rcpt.gp (c Rcpt.fe) (Rcpt.bitsX 20 11), mul3 Rcpt.gp (c Rcpt.fe) (Rcpt.ovf Rcpt.surE (fun j => dD (4 + j))) ]
def gD : List Expr :=
  [ .mul Rcpt.gp (sub (.add (Rcpt.bitsX 31 8) (smul 256 (c (Rcpt.xb 39)))) (sum [c (Rcpt.tok 0), c Rcpt.burnt, c Rcpt.c4])),
    .mul (.mul Rcpt.gp (c Rcpt.fs)) (c Rcpt.c4), mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.c4) (c (Rcpt.xb 39))),
    mul3 Rcpt.gp (c Rcpt.fe) (c (Rcpt.xb 39)) ]
def gE : List Expr :=
  [ .mul (mul3 Rcpt.gp (Dsl.not (c Rcpt.hr)) (c Rcpt.ge)) Rcpt.DE,
    mul3 Rcpt.gp (c Rcpt.fs) (sub (c Rcpt.sumD) Rcpt.DE),
    mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n Rcpt.sumD) (.add (c Rcpt.sumD) Rcpt.DEn)),
    mul3 Rcpt.gp (c Rcpt.fe) (sub (.mul (c Rcpt.sumD) (c Rcpt.invA)) (c Rcpt.hr)) ]
def gF : List Expr :=
  (List.range 8).map (fun j => mul3 Rcpt.gp (c Rcpt.fs) (dD j)) ++
  [ mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n (Rcpt.dl 0)) Rcpt.pE), mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n (Rcpt.dl 4)) Rcpt.surE) ] ++
  ([1, 2, 3, 5, 6, 7].map fun j => mul3 Rcpt.gp (Dsl.not (c Rcpt.fe)) (sub (n (Rcpt.dl j)) (dD (j - 1))))

theorem cGas_eq : Rcpt.cGas = gA ++ gB ++ gC ++ gD ++ gE ++ gF := rfl

/-- Cast a `Nat` equation to `Fp`. -/
theorem fp_eq {a b : Nat} (h : a = b) : Fp.ofNat a = Fp.ofNat b := by rw [h]

section
variable {c : WfClaim} {e : Ext} {r i : Nat}

theorem gp_one : cF c.1 e (.seg r 15 i) Rcpt.sGP = 1 := by rw [cF_sGP]; rfl
theorem gp_fe : cF c.1 e (.seg r 15 i) Rcpt.fe = if i = 15 then 1 else 0 := by
  rw [cF_fe, show fLen (Df c.1 e r) 15 = 16 from rfl]
  by_cases h : i = 15
  · subst h; rfl
  · rw [if_neg (by omega), if_neg h]

theorem gp_DE (G : GasOk (Df c.1 e r) (BG c.1) c.1.blockGasPrice) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c.1 e (.seg r 15 i)) nx fst lst pub Rcpt.DE = Fp.ofNat (Seg.gdv (Df c.1 e r) (BG c.1) i) :=
  bitsX_seg (by decide) (fun j hj => gx_D hj) (gdv_lt G i)

theorem gp_xb8 (G : GasOk (Df c.1 e r) (BG c.1) c.1.blockGasPrice) :
    cF c.1 e (.seg r 15 i) (Rcpt.xb 8) = Fp.ofNat (Seg.gbr (Df c.1 e r) (BG c.1) (i + 1)) := by
  rw [cF_xb (by decide), gx_8, bitOf_small (gbr_lt G _)]

theorem gp_pE (hh : Link.Hdr c) (hi : i < 16) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c.1 e (.seg r 15 i)) nx fst lst pub Rcpt.pE = Fp.ofNat (Seg.pB (Df c.1 e r) (BG c.1) i) := by
  simp only [Rcpt.pE, evR_add, evR_mul, evR_not, evR_c, gp_ge, gp_reg0 hi, PA_bgp hh hi, gp_b, Seg.pB]
  cases (Df c.1 e r).ge <;> simp only [b2n_true, b2n_false, ofNat0, ofNat1, ↓reduceIte, Bool.false_eq_true] <;> grind

theorem gp_surE (G : GasOk (Df c.1 e r) (BG c.1) c.1.blockGasPrice) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    evR (cF c.1 e (.seg r 15 i)) nx fst lst pub Rcpt.surE = Fp.ofNat (Seg.surB (Df c.1 e r) (BG c.1) i) := by
  simp only [Rcpt.surE, evR_mul, evR_c, gp_ge, gp_DE G, Seg.surB]
  cases (Df c.1 e r).ge <;> simp only [b2n_true, b2n_false, ofNat0, ofNat1, ↓reduceIte, Bool.false_eq_true] <;> grind

/-- **`gA`, `gE`, `gF` on a `GP` row.** -/
theorem gp_AEF (hg : Good c.1 e) (hr : r < NN e) (hi : i < 16) {nx : Nat → Fp}
    (hn : i < 15 → nx = cF c.1 e (.seg r 15 (i + 1))) :
    ∀ x ∈ gA ++ gE ++ gF, evR (cF c.1 e (.seg r 15 i)) nx false false (publicOf c) x = 0 := by
  have G := gasOk hg hr (Link.wf_bounds c).2.2.1
  have hh : Link.Hdr c := ⟨hg.pv, hg.chain⟩
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (hA | hE) | hF
  · simp only [gA, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · simp only [Rcpt.gp, evR_mul, evR_sub, evR_add, evR_c, evR_smul, gp_one, gp_b, gp_reg0 hi, PA_bgp hh hi, gp_c1,
        gp_DE G, gp_xb8 G]
      have E := fp_eq (gdv_step G i)
      simp only [ofNat_add_e, ofNat_mul_e] at E
      simp only [natCast_eq]; grind
    · simp only [Rcpt.gp, evR_mul, evR_c, gp_one, cF_fs, gp_c1]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, gbr_zero G, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_c, evR_n, gp_one, gp_fe, gp_xb8 G]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), gp_c1]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_c, gp_one, gp_fe, gp_xb8 G, gp_ge]
      by_cases h15 : i = 15
      · subst h15
        rw [show 15 + 1 = 16 from rfl, gbr_final G]
        cases (Df c.1 e r).ge <;> simp only [↓reduceIte, Bool.not_true, Bool.not_false, b2n_true, b2n_false,
          ofNat0, ofNat1] <;> grind
      · simp only [h15, ↓reduceIte]; grind
  · simp only [gE, List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · simp only [Rcpt.gp, evR_mul, evR_mul3, evR_not, evR_c, gp_one, gp_hr, gp_ge, gp_DE G]
      cases hh' : (Df c.1 e r).hr
      · cases hge : (Df c.1 e r).ge
        · simp only [b2n_false, ofNat0]; grind
        · rw [gdv_noref G hh' hge hi]; simp only [b2n_false, ofNat0]; grind
      · simp only [b2n_true, ofNat1]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_sub, evR_c, gp_one, cF_fs, gp_sumD, gp_DE G]
      by_cases h0 : i = 0
      · subst h0; simp only [↓reduceIte, runSum_zero]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_add, evR_c, evR_n, gp_one, gp_fe, gp_sumD]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), gp_sumD, runSum_succ, ofNat_add_e]
        rw [Rcpt.DEn, bitsXn_seg (by decide) (fun j hj => gx_D hj) (gdv_lt G (i + 1))]
        grind
    · simp only [Rcpt.gp, evR_mul3, evR_mul, evR_sub, evR_c, gp_one, gp_fe, gp_sumD, gp_invA, gp_hr]
      by_cases h15 : i = 15
      · subst h15
        cases hh' : (Df c.1 e r).hr
        · simp only [Bool.false_eq_true, and_false, ↓reduceIte, b2n_false, ofNat0]; grind
        · simp only [and_self, ↓reduceIte, b2n_true, ofNat1]
          rw [ofNat_invP (ofNat_ne_zero (gdv_ref G hh') (by
            have := runSum_gdv_lt G 15 (by omega); have : 4096 < ZkFormal.Algebra.P := by decide
            rw [P_def]; omega))]
          grind
      · simp only [h15, ↓reduceIte]; grind
  · simp only [gF, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with (⟨j, hj, rfl⟩ | (rfl | rfl)) | ⟨j, hj, rfl⟩
    · simp only [Rcpt.gp, dD, evR_mul3, evR_c, gp_one, cF_fs]
      by_cases h0 : i = 0
      · subst h0
        simp only [↓reduceIte, cF, S_dl c.1 e r 15 0 hj, Nat.not_lt_zero, ite_self, ofNat0]; grind
      · simp only [h0, ↓reduceIte]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_n, evR_c, gp_one, gp_fe, gp_pE hh hi]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega), gp_dlP (show 0 < 4 by decide),
          show 0 < i + 1 by omega, show i + 1 - 1 - 0 = i by omega]; grind
    · simp only [Rcpt.gp, evR_mul3, evR_not, evR_sub, evR_n, evR_c, gp_one, gp_fe, gp_surE G]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · rw [hn (by omega), show Rcpt.dl 4 = Rcpt.dl (4 + 0) from rfl, gp_dlS (show 0 < 4 by decide)]
        simp only [h15, ↓reduceIte, show 0 < i + 1 by omega, show i + 1 - 1 - 0 = i by omega]; grind
    · simp only [Rcpt.gp, dD, evR_mul3, evR_not, evR_sub, evR_n, evR_c, gp_one, gp_fe]
      by_cases h15 : i = 15
      · simp only [h15, ↓reduceIte]; grind
      · simp only [h15, ↓reduceIte, hn (by omega)]
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [gp_dlP (show 1 < 4 by decide), gp_dlP (show 0 < 4 by decide)]
          simp only [show (1 < i + 1) = (0 < i) by apply propext; omega, show i + 1 - 1 - 1 = i - 1 - 0 by omega]; grind
        · rw [gp_dlP (show 2 < 4 by decide), gp_dlP (show 1 < 4 by decide)]
          simp only [show (2 < i + 1) = (1 < i) by apply propext; omega, show i + 1 - 1 - 2 = i - 1 - 1 by omega]; grind
        · rw [gp_dlP (show 3 < 4 by decide), gp_dlP (show 2 < 4 by decide)]
          simp only [show (3 < i + 1) = (2 < i) by apply propext; omega, show i + 1 - 1 - 3 = i - 1 - 2 by omega]; grind
        · rw [show Rcpt.dl 5 = Rcpt.dl (4 + 1) from rfl, show Rcpt.dl (5 - 1) = Rcpt.dl (4 + 0) from rfl,
            gp_dlS (show 1 < 4 by decide), gp_dlS (show 0 < 4 by decide)]
          simp only [show (1 < i + 1) = (0 < i) by apply propext; omega, show i + 1 - 1 - 1 = i - 1 - 0 by omega]; grind
        · rw [show Rcpt.dl 6 = Rcpt.dl (4 + 2) from rfl, show Rcpt.dl (6 - 1) = Rcpt.dl (4 + 1) from rfl,
            gp_dlS (show 2 < 4 by decide), gp_dlS (show 1 < 4 by decide)]
          simp only [show (2 < i + 1) = (1 < i) by apply propext; omega, show i + 1 - 1 - 2 = i - 1 - 1 by omega]; grind
        · rw [show Rcpt.dl 7 = Rcpt.dl (4 + 3) from rfl, show Rcpt.dl (7 - 1) = Rcpt.dl (4 + 2) from rfl,
            gp_dlS (show 3 < 4 by decide), gp_dlS (show 2 < 4 by decide)]
          simp only [show (3 < i + 1) = (2 < i) by apply propext; omega, show i + 1 - 1 - 3 = i - 1 - 2 by omega]; grind

end

end RcptP

end ZkFormal.Near.Render
