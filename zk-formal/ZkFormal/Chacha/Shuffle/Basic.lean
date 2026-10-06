import ZkFormal.Chacha.Shuffle.Table
import ZkFormal.Chacha.Rng.Sound

/-!
# ZkFormal.Chacha.Shuffle.Basic — local facts of `shufV3`

Row-local consequences of the constraints, and the walk from any active row back to the
first row of its instance (`walkStart`).
-/

namespace ZkFormal.Chacha.Shuffle

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Rng (ofNat_inj)

abbrev SLocal := Local Shuffle.Table.constraints

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem mem_cB {x : Nat} (hx : x ∈ boolCols) : ZkFormal.Chacha.Table.boolC x ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; left; left; exact List.mem_map.mpr ⟨x, hx, rfl⟩
theorem mem_cM {e : Expr} (h : e ∈ cM) : e ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; left; right; exact h
theorem mem_cK {e : Expr} (h : e ∈ cK) : e ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; right; exact h

theorem bit (hL : SLocal tr t pub) {r x : Nat} (hr : r < tr.height t) (h1 : 30 ≤ x) (h2 : x < 77) :
    cv tr t r x ≤ 1 :=
  hL.bool hr (mem_cB (by unfold boolCols; simp only [List.mem_range'_1]; omega))

theorem zev_numS (r : Nat) (col : Nat → Nat) (len : Nat) :
    zev (tenv tr t r pub) (ZkFormal.Chacha.Rng.Table.num col len) = (numv tr t r col len : Int) :=
  zev_sum_pow _ _ _ len (fun b _ => rfl)

section
variable (hL : SLocal tr t pub)
include hL

theorem bA {r : Nat} (hr : r < tr.height t) : cv tr t r colA ≤ 1 := bit hL hr (by decide) (by decide)
theorem bSt {r : Nat} (hr : r < tr.height t) : cv tr t r colSt ≤ 1 := bit hL hr (by decide) (by decide)
theorem bFin {r : Nat} (hr : r < tr.height t) : cv tr t r colFin ≤ 1 := bit hL hr (by decide) (by decide)
theorem bEq {r : Nat} (hr : r < tr.height t) : cv tr t r colEq ≤ 1 := bit hL hr (by decide) (by decide)
theorem bS2 {r : Nat} (hr : r < tr.height t) : cv tr t r colS2 ≤ 1 := bit hL hr (by decide) (by decide)

theorem numLt {r : Nat} (hr : r < tr.height t) {col : Nat → Nat} (hc : ∀ b, b < 14 → 30 ≤ col b ∧ col b < 77) :
    numv tr t r col 14 < 2 ^ 14 := nbits_lt (fun b hb => bit hL hr (hc b hb).1 (hc b hb).2)

/-- Evaluate a product constraint `x · e` on a row where `x = 1`. -/
theorem zc1 {r : Nat} (hr : r < tr.height t) {x : Nat} {e : Expr} (hx : cv tr t r x = 1)
    (he : Expr.mul (ZkFormal.Chacha.Table.E.c x) e ∈ cM)
    (h1 : -2013265921 < zev (tenv tr t r pub) e) (h2 : zev (tenv tr t r pub) e < 2013265921) :
    zev (tenv tr t r pub) e = 0 := by
  have := hL.zc hr (mem_cM he)
  rw [zev_mul, zev_c, cur_cv, hx, show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul] at this
  exact this h1 h2

theorem fin_a {r : Nat} (hr : r < tr.height t) (h : cv tr t r colFin = 1) : cv tr t r colA = 1 := by
  have := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1)
    (ZkFormal.Chacha.Table.E.c colA)) (by simp [cM])
  simp only [zev_sub, zev_k, zev_c, cur_cv] at this
  have hb := bA hL hr; have := this (by omega) (by omega); omega

theorem st_a {r : Nat} (hr : r < tr.height t) (h : cv tr t r colSt = 1) : cv tr t r colA = 1 := by
  have := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1)
    (ZkFormal.Chacha.Table.E.c colA)) (by simp [cM])
  simp only [zev_sub, zev_k, zev_c, cur_cv] at this
  have hb := bA hL hr; have := this (by omega) (by omega); omega

/-- The final row: `q = 0`, `eqj = 1`, `j = 0`. -/
theorem fin_facts {r : Nat} (hr : r < tr.height t) (h : cv tr t r colFin = 1) :
    cv tr t r colQ = 0 ∧ cv tr t r colEq = 1 ∧ cv tr t r colJ = 0 := by
  have h1 := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.c colQ) (by simp [cM])
  have h2 := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1)
    (ZkFormal.Chacha.Table.E.c colEq)) (by simp [cM])
  simp only [zev_sub, zev_k, zev_c, cur_cv] at h1 h2
  have := cv_lt (tr := tr) (t := t) r colQ; have := bEq hL hr
  have e1 := h1 (by omega) (by omega); have e2 := h2 (by omega) (by omega)
  have h3 := zc1 hL hr (x := colEq) (by omega) (e := ZkFormal.Chacha.Table.E.sub
    (ZkFormal.Chacha.Table.E.c colJ) (ZkFormal.Chacha.Table.E.c colQ)) (by simp [cM])
  simp only [zev_sub, zev_c, cur_cv] at h3
  have := cv_lt (tr := tr) (t := t) r colJ
  have e3 := h3 (by omega) (by omega)
  omega

/-- `s2 = a·(1 − fin)·(1 − eqj)`. -/
theorem s2_eq {r : Nat} (hr : r < tr.height t) :
    (cv tr t r colS2 : Int) = cv tr t r colA * (1 - cv tr t r colFin) * (1 - cv tr t r colEq) := by
  have hz := hL.zc hr (mem_cM (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colS2)
    (.mul (.mul (ZkFormal.Chacha.Table.E.c colA) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1)
      (ZkFormal.Chacha.Table.E.c colFin))) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1)
      (ZkFormal.Chacha.Table.E.c colEq)))) (by simp [cM]))
  simp only [zev_sub, zev_mul, zev_k, zev_c, cur_cv] at hz
  have := bA hL hr; have := bFin hL hr; have := bEq hL hr; have := bS2 hL hr
  rcases (show cv tr t r colA = 0 ∨ cv tr t r colA = 1 by omega) with e1 | e1 <;>
  rcases (show cv tr t r colFin = 0 ∨ cv tr t r colFin = 1 by omega) with e2 | e2 <;>
  rcases (show cv tr t r colEq = 0 ∨ cv tr t r colEq = 1 by omega) with e3 | e3 <;>
  (rw [e1, e2, e3] at hz ⊢; simp at hz ⊢; have := hz (by omega) (by omega); omega)

/-- `eqj = 1 → j = q`; on an active row `eqj = 0 → j < q`. -/
theorem eqj_facts {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) (hq : cv tr t r colQ < 2 ^ 20)
    (hj : cv tr t r colJ < 2 ^ 20) :
    (cv tr t r colEq = 1 → cv tr t r colJ = cv tr t r colQ) ∧
    (cv tr t r colEq = 0 → cv tr t r colJ < cv tr t r colQ) := by
  have := bEq hL hr; have := cv_lt (tr := tr) (t := t) r colJ
  constructor
  · intro h
    have h3 := zc1 hL hr (x := colEq) h (e := ZkFormal.Chacha.Table.E.sub
      (ZkFormal.Chacha.Table.E.c colJ) (ZkFormal.Chacha.Table.E.c colQ)) (by simp [cM])
    simp only [zev_sub, zev_c, cur_cv] at h3
    have e3 := h3 (by omega) (by omega); omega
  · intro h
    have hz := hL.zc hr (mem_cM (e := .mul (.mul (ZkFormal.Chacha.Table.E.c colA)
      (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1) (ZkFormal.Chacha.Table.E.c colEq)))
      (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub
        (ZkFormal.Chacha.Table.E.c colQ) (ZkFormal.Chacha.Table.E.c colJ)) (ZkFormal.Chacha.Table.E.k 1)) djE))
      (by simp [cM]))
    simp only [zev_mul, zev_sub, zev_k, zev_c, cur_cv, ha, h, djE, zev_numS] at hz
    have := numLt hL hr (col := colDj) (fun b hb => by unfold colDj; omega)
    have := hz (by omega) (by omega)
    omega

/-- Stamps of the reads are larger than `q`. -/
theorem t1_gt {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) (hq : cv tr t r colQ < 2 ^ 20) :
    cv tr t r colQ < cv tr t r colT1 := by
  have h := zc1 hL hr (x := colA) ha (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub
    (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colT1) (ZkFormal.Chacha.Table.E.c colQ))
    (ZkFormal.Chacha.Table.E.k 1)) d1E) (by simp [cM])
  simp only [zev_sub, zev_k, zev_c, cur_cv, d1E, zev_numS] at h
  have := numLt hL hr (col := colD1) (fun b hb => by unfold colD1; omega)
  have := cv_lt (tr := tr) (t := t) r colT1
  have := h (by omega) (by omega); omega

theorem t2_gt {r : Nat} (hr : r < tr.height t) (hs : cv tr t r colS2 = 1) (hq : cv tr t r colQ < 2 ^ 20) :
    cv tr t r colQ < cv tr t r colT2 := by
  have h := zc1 hL hr (x := colS2) hs (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub
    (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colT2) (ZkFormal.Chacha.Table.E.c colQ))
    (ZkFormal.Chacha.Table.E.k 1)) d2E) (by simp [cM])
  simp only [zev_sub, zev_k, zev_c, cur_cv, d2E, zev_numS] at h
  have := numLt hL hr (col := colD2) (fun b hb => by unfold colD2; omega)
  have := cv_lt (tr := tr) (t := t) r colT2
  have := h (by omega) (by omega); omega

/-- The row counter. -/
theorem rc_eq (hH : tr.height t ≤ 2 ^ 20) : ∀ r, r < tr.height t → cv tr t r colRc = r := by
  intro r hr
  induction r with
  | zero =>
    have := hL.zc hr (mem_cM (e := .mul .isFirst (ZkFormal.Chacha.Table.E.c colRc)) (by simp [cM]))
    simp only [zev_mul, zev_isFirst, zev_c, cur_cv] at this
    simp [tenv] at this
    have hc := cv_lt (tr := tr) (t := t) 0 colRc
    have := this (by omega) (by omega); omega
  | succ r ih =>
    have := hL.zc (show r < _ by omega) (mem_cM (e := .mul .isTransition (ZkFormal.Chacha.Table.E.sub
      (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n colRc) (ZkFormal.Chacha.Table.E.c colRc))
      (ZkFormal.Chacha.Table.E.k 1))) (by simp [cM]))
    simp only [zev_mul, zev_sub, zev_n, zev_c, zev_k, cur_cv, nxt_cv hr, ih (by omega)] at this
    simp only [zev, tenv, show ¬ (r + 1 = tr.height t) by omega, ite_false] at this
    have hc := cv_lt (tr := tr) (t := t) (r + 1) colRc
    have := this (by omega) (by omega); omega

/-- First row of an instance: `q + 1 = L`, `kq = ks`, `inst = rc`. -/
theorem start_facts (hH : tr.height t ≤ 2 ^ 20) {r : Nat} (hr : r < tr.height t) (h : cv tr t r colSt = 1) :
    (cv tr t r colQ + 1) % 2013265921 = cv tr t r colL ∧ cv tr t r colKq = cv tr t r colKs ∧
    cv tr t r colInst = r := by
  have h1 := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.sub (.add (ZkFormal.Chacha.Table.E.c colQ)
    (ZkFormal.Chacha.Table.E.k 1)) (ZkFormal.Chacha.Table.E.c colL)) (by simp [cM])
  have h2 := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colKq)
    (ZkFormal.Chacha.Table.E.c colKs)) (by simp [cM])
  have h3 := zc1 hL hr h (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c colInst)
    (ZkFormal.Chacha.Table.E.c colRc)) (by simp [cM])
  simp only [zev_sub, zev_add, zev_k, zev_c, cur_cv] at h1 h2 h3
  have c1 := cv_lt (tr := tr) (t := t) r colQ; have c2 := cv_lt (tr := tr) (t := t) r colL
  have c3 := cv_lt (tr := tr) (t := t) r colKq; have c4 := cv_lt (tr := tr) (t := t) r colKs
  have c5 := cv_lt (tr := tr) (t := t) r colInst; have hrc := rc_eq hL hH r hr
  refine ⟨?_, by have := h2 (by omega) (by omega); omega, by have := h3 (by omega) (by omega); omega⟩
  by_cases hq : cv tr t r colQ + 1 < 2013265921
  · rw [Nat.mod_eq_of_lt hq]; have := h1 (by omega) (by omega); omega
  · have e : cv tr t r colQ + 1 = 2013265921 := by omega
    rw [e, Nat.mod_self]
    rcases Nat.eq_zero_or_pos (cv tr t r colL) with h0 | h0
    · exact h0.symm
    · have := h1 (by omega) (by omega); omega

theorem first_start (ha : cv tr t 0 colA = 1) : cv tr t 0 colSt = 1 := by
  have hz := hL.zc (Nat.two_pow_pos _) (mem_cM (e := .mul .isFirst (ZkFormal.Chacha.Table.E.sub
    (ZkFormal.Chacha.Table.E.c colA) (ZkFormal.Chacha.Table.E.c colSt))) (by simp [cM]))
  simp only [zev_mul, zev_isFirst, zev_sub, zev_c, cur_cv, ha] at hz
  simp [tenv] at hz
  have := bSt hL (Nat.two_pow_pos (tr.log t)) (r := 0)
  have := hz (by omega) (by omega); omega

/-- `n.a − n.st = a − fin`. -/
theorem trans0 {r : Nat} (hr : r + 1 < tr.height t) :
    (cv tr t (r + 1) colA : Int) - cv tr t (r + 1) colSt = (cv tr t r colA : Int) - cv tr t r colFin := by
  have hz := hL.zc (show r < _ by omega) (mem_cM (e := ZkFormal.Chacha.Table.E.sub
    (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n colA) (ZkFormal.Chacha.Table.E.n colSt)) gStep)
    (by simp [cM]))
  simp only [zev_sub, zev_n, zev_c, nxt_cv hr, cur_cv, gStep] at hz
  have := bA hL (show r < _ by omega); have := bFin hL (show r < _ by omega)
  have := bA hL hr; have := bSt hL hr
  have := hz (by omega) (by omega); omega

/-- A step row continues the instance on the next row. -/
theorem cont {r : Nat} (hr : r + 1 < tr.height t) (ha : cv tr t r colA = 1) (hf : cv tr t r colFin = 0) :
    cv tr t (r + 1) colA = 1 ∧ cv tr t (r + 1) colSt = 0 ∧
    (cv tr t (r + 1) colQ + 1) % 2013265921 = cv tr t r colQ ∧
    cv tr t (r + 1) colL = cv tr t r colL ∧ cv tr t (r + 1) colLid = cv tr t r colLid ∧
    cv tr t (r + 1) colInst = cv tr t r colInst ∧ cv tr t (r + 1) colKs = cv tr t r colKs ∧
    cv tr t (r + 1) colKq = cv tr t r colKn ∧
    (∀ j l, j < 8 → l < 2 → cv tr t (r + 1) (colK j l) = cv tr t r (colK j l)) := by
  have hr0 : r < tr.height t := by omega
  have t0 := trans0 hL hr; rw [ha, hf] at t0
  have := bA hL hr; have := bSt hL hr
  have hg : zev (tenv tr t r pub) gStep = 1 := by
    simp [gStep, zev_sub, zev_c, cur_cv, ha, hf]
  have cp : ∀ x y : Nat, Expr.mul gStep (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n x)
      (ZkFormal.Chacha.Table.E.c y)) ∈ cM → cv tr t (r + 1) x = cv tr t r y := by
    intro x y hm
    have hz := hL.zc hr0 (mem_cM hm)
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_n, zev_c, nxt_cv hr, cur_cv] at hz
    have := cv_lt (tr := tr) (t := t) (r + 1) x; have := cv_lt (tr := tr) (t := t) r y
    have := hz (by omega) (by omega); omega
  refine ⟨by omega, by omega, ?_, cp _ _ (by simp [cM]), cp _ _ (by simp [cM]), cp _ _ (by simp [cM]),
    cp _ _ (by simp [cM]), cp _ _ (by simp [cM]), fun j l hj hl => ?_⟩
  · have hz := hL.zc hr0 (mem_cM (e := .mul gStep (ZkFormal.Chacha.Table.E.sub (.add
      (ZkFormal.Chacha.Table.E.n colQ) (ZkFormal.Chacha.Table.E.k 1)) (ZkFormal.Chacha.Table.E.c colQ)))
      (by simp [cM]))
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_add, zev_n, zev_c, zev_k, nxt_cv hr, cur_cv] at hz
    have q1 := cv_lt (tr := tr) (t := t) (r + 1) colQ; have q2 := cv_lt (tr := tr) (t := t) r colQ
    simp only [show ((1 : Nat) : Int) = 1 from rfl] at hz
    by_cases hq : cv tr t (r + 1) colQ + 1 < 2013265921
    · rw [Nat.mod_eq_of_lt hq]; have hz' := hz (by omega) (by omega); omega
    · have e : cv tr t (r + 1) colQ + 1 = 2013265921 := by omega
      rw [e, Nat.mod_self]
      rcases Nat.eq_zero_or_pos (cv tr t r colQ) with h0 | h0
      · exact h0.symm
      · have hz' := hz (by omega) (by omega); omega
  · have hz := hL.zc hr0 (mem_cK (e := .mul gStep (ZkFormal.Chacha.Table.E.sub
      (ZkFormal.Chacha.Table.E.n (colK j l)) (ZkFormal.Chacha.Table.E.c (colK j l))))
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩))
    rw [zev_mul, hg, Int.one_mul, zev_sub, zev_n, zev_c, nxt_cv hr, cur_cv] at hz
    have := cv_lt (tr := tr) (t := t) (r + 1) (colK j l); have := cv_lt (tr := tr) (t := t) r (colK j l)
    have := hz (by omega) (by omega); omega

end

end ZkFormal.Chacha.Shuffle
