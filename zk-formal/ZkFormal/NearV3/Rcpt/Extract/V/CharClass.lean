import ZkFormal.NearV3.Rcpt.Extract.V.Chars

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.CharClass — character classes of an account-id byte

On a `P`/`V`/`S` row the byte `16·hi + lo` is a lowercase letter, a digit or
a separator `- . _`; `sepE` is the separator indicator, `hexE` the
hex-digit indicator.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The class of a character `16·hi + lo`. -/
def ClassOK (hi lo : Nat) : Prop :=
  (hi = 2 ∧ (lo = 13 ∨ lo = 14)) ∨ (hi = 3 ∧ lo ≤ 9) ∨ (hi = 5 ∧ lo = 15) ∨ (hi = 6 ∧ 1 ≤ lo ∧ lo < 16) ∨
    (hi = 7 ∧ lo ≤ 10)

theorem cvb {q x : Nat} (h : tr.cell tt q x = 0 ∨ tr.cell tt q x = 1) :
    (tr.cell tt q x = 0 ∧ cv tr tt q x = 0) ∨ (tr.cell tt q x = 1 ∧ cv tr tt q x = 1) := by
  rcases h with e | e
  · exact Or.inl ⟨e, by simp [cv, e, Fp.toNat_zero]⟩
  · exact Or.inr ⟨e, by simp [cv, e, Fp.toNat_one]⟩

theorem lbC (j : Nat) (hj : j < 4) : lb j ∈ charCols := by
  unfold charCols; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨j, hj, rfl⟩

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

set_option maxHeartbeats 1000000 in
/-- **Character class.** -/
theorem char_class {q X : Nat} (hq : q < tr.height tt) (hX : X = sP ∨ X = sV ∨ X = sS)
    (h1 : tr.cell tt q X = 1) :
    ClassOK (hiV tr tt q) (loV tr tt q) ∧
    sepE.eval tr tt q pub = (if hiV tr tt q = 2 ∨ hiV tr tt q = 5 then 1 else 0) ∧
    hexE.eval tr tt q pub = (if hiV tr tt q = 3 ∨ (hiV tr tt q = 6 ∧ loV tr tt q ≤ 6) then 1 else 0) := by
  have hSS := SS_eval hL hq hX h1
  have cb : ∀ x ∈ charCols, tr.cell tt q x = 0 ∨ tr.cell tt q x = 1 := fun x hx => charBool hL hq hx
  have k1 := con hL hq (e := .mul SS (sub (sum [c h2, c h3, c h5, c h6, c h7]) (k 1))) (mem_ch (by simp [cChars]))
  have k2 := con hL hq (e := mul3 (c h3) (lb' 3) (lb' 2)) (mem_ch (by simp [cChars]))
  have k3 := con hL hq (e := mul3 (c h3) (lb' 3) (lb' 1)) (mem_ch (by simp [cChars]))
  have k4 := con hL hq (e := .mul (c z) loE) (mem_ch (by simp [cChars]))
  have k5 := con hL hq (e := mul3 SS (Dsl.not (c z)) (sub (.mul loE (c linv)) (k 1))) (mem_ch (by simp [cChars]))
  have k6 := con hL hq (e := .mul (c h6) (c z)) (mem_ch (by simp [cChars]))
  have k7 := con hL hq (e := mul3 (c h7) (lb' 3) (lb' 2)) (mem_ch (by simp [cChars]))
  have k8 := con hL hq (e := .mul (mul3 (c h7) (lb' 3) (lb' 1)) (lb' 0)) (mem_ch (by simp [cChars]))
  have k9 := con hL hq (e := .mul (c h2) (Dsl.not (lb' 3))) (mem_ch (by simp [cChars]))
  have k10 := con hL hq (e := .mul (c h2) (Dsl.not (lb' 2))) (mem_ch (by simp [cChars]))
  have k11 := con hL hq (e := .mul (c h2) (sub (.add (lb' 1) (lb' 0)) (k 1))) (mem_ch (by simp [cChars]))
  have k12 := con hL hq (e := .mul (c h5) (Dsl.not (lb' 0))) (mem_ch (by simp [cChars]))
  have k13 := con hL hq (e := .mul (c h5) (Dsl.not (lb' 1))) (mem_ch (by simp [cChars]))
  have k14 := con hL hq (e := .mul (c h5) (Dsl.not (lb' 2))) (mem_ch (by simp [cChars]))
  have k15 := con hL hq (e := .mul (c h5) (Dsl.not (lb' 3))) (mem_ch (by simp [cChars]))
  have k16 := con hL hq (e := sub (c l210) (mul3 (lb' 2) (lb' 1) (lb' 0))) (mem_ch (by simp [cChars]))
  have k17 := con hL hq (e := .mul (c hx6) (Dsl.not (c h6))) (mem_ch (by simp [cChars]))
  have k18 := con hL hq (e := .mul (c hx6) (lb' 3)) (mem_ch (by simp [cChars]))
  have k19 := con hL hq (e := .mul (c hx6) (c l210)) (mem_ch (by simp [cChars]))
  have k20 := con hL hq (e := mul3 (sub (c h6) (c hx6)) (Dsl.not (lb' 3)) (Dsl.not (c l210))) (mem_ch (by simp [cChars]))
  simp only [lb', loE, bits, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.map_append, eval_sum_append, eval_mul, eval_mul3, eval_sub, eval_add, eval_smul, eval_c, eval_k, eval_not,
    eval_sum_cons, eval_sum_nil, hSS, Nat.zero_add, Nat.reduceAdd, Nat.reducePow] at k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20
  have e210 : tr.cell tt q l210 = tr.cell tt q (lb 2) * tr.cell tt q (lb 1) * tr.cell tt q (lb 0) := by
    grind
  rw [e210] at k19 k20
  simp only [ClassOK, hiV, loV, bitsVal, sepE, hexE, eval_add, eval_c, Nat.zero_add]
  rcases cvb (cb h2 (by simp [charCols])) with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
  rcases cvb (cb h3 (by simp [charCols])) with ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
  rcases cvb (cb h5 (by simp [charCols])) with ⟨a5, b5⟩ | ⟨a5, b5⟩ <;>
  rcases cvb (cb h6 (by simp [charCols])) with ⟨a6, b6⟩ | ⟨a6, b6⟩ <;>
  rcases cvb (cb h7 (by simp [charCols])) with ⟨a7, b7⟩ | ⟨a7, b7⟩ <;>
  simp only [a2, a3, a5, a6, a7, b2, b3, b5, b6, b7] at k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k17 k18 k19 k20 ⊢ <;>
  (try (exfalso; revert k1; decide)) <;>
  rcases cvb (cb (lb 0) (lbC 0 (by omega))) with ⟨l0, m0⟩ | ⟨l0, m0⟩ <;>
  rcases cvb (cb (lb 1) (lbC 1 (by omega))) with ⟨l1, m1⟩ | ⟨l1, m1⟩ <;>
  rcases cvb (cb (lb 2) (lbC 2 (by omega))) with ⟨l2, m2⟩ | ⟨l2, m2⟩ <;>
  rcases cvb (cb (lb 3) (lbC 3 (by omega))) with ⟨l3, m3⟩ | ⟨l3, m3⟩ <;>
  simp only [l0, l1, l2, l3, m0, m1, m2, m3] at k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k17 k18 k19 k20 ⊢ <;>
  (try (exfalso; first | (revert k2; decide) | (revert k3; decide) | (revert k7; decide) | (revert k8; decide) |
    (revert k9; decide) | (revert k10; decide) | (revert k11; decide) | (revert k12; decide) |
    (revert k13; decide) | (revert k14; decide) | (revert k15; decide))) <;>
  rcases cvb (cb hx6 (by simp [charCols])) with ⟨x6, -⟩ | ⟨x6, -⟩ <;>
  simp only [x6] at k17 k18 k19 k20 ⊢ <;>
  (try (exfalso; first | (revert k17; decide) | (revert k18; decide) | (revert k19; decide) | (revert k20; decide))) <;>
  rcases cvb (cb z (by simp [charCols])) with ⟨zz, -⟩ | ⟨zz, -⟩ <;>
  simp only [zz] at k4 k5 k6 <;>
  (try (exfalso; first | (revert k4; decide) | (revert k6; decide) | grind)) <;>
  decide

end ZkFormal.NearV3.RcptV3Proof
