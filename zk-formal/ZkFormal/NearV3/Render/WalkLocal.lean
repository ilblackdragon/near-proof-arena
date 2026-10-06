import ZkFormal.NearV3.Render.WalkGen
import ZkFormal.NearV3.Render.UniqLocal

/-!
# ZkFormal.NearV3.Render.WalkLocal — the honest `walkV3` table is locally legal

Constraint by constraint, for any trace whose table `tt` has height `H ≥ rows L` and cells
`Fp.ofNat (WalkGen.cell L H q col)` on rows `q < H`, columns `col < 56`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open ZkFormal.NearV3.WalkV3 (act ws we gK w tau sym nN nI nib nN2 nI2 ek u mS mK mB mD inv hv ub fk kk bmb
  bmE selIdx selSum selBit absE modes boolCols)
open WalkGen
open UniqLocal (ofNat0 ofNat1 boolF ofNat_succ)

namespace WalkLocal

theorem fp_ne {a b : Nat} (ha : a < ZkFormal.Algebra.P) (hb : b < ZkFormal.Algebra.P) (h : a ≠ b) :
    Fp.ofNat a - Fp.ofNat b ≠ 0 := by
  intro h0
  have : Fp.ofNat a = Fp.ofNat b := by grind
  exact h (ofNat_inj ha hb this)

theorem rows_pos {L : List WalkR} (hok : WalkOk L) : 0 < rows L := by
  cases L with
  | nil => exact absurd hok.pos (by simp)
  | cons wv l =>
    have := len2 hok (wv := wv) (by simp)
    simp only [rows, List.map_cons, List.sum_cons]; omega

theorem sum_ind (P : Prop) [Decidable P] (s : Nat) (g : Nat → Nat) : ∀ n,
    ((List.range n).map fun j => if P ∧ s = j then g j else 0).sum = if P ∧ s < n then g s else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_ind P s g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hP : P
    · by_cases h1 : s < n
      · simp [hP, h1, show s ≠ n by omega, show s < n + 1 by omega]
      · by_cases h2 : s = n
        · subst h2; simp [hP]
        · simp [hP, h1, h2, show ¬ s < n + 1 by omega]
    · simp [hP]

theorem getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem _

theorem adjAt {L : List WalkR} (hok : WalkOk L) {q : Nat} (h : q + 1 < rows L) :
    RAdj ((recs L).getD q default) ((recs L).getD (q + 1) default) := by
  have := (recs_adj L (len1 hok)).get q (by rw [recs_length]; exact h)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [recs_length]; omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [recs_length]; exact h)]
  exact this

/-- A non-last row is followed by the next step of its walk. -/
theorem nextSame {L : List WalkR} (hok : WalkOk L) {q : Nat} (ha : q < rows L)
    (hl : ¬ ((recs L).getD q default).2 + 1 = ((recs L).getD q default).1.steps.length) :
    q + 1 < rows L ∧ ((recs L).getD (q + 1) default).1 = ((recs L).getD q default).1 ∧
      ((recs L).getD (q + 1) default).2 = ((recs L).getD q default).2 + 1 := by
  have h1 : q + 1 < rows L := by
    apply Classical.byContradiction; intro h
    exact hl (by rw [show q = rows L - 1 by omega]; exact recs_last hok.pos (len1 hok))
  rcases adjAt hok h1 with h | h
  · exact ⟨h1, h⟩
  · exact absurd h.1 hl

/-- After a last row comes the first row of a walk. -/
theorem nextNew {L : List WalkR} (hok : WalkOk L) {q : Nat} (h1 : q + 1 < rows L)
    (hl : ((recs L).getD q default).2 + 1 = ((recs L).getD q default).1.steps.length) :
    ((recs L).getD (q + 1) default).2 = 0 := by
  have hj := (recs_mem (recs_getD_mem (show q < rows L by omega))).2
  rcases adjAt hok h1 with h | h
  · have hj' := (recs_mem (recs_getD_mem h1)).2
    rw [h.1, h.2] at hj'; omega
  · exact h.2

theorem cellSel (p : WalkGen.Rec) {j : Nat} (hj : j < 16) :
    rowCell p (WalkV3.sel j) = if ((stp p).mode = 2 ∧ ¬ p.2 + 1 = p.1.steps.length) ∧ (stp p).sym = j then 1 else 0 := by
  rw [show WalkV3.sel j = (j + 16) + 24 by simp only [WalkV3.sel]; omega]
  simp only [rowCell, if_neg (show ¬ j + 16 < 16 by omega), if_pos (show j + 16 < 32 by omega),
    Nat.add_sub_cancel, and_assoc]

theorem cellBmb (p : WalkGen.Rec) {j : Nat} (hj : j < 16) :
    rowCell p (bmb j) = if (stp p).mode = 2 then (stp p).bm / 2 ^ j % 2 else 0 := by
  rw [show bmb j = j + 24 by simp only [bmb]; omega]
  simp only [rowCell, if_pos hj]

section rows
variable {L : List WalkR} (hok : WalkOk L) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : rows L ≤ H)
  (hc : ∀ q col, q < H → col < 56 → tr.cell tt q col = Fp.ofNat (WalkGen.cell L H q col))
include hok hH hHS hc

theorem cA {q : Nat} (hq : q < H) (ha : q < rows L) {x : Nat} (hx : x < 56) :
    tr.cell tt q x = Fp.ofNat (rowCell ((recs L).getD q default) x) := by
  rw [hc q x hq hx]; simp [WalkGen.cell, ha]

theorem cP {q : Nat} (hq : q < H) (ha : ¬ q < rows L) {x : Nat} (hx : x < 56) : tr.cell tt q x = 0 := by
  rw [hc q x hq hx]; simp [WalkGen.cell, ha]; rfl

theorem bools {q : Nat} (hq : q < H) {x : Nat} (hx : x ∈ boolCols) :
    (Dsl.bool (c x)).eval tr tt q pub = 0 := by
  have hx56 : x < 56 := by
    simp only [boolCols, act, ws, we, gK, mS, mK, mB, mD, hv, bmb, WalkV3.sel, List.mem_append, List.mem_cons,
      List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩ <;> omega
  simp only [eval_bool, eval_c]
  by_cases ha : q < rows L
  · rw [cA hok hH hHS hc hq ha hx56]
    apply boolF
    have F := rowF hok (recs_getD_mem ha)
    simp only [boolCols, act, ws, we, gK, mS, mK, mB, mD, hv, bmb, WalkV3.sel, List.mem_append, List.mem_cons,
      List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    all_goals first
      | (simp only [rowCell]; omega)
      | (simp only [rowCell]; split <;> omega)
      | skip
    · simp only [rowCell]; split
      · rename_i h; exact (F.absB h).2.2.1
      · omega
    · rw [show 24 + j = j + 24 by omega]; simp only [rowCell, if_pos hj]; split <;> omega
    · rw [show 40 + j = (j + 16) + 24 by omega]; simp only [rowCell, if_neg (show ¬ j + 16 < 16 by omega),
        if_pos (show j + 16 < 32 by omega)]; split <;> omega
  · rw [cP hok hH hHS hc hq ha hx56]; grind

/-- Row-only constraints. -/
theorem rowC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ sub (c gK) (sub (c act) (c ws)),
      sub (sum (modes.map c)) (c act),
      .mul (c ws) (Dsl.not (c act)), .mul (c we) (Dsl.not (c act)),
      .mul (c ws) (c we),
      .mul (c ws) (Dsl.not (c mS)),
      .mul (c ws) (sub (c nI) (c tau)), .mul (c ws) (sub (c sym) (k SYM_START)),
      .mul (c ws) (c WalkV3.t),
      .mul .isFirst (Dsl.not (c ws)),
      .mul .isLast (.mul (c act) (Dsl.not (c we))),
      .mul (c we) (sub (c sym) (k SYM_END)),
      .mul (c mS) (sub (c nib) (c sym)),
      mul3 (c mS) (Dsl.not (c we)) (.mul (c ek) (sub (c ek) (k 1))),
      mul3 (c mS) (c we) (sub (c ek) (k EK_VAL)),
      .mul (c mK) (.mul (sub (c ek) (k EK_KEY)) (sub (c ek) (k EK_LEND))),
      .mul (c mB) (c nI),
      mul3 (c mB) (c we) (c hv) ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    have hp := recs_getD_mem ha
    obtain ⟨Fj, Fn, Fm, Fe, FS, FK, FB, FE, F0, FL, FC⟩ := rowF hok hp
    have hq0 : q = 0 → ((recs L).getD q default).2 = 0 := fun h => by
      rw [h]; exact recs_head hok.pos (len1 hok)
    have hqL : q + 1 = H → ((recs L).getD q default).2 + 1 = ((recs L).getD q default).1.steps.length :=
      fun h => by
        rw [show q = rows L - 1 by omega]; exact recs_last hok.pos (len1 hok)
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_isFirst, eval_isLast, hH,
      modes, List.map_cons, List.map_nil, eval_sum_cons, eval_sum_nil,
      act, ws, we, gK, mS, mK, mB, mD, nI, tau, sym, nib, ek, hv, WalkV3.t, cq, Nat.reduceLT, rowCell,
      natCast_eq, SYM_START, SYM_END, EK_VAL, EK_KEY, EK_LEND] <;>
    repeat' split
    all_goals first
      | omega
      | (simp only [ofNat0, ofNat1]; grind)
      | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])
  · have cq := fun (x : Nat) (hx : x < 56) => cP hok hH hHS hc hq ha hx
    have := rows_pos hok
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_isFirst, eval_isLast, hH,
      modes, List.map_cons, List.map_nil, eval_sum_cons, eval_sum_nil,
      act, ws, we, gK, mS, mK, mB, mD, nI, tau, sym, nib, ek, hv, WalkV3.t, cq, Nat.reduceLT] <;>
    repeat' split
    all_goals first
      | omega
      | grind
      | (have := rows_pos hok; omega)

theorem selC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ sub selSum (.mul (c mB) (Dsl.not (c we))),
      mul3 (c mB) (Dsl.not (c we)) (sub selIdx (c sym)), selBit ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    have hp := recs_getD_mem ha
    obtain ⟨Fj, Fn, Fm, Fe, FS, FK, FB, FE, F0, FL, FC⟩ := rowF hok hp
    generalize hpp : (recs L).getD q default = p at cq Fj Fn Fm Fe FS FK FB FE F0 FL FC
    have hsel : ∀ j, j < 16 → (c (WalkV3.sel j)).eval tr tt q pub =
        ((if ((stp p).mode = 2 ∧ ¬ p.2 + 1 = p.1.steps.length) ∧ (stp p).sym = j then 1 else 0 : Nat) : Fp) := by
      intro j hj
      rw [eval_c, cq _ (by simp only [WalkV3.sel]; omega), cellSel p hj]; rfl
    have hidx : ∀ j, j < 16 → (smul j (c (WalkV3.sel j))).eval tr tt q pub =
        ((if ((stp p).mode = 2 ∧ ¬ p.2 + 1 = p.1.steps.length) ∧ (stp p).sym = j then j else 0 : Nat) : Fp) := by
      intro j hj
      rw [eval_smul, hsel j hj, ← natCast_mul]; congr 1; split <;> simp
    have hbit : ∀ j, j < 16 → (Expr.mul (c (WalkV3.sel j)) (c (bmb j))).eval tr tt q pub =
        ((if ((stp p).mode = 2 ∧ ¬ p.2 + 1 = p.1.steps.length) ∧ (stp p).sym = j then
          (stp p).bm / 2 ^ j % 2 else 0 : Nat) : Fp) := by
      intro j hj
      rw [eval_mul, hsel j hj, eval_c, cq _ (by simp only [bmb]; omega), cellBmb p hj, ← natCast_eq,
        ← natCast_mul]
      congr 1; split
      · rename_i h; simp [h.1.1]
      · simp
    rcases he with rfl | rfl | rfl
    · simp only [selSum, eval_sub, eval_mul, eval_not, eval_c]
      rw [WalkProof.evsum 16 _ _ hsel, sum_ind _ _ (fun _ => 1) 16, cq _ (by decide), cq _ (by decide)]
      simp only [mB, we, rowCell]
      by_cases h2 : (stp p).mode = 2 <;> by_cases hl : p.2 + 1 = p.1.steps.length <;>
        simp only [h2, hl, true_and, false_and, and_false, and_true, not_true, not_false_eq_true, if_true,
          if_false, natCast_eq, ofNat0, ofNat1] <;> (try (have hs := (FB h2).2.2.2.2 hl; simp only [hs.1, hs.2, if_true])) <;>
        (try simp only [ofNat0, ofNat1]) <;> grind
    · simp only [selIdx, eval_sub, eval_mul3, eval_not, eval_c]
      rw [WalkProof.evsum 16 _ _ hidx, sum_ind _ _ (fun j => j) 16, cq _ (by decide), cq _ (by decide),
        cq _ (by decide)]
      simp only [mB, we, sym, rowCell]
      by_cases h2 : (stp p).mode = 2 <;> by_cases hl : p.2 + 1 = p.1.steps.length <;>
        simp only [h2, hl, true_and, false_and, and_false, and_true, not_true, not_false_eq_true, if_true,
          if_false, natCast_eq, ofNat0, ofNat1] <;> (try (have hs := (FB h2).2.2.2.2 hl; simp only [hs.1, hs.2, if_true])) <;>
        (try simp only [ofNat0, ofNat1]) <;> grind
    · simp only [selBit]
      rw [WalkProof.evsum 16 _ _ hbit, sum_ind _ _ (fun j => (stp p).bm / 2 ^ j % 2) 16]
      by_cases h2 : (stp p).mode = 2 <;> by_cases hl : p.2 + 1 = p.1.steps.length <;>
        simp only [h2, hl, true_and, false_and, and_false, and_true, not_true, not_false_eq_true, if_true,
          if_false, natCast_eq, ofNat0, ofNat1] <;> (try (have hs := (FB h2).2.2.2.2 hl; simp only [hs.1, hs.2, if_true])) <;>
        rfl
  · have cq := fun (x : Nat) (hx : x < 56) => cP hok hH hHS hc hq ha hx
    have hz : ∀ (f : Nat → Expr), (∀ j, j < 16 → (f j).eval tr tt q pub = ((0 : Nat) : Fp)) →
        (sum ((List.range 16).map f)).eval tr tt q pub = 0 := by
      intro f hf
      rw [WalkProof.evsum 16 f (fun _ => 0) hf, WalkProof.sum_map_zero _ _ (fun _ _ => rfl)]; rfl
    rcases he with rfl | rfl | rfl
    · simp only [selSum, eval_sub, eval_mul, eval_not, eval_c]
      rw [hz _ (fun j hj => by rw [eval_c, cq _ (by simp only [WalkV3.sel]; omega)]; rfl), cq _ (by decide)]
      grind
    · simp only [selIdx, eval_mul3, eval_c]; rw [cq _ (by decide)]; grind
    · simp only [selBit]
      exact hz _ (fun j hj => by
        rw [eval_mul, eval_c, cq _ (by simp only [WalkV3.sel]; omega)]; simp only [natCast_eq, ofNat0]; grind)

theorem invC {q : Nat} (hq : q < H) :
    (Expr.mul (c mK) (sub (.mul (sub (c sym) (c nib)) (c inv)) (k 1))).eval tr tt q pub = 0 := by
  simp only [eval_mul, eval_sub, eval_c, eval_k]
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    have hp := recs_getD_mem ha
    obtain ⟨Fj, Fn, Fm, Fe, FS, FK, FB, FE, F0, FL, FC⟩ := rowF hok hp
    rw [cq _ (by decide), cq _ (by decide), cq _ (by decide), cq _ (by decide)]
    simp only [mK, sym, nib, inv, rowCell]
    by_cases h1 : (stp ((recs L).getD q default)).mode = 1
    · simp only [h1, if_true, invOf, Fp.ofNat_toNat, ofNat1]
      have hne := fp_ne FC.2.2.1 (FC.2.2.2 _ ?_) (FK h1).2.symm
      · rw [Fp.mul_inv_cancel hne]; grind
      · exact getD_mem (by omega)
    · simp only [h1, if_false, ofNat0]; grind
  · rw [cP hok hH hHS hc hq ha (by decide : mK < 56)]; grind

theorem finC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ .mul (c we) (sub (c fk) (.add absE (c mD))), .mul (c we) (sub (c kk) (.mul (c mS) (c nN2))) ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    have hp := recs_getD_mem ha
    obtain ⟨Fj, Fn, Fm, Fe, FS, FK, FB, FE, F0, FL, FC⟩ := rowF hok hp
    by_cases hl : ((recs L).getD q default).2 + 1 = ((recs L).getD q default).1.steps.length
    · have hfk := FL hl
      rcases he with rfl | rfl <;>
      simp only [eval_mul, eval_sub, eval_add, eval_c, absE, we, fk, kk, mK, mB, mD, mS, nN2, cq, Nat.reduceLT,
        rowCell, hl, if_true, WalkR.fk, WalkR.k, hfk, FK_VAL, FK_ABS] <;>
      repeat' split
      all_goals first | omega | (simp only [ofNat0, ofNat1]; grind)
    · rcases he with rfl | rfl <;>
      simp only [eval_mul, eval_c, we, cq, Nat.reduceLT, rowCell, hl, if_false, ofNat0] <;> grind
  · have cq := fun (x : Nat) (hx : x < 56) => cP hok hH hHS hc hq ha hx
    rcases he with rfl | rfl <;>
    simp only [eval_mul, eval_c, we, cq, Nat.reduceLT] <;> grind

/-- Constraints gated by `1 − we` that read the next row. -/
theorem nextC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ mul3 (c act) (Dsl.not (c we)) (Dsl.not (n act)),
      mul3 (c act) (Dsl.not (c we)) (n ws),
      mul3 (c act) (Dsl.not (c we)) (sub (n w) (c w)),
      mul3 (c act) (Dsl.not (c we)) (sub (n tau) (c tau)),
      mul3 (c act) (Dsl.not (c we)) (sub (n WalkV3.t) (.add (c WalkV3.t) (c gK))),
      mul3 (c mS) (Dsl.not (c we)) (sub (n nN) (c nN2)),
      mul3 (c mS) (Dsl.not (c we)) (sub (n nI) (c nI2)),
      mul3 (c mS) (Dsl.not (c we)) (n mD),
      .mul (.add absE (c mD)) (.mul (Dsl.not (c we)) (Dsl.not (n mD))) ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    have hp := recs_getD_mem ha
    obtain ⟨Fj, Fn, Fm, Fe, FS, FK, FB, FE, F0, FL, FC⟩ := rowF hok hp
    by_cases hl : ((recs L).getD q default).2 + 1 = ((recs L).getD q default).1.steps.length
    · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_add, absE, act, we, mS, mK, mB, mD, cq,
        Nat.reduceLT, rowCell, hl, if_true, ofNat1] <;> grind
    · obtain ⟨h1, hw, hj⟩ := nextSame hok ha hl
      have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
      have cn := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc (q := q + 1) (by omega) h1 hx
      have ch := chainF hok hp hw hj (by omega)
      have Fm' := (rowF hok (recs_getD_mem h1)).mode
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      rotate_left 4
      all_goals
        simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, absE, hH, hnx,
          act, ws, we, w, tau, gK, mS, mK, mB, mD, nN, nI, nN2, nI2, cq, cn, Nat.reduceLT, rowCell, hl, hw, hj,
          if_false, Nat.add_one_ne_zero, ofNat0, ofNat1]
      · -- `t`
        simp only [WalkV3.t, gK, cq, cn, Nat.reduceLT, rowCell, hj, hw, Nat.add_sub_cancel, ofNat_add']
        have : ((recs L).getD q default).2 = ((recs L).getD q default).2 - 1 +
            (if ((recs L).getD q default).2 = 0 then 0 else 1) := by split <;> omega
        rw [← this]; grind
      all_goals (repeat' split) <;> first | omega | ((try simp only [ofNat0, ofNat1]) <;> grind)
  · have cq := fun (x : Nat) (hx : x < 56) => cP hok hH hHS hc hq ha hx
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_add, absE, act, mS, mK, mB, mD, cq, Nat.reduceLT] <;> grind

/-- Walk boundaries and padding. -/
theorem boundC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ mul3 (c we) (n act) (Dsl.not (n ws)), mul3 .isTransition (Dsl.not (c act)) (n act) ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  have hr := rows_pos hok
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    rcases he with rfl | rfl
    · simp only [eval_mul3, eval_c, eval_n, eval_not, hH, we, act, ws, cq, Nat.reduceLT, rowCell]
      split
      · rename_i hl
        by_cases h1 : q + 1 < rows L
        · rw [Nat.mod_eq_of_lt (show q + 1 < H by omega), cA hok hH hHS hc (by omega) h1 (by decide),
            cA hok hH hHS hc (by omega) h1 (by decide)]
          simp only [rowCell, nextNew hok h1 hl, if_true, ofNat1]; grind
        · by_cases h2 : q + 1 < H
          · rw [Nat.mod_eq_of_lt h2, cP hok hH hHS hc h2 h1 (by decide)]; grind
          · rw [show (q + 1) % H = 0 by rw [show q + 1 = H by omega]; exact Nat.mod_self H,
              cA hok hH hHS hc (by omega) hr (by decide), cA hok hH hHS hc (by omega) hr (by decide)]
            simp only [rowCell, recs_head hok.pos (len1 hok), if_true, ofNat1]; grind
      · simp only [ofNat0]; grind
    · simp only [eval_mul3, eval_c, eval_n, eval_not, act, cq, Nat.reduceLT, rowCell, ofNat1]; grind
  · rcases he with rfl | rfl
    · simp only [eval_mul3, eval_c, we, cP hok hH hHS hc hq ha (by decide : (2 : Nat) < 56)]; grind
    · simp only [eval_mul3, eval_c, eval_n, eval_not, eval_isTransition, act, hH]
      split
      · grind
      · rw [Nat.mod_eq_of_lt (show q + 1 < H by omega),
          cP hok hH hHS hc (q := q + 1) (by omega) (by omega) (by decide : (0 : Nat) < 56)]
        grind

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ WalkV3.constraints) : e.eval tr tt q pub = 0 := by
  simp only [WalkV3.constraints] at he
  rcases List.mem_append.1 he with he | he
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    exact bools hok hH hHS hc hq hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact invC hok hH hHS hc hq
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact rowC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact selC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact selC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact selC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact finC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact finC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact boundC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact boundC hok hH hHS hc hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

theorem multBits {q : Nat} (hq : q < H) {it : Interaction} (hi : it ∈ WalkV3.interactions) {b : Expr}
    (hb : b ∈ it.mult) : b.eval tr tt q pub = 0 ∨ b.eval tr tt q pub = 1 := by
  simp only [WalkV3.interactions, recv, send, List.mem_cons, List.not_mem_nil, or_false] at hi
  by_cases ha : q < rows L
  · have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
    have Fm := (rowF hok (recs_getD_mem ha)).mode
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_add, eval_c, gK, mS, mK, mB, we, cq, Nat.reduceLT, rowCell, ofNat_add'] <;>
      repeat' split
    all_goals first | (left; rfl) | (right; rfl) | omega
  · have cq := fun (x : Nat) (hx : x < 56) => cP hok hH hHS hc hq ha hx
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_add, eval_c, gK, mS, mK, mB, we, cq, Nat.reduceLT] <;> left <;> grind

end rows

end WalkLocal

open WalkLocal in
/-- **The honest `walkV3` table is locally legal.**  Hypotheses on the trace: table `t` has
`log₂` height `logOf (rows ws)` and, on every row `r < height` and column `x < WalkV3.width`,
the cell `Fp.ofNat (WalkGen.cell ws height r x)` (what `mkTab` + `Fp.ofNat` gives for
`walkRows ws`; cells outside the table are unconstrained). -/
theorem walk_render_local (ws : List WalkR) (hok : WalkOk ws) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (rows ws))
    (hcell : ∀ r x, r < tr.height t → x < WalkV3.width →
      tr.cell t r x = Fp.ofNat (WalkGen.cell ws (tr.height t) r x)) :
    TableLocal WalkV3.table tr t pub := by
  have hHS : rows ws ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) hok.cap
  · intro r hr e he
    exact constr hok rfl hHS hcell hr he
  · intro r hr it hi b hb
    exact multBits hok rfl hHS hcell hr hi hb

end ZkFormal.NearV3.Render
