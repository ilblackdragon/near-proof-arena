import ZkFormal.NearV3.Render.ValGen

/-!
# ZkFormal.NearV3.Render.ValRender — completeness of the `valV3` table

For honest records `es` (`ValOk es`, possibly empty) and any trace whose table `t` has the
cells of `ValGen.cell es` (`Render/ValGen.lean`):
* `val_render_local`: `TableLocal ValV3.table`;
* `val_render_traffic`: traffic `valTraffic es`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open ZkFormal.NearV3.ValV3 (act vf vl vid len pos b vz dup hd repE sz sumr gb gdu valConst)
open ValGen
open UniqLocal (ofNat0 ofNat1 boolF ofNat_succ)

namespace ValLocal

theorem ofNat_mod (x : Nat) : Fp.ofNat (x % ZkFormal.Algebra.P) = Fp.ofNat x :=
  Fp.ext (by rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_mod])

section rows
variable {es : List ValE} (ok : ValOk es) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : R es + 1 ≤ H)
  (hc : ∀ q col, q < H → col < 15 → tr.cell tt q col = Fp.ofNat (ValGen.cell es H q col))
include ok hH hHS hc

theorem cR {q : Nat} (hq : q < H) (ha : q < R es) {x : Nat} (hx : x < 15) (h11 : x ≠ 11) :
    tr.cell tt q x = Fp.ofNat (recCell es ((recs es).getD q default) x) := by
  rw [hc q x hq hx]; simp [ValGen.cell, ha, h11]

theorem cS {q : Nat} (hq : q < H) (ha : q = R es) {x : Nat} (hx : x < 15) (h11 : x ≠ 11) :
    tr.cell tt q x = Fp.ofNat (if x = 12 then 1 else 0) := by
  rw [hc q x hq hx]; simp [ValGen.cell, ha, h11]

theorem cP {q : Nat} (hq : q < H) (ha : R es < q) {x : Nat} (hx : x < 15) (h11 : x ≠ 11) :
    tr.cell tt q x = 0 := by
  rw [hc q x hq hx]; simp [ValGen.cell, h11, show ¬ q < R es by omega, show q ≠ R es by omega]; rfl

theorem cZ {q : Nat} (hq : q < H) : tr.cell tt q 11 = Fp.ofNat (szAt es q) := by
  rw [hc q 11 hq (by decide)]; simp [ValGen.cell]

/-- Row-only constraints. -/
theorem rowC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [act, vf, vl, vz, dup, hd, sumr, gb, gdu].map (fun x => Dsl.bool (c x)) ++
      [ sub (c gb) (.mul (c act) (Dsl.not (c vz))), sub (c gdu) (.mul (c vf) (c dup)),
        .mul (c dup) (Dsl.not (c act)), .mul (c hd) (Dsl.not (c act)),
        .mul (c vf) (Dsl.not (c act)), .mul (c vl) (Dsl.not (c act)), .mul (c act) (c sumr),
        .mul .isFirst (sub (.add (c act) (c sumr)) (k 1)), .mul .isFirst (sub (c act) (c vf)),
        .mul .isFirst (c sz),
        .mul .isLast (c act),
        .mul (c vf) (c pos),
        .mul (c vz) (Dsl.not (c vf)), .mul (c vz) (Dsl.not (c vl)), .mul (c vz) (c len), .mul (c vz) (c b),
        .mul (.mul (c vl) (Dsl.not (c vz))) (sub (.add (c pos) (k 1)) (c len)) ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  have z0 : q = 0 → szAt es q = 0 := fun h => by rw [h]; exact szAt_zero
  rcases Nat.lt_trichotomy q (R es) with ha | ha | ha
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc hq ha hx h11
    have cz := cZ ok hH hHS hc hq
    have hm := recs_mem (recs_getD_mem ha)
    have hsh := shapeAt ok hm.1
    have hq0 : q = 0 → (recs es).getD q default = (0, 0) := fun h => by rw [h]; exact recs_head ok (by omega)
    have hqL : ¬ q + 1 = H := by omega
    generalize hpp : (recs es).getD q default = p at cq hm hsh hq0
    have hb0 : (ent es p.1).vz = true → (ent es p.1).bytes.getD p.2 0 = 0 := fun h => by
      rw [(hsh.1 h).2]; simp
    have hn1 : (ent es p.1).vz = true → p.2 = 0 := fun h => by
      have := hm.2; simp only [nOf, h, if_true] at this; omega
    have hnl : (ent es p.1).vz = false → p.2 < (ent es p.1).len := fun h => by
      have := hm.2; simp only [nOf, h] at this; simpa using this
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_bool, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_isFirst, eval_isLast, hH,
      act, vf, vl, vid, len, pos, b, vz, dup, hd, sumr, gb, gdu, cq, cz, sz, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true, recCell, nOf, natCast_eq, hqL, if_false] <;>
    repeat' split
    all_goals first
      | omega
      | (simp only [ofNat0, ofNat1]; grind)
      | (rename_i h; simp only [z0 h, ofNat0]; grind)
      | (simp only [ofNat_add', ofNat0, ofNat1]; grind)
      | (simp only [ofNat_add', ofNat0, ofNat1] at *; grind)
      | grind [ofNat0, ofNat1]
      | (simp only [ofNat0, ofNat1, ← ofNat_succ]; grind)
      | (have := hsh.1; have := hn1; have := hb0; simp_all [ofNat0, ofNat1]; done)
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cS ok hH hHS hc hq ha hx h11
    have cz := cZ ok hH hHS hc hq
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_bool, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_isFirst, eval_isLast, hH,
      act, vf, vl, vid, len, pos, b, vz, dup, hd, sumr, gb, gdu, cq, cz, sz, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true, if_true, if_false, natCast_eq] <;>
    repeat' split
    all_goals first
      | omega
      | (simp only [ofNat0, ofNat1]; grind)
      | (rename_i h; simp only [z0 h, ofNat0]; grind)
      | (rename_i h; rw [z0 h]; simp only [ofNat0]; grind)
      | grind [ofNat0, ofNat1]
      | (simp only [ofNat_add', ofNat0, ofNat1] at *; grind)
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cP ok hH hHS hc hq ha hx h11
    have cz := cZ ok hH hHS hc hq
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_bool, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_isFirst, eval_isLast, hH,
      act, vf, vl, vid, len, pos, b, vz, dup, hd, sumr, gb, gdu, cq, cz, sz, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true] <;>
    repeat' split
    all_goals first | omega | grind | grind [ofNat0, ofNat1]

/-- Constraints gated by `act·(1 − vl)` (within a record). -/
theorem within {q : Nat} (hq : q < H) {E : Expr}
    (hE : E ∈ [Dsl.not (n act), n vf, sub (n pos) (.add (c pos) (k 1))] ∨ ∃ x ∈ valConst, E = sub (n x) (c x)) :
    (mul3 (c act) (Dsl.not (c vl)) E).eval tr tt q pub = 0 := by
  simp only [eval_mul3, eval_c, eval_not, act, vl]
  by_cases ha : q < R es
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc hq ha hx h11
    rw [cq 0 (by decide) (by decide), cq 2 (by decide) (by decide)]
    simp only [recCell]
    split
    · simp only [ofNat1]; grind
    · rename_i hl
      obtain ⟨h1, hw, hj⟩ := next_within ok ha hl
      have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
      have cn := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc (q := q + 1) (by omega) h1 hx h11
      suffices E.eval tr tt q pub = 0 by rw [this]; grind
      simp only [valConst, List.mem_cons, List.not_mem_nil, or_false] at hE
      rcases hE with (rfl | rfl | rfl) | ⟨x, hx, rfl⟩
      · simp only [eval_not, eval_n, hH, hnx, act, cn 0 (by decide) (by decide), recCell, ofNat1]; grind
      · simp only [eval_n, hH, hnx, vf, cn 1 (by decide) (by decide), recCell, hj, Nat.add_one_ne_zero, if_false]; rfl
      · simp only [eval_sub, eval_add, eval_n, eval_c, eval_k, hH, hnx, pos, cn 5 (by decide) (by decide),
          cq 5 (by decide) (by decide), recCell, hj, ofNat_succ, natCast_eq]; simp only [ofNat0, ofNat1]; grind
      · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [eval_sub, eval_n, eval_c, hH, hnx, vid, len, vz, dup, hd, repE, cn, cq, Nat.reduceLT, ne_eq,
          Nat.reduceEqDiff, not_false_eq_true, recCell, hw] <;> grind
  · rcases Nat.lt_or_ge (R es) q with h | h
    · rw [cP ok hH hHS hc hq h (by decide : (0 : Nat) < 15) (by decide)]; grind
    · rw [cS ok hH hHS hc hq (by omega) (by decide : (0 : Nat) < 15) (by decide)]
      simp only [show Fp.ofNat (if (0 : Nat) = 12 then 1 else 0) = 0 from rfl]; grind

/-- Record boundaries, the `SUM` row, padding and `sz`. -/
theorem nextC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ .mul (c vl) (sub (k 1) (.add (n act) (n sumr))),
      mul3 (c vl) (n act) (Dsl.not (n vf)),
      mul3 (c vl) (n act) (sub (n vid) (.add (c vid) (k 1))),
      mul3 .isTransition (c sumr) (n act), mul3 .isTransition (c sumr) (n sumr),
      mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n act),
      mul3 .isTransition (Dsl.not (.add (c act) (c sumr))) (n sumr),
      .mul .isTransition (sub (n sz) (.add (c sz) (mul3 (c act) (Dsl.not (c vz)) (Dsl.not (c dup))))) ]) :
    e.eval tr tt q pub = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  have czq := cZ ok hH hHS hc hq
  rcases Nat.lt_trichotomy q (R es) with ha | ha | ha
  · -- a record row
    have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc hq ha hx h11
    have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
    have hT : ¬ q + 1 = H := by omega
    have czn := cZ ok hH hHS hc (q := q + 1) (by omega)
    rw [szAt_succ ok, if_pos ha] at czn
    have hm := recs_mem (recs_getD_mem ha)
    -- the next row: same record, next record, or SUM
    by_cases hl : ((recs es).getD q default).2 + 1 = nOf (ent es ((recs es).getD q default).1)
    · by_cases h1 : q + 1 < R es
      · obtain ⟨hw, hj⟩ := next_after_last ok h1 hl
        have cn := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc (q := q + 1) (by omega) h1 hx h11
        have hid := ids' ok (t := ((recs es).getD q default).1) (by
          have := (recs_mem (recs_getD_mem h1)).1; rw [hw] at this; exact this)
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
          hH, hnx, hT, if_false, act, vf, vl, vid, sumr, vz, dup, sz, czq, czn, cq, cn, Nat.reduceLT, ne_eq,
          Nat.reduceEqDiff, not_false_eq_true, recCell, hl, hw, hj, if_true, hid, ofNat_mod, natCast_eq] <;>
        (try simp only [gw]) <;> (repeat' split) <;> (try simp only [ofNat0, ofNat1, ← ofNat_add']) <;>
        first | grind | (simp only [ofNat_succ]; grind)
      · have hR : q + 1 = R es := by omega
        have cn := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cS ok hH hHS hc (q := q + 1) (by omega) hR hx h11
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
          hH, hnx, hT, if_false, act, vf, vl, vid, sumr, vz, dup, sz, czq, czn, cq, cn, Nat.reduceLT, ne_eq,
          Nat.reduceEqDiff, not_false_eq_true, recCell, hl, if_true, natCast_eq] <;>
        (try simp only [gw]) <;> (repeat' split) <;> (try simp only [ofNat0, ofNat1, ← ofNat_add']) <;> grind
    · obtain ⟨h1, hw, hj⟩ := next_within ok ha hl
      have cn := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc (q := q + 1) (by omega) h1 hx h11
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
        hH, hnx, hT, if_false, act, vf, vl, vid, sumr, vz, dup, sz, czq, czn, cq, cn, Nat.reduceLT, ne_eq,
        Nat.reduceEqDiff, not_false_eq_true, recCell, hl, natCast_eq] <;>
      (try simp only [gw]) <;> (repeat' split) <;> (try simp only [ofNat0, ofNat1, ← ofNat_add']) <;> grind
  · -- the SUM row
    have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cS ok hH hHS hc hq ha hx h11
    by_cases hT : q + 1 = H
    · have hT' : (q + 1 = H) = True := eq_true hT
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
        hH, hT', if_true, vl, cq, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true, if_false, ofNat0] <;> grind
    · have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
      have cn := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cP ok hH hHS hc (q := q + 1) (by omega) (by omega) hx h11
      have czn := cZ ok hH hHS hc (q := q + 1) (by omega)
      rw [szAt_succ ok, if_neg (by omega)] at czn
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
        hH, hnx, hT, if_false, act, vl, sumr, vz, dup, sz, czq, czn, cq, cn, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, if_true, ofNat0, ofNat1, Nat.add_zero] <;> grind
  · -- padding
    have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cP ok hH hHS hc hq ha hx h11
    by_cases hT : q + 1 = H
    · have hT' : (q + 1 = H) = True := eq_true hT
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
        hH, hT', if_true, vl, cq, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true] <;> grind
    · have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
      have cn := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cP ok hH hHS hc (q := q + 1) (by omega) (by omega) hx h11
      have czn := cZ ok hH hHS hc (q := q + 1) (by omega)
      rw [szAt_succ ok, if_neg (by omega)] at czn
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_isTransition,
        hH, hnx, hT, if_false, act, vl, sumr, vz, dup, sz, czq, czn, cq, cn, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, Nat.add_zero] <;> grind

theorem vidFirst {q : Nat} (hq : q < H) : (Expr.mul .isFirst (c vid)).eval tr tt q pub = 0 := by
  simp only [eval_mul, eval_isFirst, eval_c]
  by_cases h0 : q = 0
  · subst h0
    rw [if_pos rfl]
    rcases Nat.eq_zero_or_pos (R es) with hR | hR
    · rw [cS ok hH hHS hc hq hR.symm (x := vid) (by decide) (by decide)]; simp [vid]; rfl
    · rw [cR ok hH hHS hc hq hR (x := vid) (by decide) (by decide), recs_head ok hR]
      have hne : 0 < es.length := by
        rcases Nat.eq_zero_or_pos es.length with h | h
        · simp [ValGen.R, List.length_eq_zero_iff.mp h] at hR
        · exact h
      simp only [vid, recCell, ent, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hne, Option.getD_some,
        ok.wf.first hne]
      rfl
  · rw [if_neg h0]; grind

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ ValV3.constraints) : e.eval tr tt q pub = 0 := by
  simp only [ValV3.constraints] at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · rcases List.mem_append.1 he with he | he
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
          exact rowC ok hH hHS hc hq (List.mem_append_left _ (List.mem_map_of_mem hx))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl
          · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact vidFirst ok hH hHS hc hq
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact rowC ok hH hHS hc hq (List.mem_append_right _ (by simp))
        · exact within ok hH hHS hc hq (Or.inl (by simp))
        · exact within ok hH hHS hc hq (Or.inl (by simp))
        · exact within ok hH hHS hc hq (Or.inl (by simp))
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      exact within ok hH hHS hc hq (Or.inr ⟨x, hx, rfl⟩)
  · exact nextC ok hH hHS hc hq he

theorem multBits {q : Nat} (hq : q < H) {it : Interaction} (hi : it ∈ ValV3.interactions) {bb : Expr}
    (hb : bb ∈ it.mult) : bb.eval tr tt q pub = 0 ∨ bb.eval tr tt q pub = 1 := by
  simp only [ValV3.interactions, recv, send, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases Nat.lt_trichotomy q (R es) with ha | ha | ha
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc hq ha hx h11
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_c, gb, vf, gdu, hd, dup, sumr, cq, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        recCell] <;> (repeat' split) <;> first | exact Or.inl rfl | exact Or.inr rfl
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cS ok hH hHS hc hq ha hx h11
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_c, gb, vf, gdu, hd, dup, sumr, cq, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        if_true, if_false] <;> first | exact Or.inl rfl | exact Or.inr rfl
  · have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cP ok hH hHS hc hq ha hx h11
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_c, gb, vf, gdu, hd, dup, sumr, cq, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true] <;> simp

end rows

end ValLocal

open ValLocal in
/-- Honest values and their SUM row at any sufficient padded height. -/
theorem val_render_local_at (es : List ValE) (hok : ValOk es) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (cap : Nat) (hlog : 1 ≤ tr.log t ∧ tr.log t ≤ cap)
    (hHS : ValGen.R es + 1 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < ValV3.width →
      tr.cell t r x = Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    TableLocal { ValV3.table with maxLog := cap } tr t pub := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hlog.1
  · exact hlog.2
  · intro r hr e he
    exact constr hok rfl hHS hcell hr he
  · intro r hr it hi bb hb
    exact multBits hok rfl hHS hcell hr hi hb

open ValLocal in
/-- **The honest `valV3` table is locally legal.**  Hypotheses on the trace: `log₂` height
`logOf (R + 1)` (`R = Σ` record rows, plus the `SUM` row) and cells
`Fp.ofNat (ValGen.cell es height r x)` on rows `r < height`, columns `x < ValV3.width`. -/
theorem val_render_local (es : List ValE) (hok : ValOk es) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (ValGen.R es + 1))
    (hcell : ∀ r x, r < tr.height t → x < ValV3.width →
      tr.cell t r x = Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    TableLocal ValV3.table tr t pub := by
  apply val_render_local_at es hok tr t pub ValV3.maxLog
  · rw [hlog]; exact ⟨one_le_logOf _, logOf_le (by decide) hok.wf.rows⟩
  · simp only [Trace.height, hlog]; exact le_pow_logOf _
  · exact hcell

namespace ValTraffic
open ValLocal

/-- Messages of record row `p` of `e` (as naturals), in the order of `ValProof.rowT`. -/
def recMsgs (e : ValE) (p b' : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  (if b' = B_BYTES ∧ sd = true ∧ e.vz = false then [[eidV e, p, e.bytes.getD p 0]] else []) ++
  (if b' = B_VBYTES ∧ sd = false ∧ e.vz = false then [[e.vid, p, e.bytes.getD p 0]] else []) ++
  (if b' = B_VPARENT ∧ sd = false ∧ p = 0 then [[e.vid, e.len]] else []) ++
  (if b' = B_DUP ∧ sd = false ∧ (p = 0 ∧ e.dup = true) then [[eidV e, e.repE]] else []) ++
  (if b' = B_ENT ∧ sd = true ∧ e.hd = true then [[eidV e, e.len, p, e.bytes.getD p 0]] else []) ++
  (if b' = B_ENT ∧ sd = false ∧ e.dup = true then [[e.repE, e.len, p, e.bytes.getD p 0]] else [])

theorem flat_if {β : Type} (n : Nat) (c : Prop) [Decidable c] (f : Nat → β) :
    (List.range n).flatMap (fun p => if c then [f p] else []) = if c then (List.range n).map f else [] := by
  by_cases h : c <;> simp [h, ← List.map_eq_flatMap]

theorem flat_zero {β : Type} (n : Nat) (hn : 1 ≤ n) (c : Prop) [Decidable c] (m : β) :
    (List.range n).flatMap (fun p => if p = 0 ∧ c then [m] else []) = if c then [m] else [] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    flatMap_nil' (fun j _ => by simp)]
  by_cases h : c <;> simp [h]

/-- The messages of one record's rows. -/
theorem rec_msgs (e : ValE) (hsh : (e.vz = true → e.len = 0 ∧ e.bytes = []) ∧
      (e.vz = false → e.bytes.length = e.len ∧ 0 < e.len)) (b' : Nat) (hb : b' ≠ B_SIZE) (sd : Bool) :
    (List.range (nOf e)).flatMap (fun p => recMsgs e p b' sd) =
      if sd then valSends [e] b' else valRecvs [e] b' := by
  have hn : 1 ≤ nOf e := by
    simp only [nOf]; split
    · omega
    · rename_i h; exact (hsh.2 (by simpa using h)).2
  by_cases h0 : b' = B_BYTES
  · subst h0; cases sd
    · simp [recMsgs, valRecvs, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT]
    · simp only [recMsgs, valSends, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT, true_and, Nat.reduceEqDiff,
        false_and, if_false, List.append_nil, if_true, List.flatMap_cons, List.flatMap_nil, flat_if]
      cases hv : e.vz
      · simp [nOf, hv, emitAt, (hsh.2 hv).1]
      · simp [nOf, hv]
  by_cases h1 : b' = B_VBYTES
  · subst h1; cases sd
    · simp only [recMsgs, valRecvs, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT, true_and, Nat.reduceEqDiff,
        false_and, if_false, List.append_nil, List.nil_append, if_true, List.flatMap_cons, List.flatMap_nil,
        flat_if, Bool.false_eq_true]
      cases hv : e.vz
      · simp [nOf, hv, (hsh.2 hv).1]
      · simp [nOf, hv]
    · simp [recMsgs, valSends, B_BYTES, B_VBYTES, B_ENT, B_SIZE]
  by_cases h2 : b' = B_VPARENT
  · subst h2; cases sd
    · simp only [recMsgs, valRecvs, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT, true_and, Nat.reduceEqDiff,
        false_and, if_false, List.append_nil, List.nil_append, if_true, Bool.false_eq_true]
      rw [show (fun p => if p = 0 then [[e.vid, e.len]] else []) =
        (fun p => if p = 0 ∧ True then [[e.vid, e.len]] else []) by simp, flat_zero _ hn]
      simp
    · simp [recMsgs, valSends, B_BYTES, B_VBYTES, B_VPARENT, B_ENT, B_SIZE]
  by_cases h3 : b' = B_DUP
  · subst h3; cases sd
    · simp only [recMsgs, valRecvs, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT, true_and, Nat.reduceEqDiff,
        false_and, if_false, List.append_nil, List.nil_append, if_true, Bool.false_eq_true]
      rw [flat_zero _ hn]; simp
    · simp [recMsgs, valSends, B_BYTES, B_DUP, B_ENT, B_SIZE]
  by_cases h4 : b' = B_ENT
  · subst h4; cases sd
    · simp only [recMsgs, valRecvs, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT, true_and, Nat.reduceEqDiff,
        false_and, if_false, List.append_nil, List.nil_append, if_true, Bool.false_eq_true, flat_if,
        List.flatMap_cons, List.flatMap_nil]
      cases hd' : e.dup
      · simp
      · cases hv : e.vz
        · simp [nOf, hv, ValE.entRows, ← List.map_eq_flatMap]
        · simp [nOf, hv, ValE.entRows, (hsh.1 hv).1, (hsh.1 hv).2]
    · simp only [recMsgs, valSends, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT, true_and, Nat.reduceEqDiff,
        false_and, if_false, List.append_nil, List.nil_append, if_true, flat_if, List.flatMap_cons, List.flatMap_nil]
      cases hd' : e.hd
      · simp
      · cases hv : e.vz
        · simp [nOf, hv, ValE.entRows, ← List.map_eq_flatMap]
        · simp [nOf, hv, ValE.entRows, (hsh.1 hv).1, (hsh.1 hv).2]
  · cases sd
    · simp [recMsgs, valRecvs, h0, h1, h2, h3, h4]
    · simp [recMsgs, valSends, h0, h4, hb]

theorem rec_size (e : ValE) (p : Nat) (sd : Bool) : recMsgs e p B_SIZE sd = [] := by
  simp [recMsgs, B_SIZE, B_BYTES, B_VBYTES, B_VPARENT, B_DUP, B_ENT]

theorem ite_map {P Q : Prop} [Decidable P] [Decidable Q] {x : List Fp} {m : ZkFormal.Near.Msg} (h : P ↔ Q)
    (hm : Q → x = Msg.toFp m) : (if P then [x] else []) = (if Q then [m] else []).map Msg.toFp := by
  by_cases hq : Q
  · rw [if_pos (h.2 hq), if_pos hq, hm hq]; rfl
  · rw [if_neg (fun hp => hq (h.1 hp)), if_neg hq]; rfl

theorem eid_eq (x : Nat) : (K_VPRE : Fp) + 16 * Fp.ofNat x = Fp.ofNat (msgId K_VPRE x) := by
  unfold msgId; rw [natCast_eq, show (16 : Fp) = Fp.ofNat 16 from rfl, ofNat_mul', ofNat_add']

section rows
variable {es : List ValE} (ok : ValOk es) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : R es + 1 ≤ H)
  (hc : ∀ q col, q < H → col < 15 → tr.cell tt q col = Fp.ofNat (ValGen.cell es H q col))
include ok hH hHS hc

theorem rowAct {q : Nat} (hq : q < H) (ha : q < R es) (b' : Nat) (sd : Bool) :
    rowTraffic ValV3.interactions tr tt q pub b' sd =
      (recMsgs (ent es ((recs es).getD q default).1) ((recs es).getD q default).2 b' sd).map Msg.toFp := by
  have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cR ok hH hHS hc hq ha hx h11
  generalize hpp : (recs es).getD q default = p at cq
  rw [ValProof.rowT]
  simp only [recMsgs, List.map_append]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  have i01 : ∀ (P : Prop) [Decidable P], Fp.ofNat (if P then 1 else 0) = 1 ↔ P := by
    intro P _; split <;> simp_all [ofNat0, ofNat1]
  have i10 : ∀ (P : Prop) [Decidable P], Fp.ofNat (if P then 0 else 1) = 1 ↔ ¬ P := by
    intro P _; split <;> simp_all [ofNat0, ofNat1]
  have heid : ValProof.eidF tr tt q = Fp.ofNat (eidV (ent es p.1)) := by
    simp only [ValProof.eidF, vid]; rw [cq 3 (by decide) (by decide)]; simp only [recCell]; exact eid_eq _
  have hs0 : tr.cell tt q sumr = 0 := by simp only [sumr]; rw [cq 12 (by decide) (by decide)]; rfl
  simp only [hs0, fp_zero_ne_one, and_false, if_false, List.append_nil]
  refine ap (ap (ap (ap (ap ?_ ?_) ?_) ?_) ?_) ?_
  · apply ite_map
    · simp only [gb, vf, gdu, hd, dup]; rw [cq 13 (by decide) (by decide)]; simp only [recCell, i10]; simp
    · intro _; simp only [heid, cq, pos, b, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true, recCell,
        Msg.toFp, List.map_cons, List.map_nil]
  · apply ite_map
    · simp only [gb, vf, gdu, hd, dup]; rw [cq 13 (by decide) (by decide)]; simp only [recCell, i10]; simp
    · intro _; simp only [cq, vid, pos, b, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true, recCell,
        Msg.toFp, List.map_cons, List.map_nil]
  · apply ite_map
    · simp only [gb, vf, gdu, hd, dup]; rw [cq 1 (by decide) (by decide)]; simp only [recCell, i01]
    · intro _; simp only [cq, vid, len, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true, recCell,
        Msg.toFp, List.map_cons, List.map_nil]
  · apply ite_map
    · simp only [gb, vf, gdu, hd, dup]; rw [cq 14 (by decide) (by decide)]; simp only [recCell, i01]
    · intro _; simp only [heid, cq, repE, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true, recCell,
        Msg.toFp, List.map_cons, List.map_nil]
  · apply ite_map
    · simp only [gb, vf, gdu, hd, dup]; rw [cq 9 (by decide) (by decide)]; simp only [recCell, i01]
    · intro _; simp only [heid, cq, len, pos, b, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        recCell, Msg.toFp, List.map_cons, List.map_nil]
  · apply ite_map
    · simp only [gb, vf, gdu, hd, dup]; rw [cq 8 (by decide) (by decide)]; simp only [recCell, i01]
    · intro _; simp only [cq, repE, len, pos, b, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        recCell, Msg.toFp, List.map_cons, List.map_nil]

theorem rowSum {q : Nat} (hq : q < H) (ha : q = R es) (b' : Nat) (sd : Bool) :
    rowTraffic ValV3.interactions tr tt q pub b' sd =
      (if b' = B_SIZE ∧ sd = true then [[1, ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum]] else
        []).map Msg.toFp := by
  have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cS ok hH hHS hc hq ha hx h11
  rw [ValProof.rowT]
  simp only [cq, gb, vf, gdu, hd, dup, sumr, sz, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true, if_false,
    if_true, ofNat0, ofNat1, fp_zero_ne_one, and_false, List.nil_append, and_true]
  rw [cZ ok hH hHS hc hq, ha, szAt_R ok]
  split <;> simp [Msg.toFp] <;> rfl

theorem rowPad {q : Nat} (hq : q < H) (ha : R es < q) (b' : Nat) (sd : Bool) :
    rowTraffic ValV3.interactions tr tt q pub b' sd = [] := by
  have cq := fun (x : Nat) (hx : x < 15) (h11 : x ≠ 11) => cP ok hH hHS hc hq ha hx h11
  rw [ValProof.rowT]
  simp [cq, gb, vf, gdu, hd, dup, sumr]

end rows

end ValTraffic

open ValTraffic ValLocal in
/-- **The honest `valV3` table has the traffic of `es`.**  Same hypotheses as `val_render_local`. -/
theorem val_render_traffic_at (es : List ValE) (hok : ValOk es) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hle : ValGen.R es + 1 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < ValV3.width →
      tr.cell t r x = Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    TableTraffic ValV3.interactions tr t pub (valTraffic es) := by
  -- record rows
  have hrec : ∀ b' sd, (List.range (ValGen.R es)).flatMap
      (fun r => rowTraffic ValV3.interactions tr t r pub b' sd) =
      ((List.range es.length).flatMap fun t' =>
        (List.range (nOf (ent es t'))).flatMap fun p => recMsgs (ent es t') p b' sd).map Msg.toFp := by
    intro b' sd
    rw [ZkFormal.Near.Render.flatMap_congr' (g := fun q =>
      (recMsgs (ent es ((recs es).getD q default).1) ((recs es).getD q default).2 b' sd).map Msg.toFp)
      (fun q hq => rowAct hok rfl hle hcell (by have := List.mem_range.1 hq; omega) (List.mem_range.1 hq) b' sd),
      ← recs_length, ← flatMap_getD default (recs es) (fun p => (recMsgs (ent es p.1) p.2 b' sd).map Msg.toFp),
      List.map_flatMap, recs, List.flatMap_assoc]
    simp only [List.flatMap_map, List.map_flatMap]
  have hall : ∀ sd b', (List.range (tr.height t)).flatMap
      (fun r => rowTraffic ValV3.interactions tr t r pub b' sd) =
      (if sd then valSends es b' else valRecvs es b').map Msg.toFp := by
    intro sd b'
    rw [range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact rowPad hok rfl hle hcell (by have := List.mem_range.1 hq'; omega) (by omega) b' sd),
      List.append_nil, List.range_succ, List.flatMap_append, hrec, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, rowSum hok rfl hle hcell (by omega) rfl b' sd]
    by_cases hb : b' = B_SIZE
    · subst hb
      rw [flatMap_nil' (fun t' _ => flatMap_nil' (fun p _ => rec_size _ _ _))]
      cases sd <;> simp [valSends, valRecvs, B_SIZE, B_BYTES, B_ENT, B_VBYTES, B_VPARENT, B_DUP]
    · rw [ZkFormal.Near.Render.flatMap_congr' (g := fun t' => if sd then valSends [ent es t'] b' else
          valRecvs [ent es t'] b') (fun t' ht' =>
        rec_msgs _ (shapeAt hok (List.mem_range.1 ht')) b' hb sd)]
      rw [show (fun t' => if sd then valSends [ent es t'] b' else valRecvs [ent es t'] b') =
        fun t' => (fun e => if sd then valSends [e] b' else valRecvs [e] b') (es.getD t' default) from rfl,
        ← flatMap_getD default es (fun e => if sd then valSends [e] b' else valRecvs [e] b')]
      cases sd
      · simp only [Bool.false_eq_true, ↓reduceIte, ← valRecvs_flat]; simp [hb]
      · simp only [↓reduceIte, ← valSends_flat es b' hb]; simp [hb]
  apply traffic_of
  · intro b'; rw [hall true b']; exact List.Perm.refl _
  · intro b'; rw [hall false b']; exact List.Perm.refl _

open ValTraffic ValLocal in
/-- **The honest `valV3` table has the traffic of `es`.**  Same hypotheses as `val_render_local`. -/
theorem val_render_traffic (es : List ValE) (hok : ValOk es) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (ValGen.R es + 1))
    (hcell : ∀ r x, r < tr.height t → x < ValV3.width →
      tr.cell t r x = Fp.ofNat (ValGen.cell es (tr.height t) r x)) :
    TableTraffic ValV3.interactions tr t pub (valTraffic es) := by
  apply val_render_traffic_at es hok tr t pub
  · simp only [Trace.height, hlog]; exact le_pow_logOf _
  · exact hcell

end ZkFormal.NearV3.Render
