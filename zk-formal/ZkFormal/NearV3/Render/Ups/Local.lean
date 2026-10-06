import ZkFormal.NearV3.Render.Ups.Traffic

/-!
# ZkFormal.NearV3.Render.Ups.Local — `TableLocal` of the honest `upsV3` table from its constraints

`ups_render_local_of`: if every constraint of `upsV3` vanishes on every row of the honest table
(`GroupOk insts H UpsV3.constraints`, with the generator's integer cells), then the table is
locally legal: the height is within `maxLog = 22` (`R + 1 ≤ 2^22`, a field of the honest input),
and every interaction gate is a bit — derived from the constraints themselves through the
view's row facts (`UpsRows.rowBool`, `UpsRows.kinds`, the drain flag `mD`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.NearV3.UpsRows
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < ZkFormal.Algebra.P) (hD : ∀ x, D x < ZkFormal.Algebra.P)
include ok hC

theorem bit01 {x : Nat} (hx : x ∈ rowBools) : uev C D (c x) = 0 ∨ uev C D (c x) = 1 := by
  rcases rowBool ok hC hx with h | h
  · left; show Fp.ofNat (C x) = 0; rw [h]; rfl
  · right; show Fp.ofNat (C x) = 1; rw [h]; rfl

/-- `mS + mK ≤ 1`: the modes are bits and so is the drain flag `wk − mS − mK − mB`. -/
theorem modes01 : C mS + C mK ≤ 1 := by
  have b := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bS := b (x := mS) (by simp [rowBools])
  have bK := b (x := mK) (by simp [rowBools])
  have bB := b (x := mB) (by simp [rowBools])
  have bW := b (x := wk) (by simp [rowBools])
  have h := fact ok (e := Dsl.bool mDE) (by unfold UpsV3.constraints cBool; simp)
  simp only [uev, Expr.evalWith, uEnv, Dsl.bool, Dsl.sub, Dsl.k, Dsl.c, mDE, if_false,
    Bool.false_eq_true] at h
  rcases bS with hS | hS <;> rcases bK with hK | hK <;> rcases bB with hB | hB <;> rcases bW with hW | hW <;>
    rw [hS, hK, hB, hW] at h <;> first | omega | exact absurd h (by decide)

end

/-- Every interaction gate of `upsV3` is a bit on a row satisfying the constraints. -/
theorem gates01 {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < ZkFormal.Algebra.P) (hD : ∀ x, D x < ZkFormal.Algebra.P) :
    ∀ i ∈ UpsV3.interactions, ∀ g ∈ i.mult, uev C D g = 0 ∨ uev C D g = 1 := by
  intro i hi g hg
  simp only [UpsV3.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
  have K := kinds ok hC hD
  obtain ⟨hact, hsum, -⟩ := K
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_singleton] at hg <;> subst hg
  all_goals first
    | exact bit01 ok hC (by simp [rowBools])
    | skip
  · -- vb + qb
    have : C vb + C qb ≤ 1 := by
      have := rowBool ok hC (x := wk) (by simp [rowBools]); omega
    show Fp.ofNat (C vb) + Fp.ofNat (C qb) = 0 ∨ Fp.ofNat (C vb) + Fp.ofNat (C qb) = 1
    rcases (show (C vb = 0 ∧ C qb = 0) ∨ (C vb = 1 ∧ C qb = 0) ∨ (C vb = 0 ∧ C qb = 1) by
      have := rowBool ok hC (x := vb) (by simp [rowBools])
      have := rowBool ok hC (x := qb) (by simp [rowBools]); omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rw [a, b] <;> decide
  all_goals
    have hm := modes01 ok hC
    show Fp.ofNat (C mS) + Fp.ofNat (C mK) = 0 ∨ Fp.ofNat (C mS) + Fp.ofNat (C mK) = 1
    rcases (show (C mS = 0 ∧ C mK = 0) ∨ (C mS = 1 ∧ C mK = 0) ∨ (C mS = 0 ∧ C mK = 1) by
      have := rowBool ok hC (x := mS) (by simp [rowBools])
      have := rowBool ok hC (x := mK) (by simp [rowBools]); omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rw [a, b] <;> decide

end UpsGen

open UpsGen in
/-- **The honest `upsV3` table is locally legal once its constraints vanish.**  Hypotheses on the
trace: `log₂` height `logOf (R + 1)` with `R + 1 ≤ 2^22`, cells `UpsGen.cell insts` (their images
in `Fp`) below the width; and `GroupOk` of all constraints (proved group by group). -/
theorem ups_render_local_of (insts : List UpsInst) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hcap : R insts + 1 ≤ 2 ^ 22)
    (hlog : tr.log t = logOf (R insts + 1))
    (hcell : ∀ r x, r < tr.height t → x < 187 → tr.cell t r x = ((cell insts r x : Int) : Fp))
    (hG : GroupOk insts (tr.height t) UpsV3.constraints) :
    TableLocal UpsV3.table tr t pub := by
  have hcon := constr_of (pub := pub) hcell hG
  refine ⟨by rw [hlog]; exact one_le_logOf _, by rw [hlog]; exact logOf_le (by decide) hcap, hcon, ?_⟩
  intro r hr i hi g hg
  have ok : URowOk (rowC tr t r) (rowC tr t ((r + 1) % tr.height t)) := by
    intro e he hp
    rw [← eval_pure tr t r pub e hp]
    exact hcon r hr e he
  have hp : g.pure = true := by
    have h := List.all_eq_true.1 interactions_pure i hi
    simp only [Bool.and_eq_true] at h
    have h1 := h.1
    unfold pureGate at h1
    split at h1
    · rename_i g' hgm
      rw [hgm] at hg; simp only [List.mem_singleton] at hg; subst hg; exact h1
    · exact absurd h1 (by simp)
  rw [eval_pure tr t r pub g hp]
  exact gates01 ok (fun x => rowC_lt tr t r x) (fun x => rowC_lt tr t _ x) i hi g hg

end ZkFormal.NearV3.Render
