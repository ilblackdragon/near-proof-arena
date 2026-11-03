import WasmBase.Main.SegMemb
import WasmBase.Main.SegS.SegRows
/-!
# WasmBase.Main.SegS.SegMemb — `SegMemb`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegMemb.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- `p8` is a bit on a MEMB row. -/
theorem memb_p_bitS {r : Nat} (hr : r < tr.height 19) {i : Nat} (hi : i < 9) :
    bc tr r (1 + i) = 0 ∨ bc tr r (1 + i) = 1 := by
  have h := H.constr 19 (by simp [seg_air_len]) r hr (Chips.bool (Memb.p i))
    (by
      rw [seg_t19]
      show _ ∈ Memb.constraints
      unfold Memb.constraints
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ ?_))))))))
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simp only [Chips.bool, Memb.p, Memb.c, mb_ix_p i hi, Expr.eval_mul', Expr.eval_sub', v, Expr.eval_col,
    Expr.eval_ofNat', Trace.row] at h
  exact bool_cases (by simpa [cast_one] using h)

end

/-- An R16 query with count 1 on a segment trace is `< 2^16`, given the R16 send bound `hsend`. -/
theorem seg_r16_ltS {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) {r : Nat} (hr : r < tr.height t)
    {e c : Expr} (hi : r16 e c ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have hocc := occ_of_inter ht hr hi hc
  obtain ⟨x, hx, hxl⟩ := lookup_r16GXS H hsend (regG_r16_recvXS H (regAt_seg nloc ngl)) hocc rfl rfl rfl
  simp only [r16, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

theorem memb_CS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r < tr.height 19) : ∀ e ∈ Memb.constraints, e.eval (tr.row pub 19 r) = 0 := by
  intro e he
  exact H.constr 19 (by simp [seg_air_len]) r hr e (by rw [seg_t19]; exact he)

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- **A MEMB row as naturals**: `act` and the nine position flags are bits, and they sum to `act`. -/
theorem memb_rowS {r : Nat} (hr : r < tr.height 19) :
    mbN tr r 0 ≤ 1 ∧ (∀ i, i < 9 → mbN tr r (1 + i) ≤ 1) ∧
      mbN tr r 1 + mbN tr r 2 + mbN tr r 3 + mbN tr r 4 + mbN tr r 5 + mbN tr r 6 + mbN tr r 7 +
        mbN tr r 8 + mbN tr r 9 = mbN tr r 0 := by
  have C := memb_CS H hr
  have ha := C (Chips.bool (Memb.c "act")) (by simp [Memb.constraints])
  rw [Chips.bool, Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.1, Expr.eval_ofNat'] at ha
  have ba := bool_nat (rowNat_lt tr 19 r 0) ha
  have bp : ∀ i, i < 9 → mbN tr r (1 + i) ≤ 1 := by
    intro i hi
    rcases memb_p_bitS H hr hi with h | h
    · have := natEq (R := 0) (show ((mbN tr r (1 + i) : Nat) : F) = ((0 : Nat) : F) by rw [← cell_cast]; exact h)
        (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
      omega
    · have := natEq (R := 1) (show ((mbN tr r (1 + i) : Nat) : F) = ((1 : Nat) : F) by rw [← cell_cast]; exact h)
        (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
      omega
  have ha1 : mbN tr r 0 ≤ 1 := by rcases ba with h | h <;> (show rowNat tr 19 r 0 ≤ 1; omega)
  refine ⟨ha1, bp, ?_⟩
  have hs := C (sumE ((List.range 9).map Memb.p) - Memb.c "act") (by simp [Memb.constraints])
  have e9 : sumE ((List.range 9).map Memb.p) =
      0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 + Memb.p 7 + Memb.p 8 := rfl
  rw [e9] at hs
  simp only [Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
    memb_p_eval tr pub r (show 0 < 9 by decide), memb_p_eval tr pub r (show 1 < 9 by decide),
    memb_p_eval tr pub r (show 2 < 9 by decide), memb_p_eval tr pub r (show 3 < 9 by decide),
    memb_p_eval tr pub r (show 4 < 9 by decide), memb_p_eval tr pub r (show 5 < 9 by decide),
    memb_p_eval tr pub r (show 6 < 9 by decide), memb_p_eval tr pub r (show 7 < 9 by decide),
    memb_p_eval tr pub r (show 8 < 9 by decide)] at hs
  have b1 : mbN tr r 1 ≤ 1 := bp 0 (by decide)
  have b2 : mbN tr r 2 ≤ 1 := bp 1 (by decide)
  have b3 : mbN tr r 3 ≤ 1 := bp 2 (by decide)
  have b4 : mbN tr r 4 ≤ 1 := bp 3 (by decide)
  have b5 : mbN tr r 5 ≤ 1 := bp 4 (by decide)
  have b6 : mbN tr r 6 ≤ 1 := bp 5 (by decide)
  have b7 : mbN tr r 7 ≤ 1 := bp 6 (by decide)
  have b8 : mbN tr r 8 ≤ 1 := bp 7 (by decide)
  have b9 : mbN tr r 9 ≤ 1 := bp 8 (by decide)
  simp only [mbN] at b1 b2 b3 b4 b5 b6 b7 b8 b9 ha1 ⊢
  have hP := P_val
  refine natEq ?_ (by omega) (rowNat_lt _ _ _ _)
  simp only [Lean.Grind.Semiring.natCast_add]
  grind

end

end WasmBase
