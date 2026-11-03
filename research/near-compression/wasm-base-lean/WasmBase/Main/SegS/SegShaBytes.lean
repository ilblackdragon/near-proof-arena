import WasmBase.Main.SegShaBytes
import WasmBase.Main.SegS.SegSha
/-!
# WasmBase.Main.SegS.SegShaBytes — `SegShaBytes`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegShaBytes.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

theorem le_of_sendsOkBS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) {b t : Nat}
    (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t] (hok : SendsOkB b ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters) (hb : i.bus = b) (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  have hc := List.all_eq_true.mp hok i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  rcases hc with (hc | hc) | hc
  · exact absurd hb hc
  · rw [hs] at hc; exact absurd hc (by decide)
  · rcases bitS_soundS H ht hr _ hc with h | h <;> rw [h] <;> decide

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- **The BYTE send bound of `wasmBaseSegAir`.** -/
theorem seg_hsend_byteS :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busByte → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have : SegT t := ⟨by omega⟩
    have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqXS H ht (chipT t) hT hr
    rw [hT] at hi
    obtain ⟨h1, h13⟩ := hc
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact add_counts_of hcon i hi
    · exact bit_counts_of hcon i hi
    · exact mul_counts_of hcon i hi
    · exact shift_counts_of hcon i hi
    · exact cmp_counts_of hcon i hi
    · exact const_counts_of hcon i hi
    · exact stack_counts_of hcon i hi
    · exact ctrl_counts_of hcon i hi
    · exact local_counts_of hcon i hi
    · exact div_counts_of hcon i hi
    · exact load_counts_of hcon i hi
    · exact store_counts_of hcon i hi
    · exact call_counts_of hcon i hi
  by_cases h14 : t = 14
  · subst h14
    have hcon : ∀ e ∈ Ret.table.constraints, e.eval (Local.natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0 :=
      table_constr_eqXS H ht RetT.table (seg_t14' nloc ngl) hr
    rw [seg_t14'] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ret_counts_of hcon i hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; exact absurd hb (by decide)
  by_cases h19 : t = 19
  · subst h19
    rw [seg_t19] at hi
    have hc := List.all_eq_true.mp memb_byte_shape i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    rcases hc with (((hc | hc) | hc) | hc) | hc
    · exact absurd hb hc
    · rw [hs] at hc; exact absurd hc (by decide)
    · rw [hc]; exact (memb_kD_leS H hr).1
    · rw [hc]; exact (memb_kD_leS H hr).2
    · have hT := seg_t19 nloc ngl
      rcases bitS_soundS H ht hr i.count (by rw [hT]; exact hc) with h | h <;> rw [h] <;> decide
  · by_cases h20 : t = 20
    · subst h20; exact absurd hb (seg_t20_noBus nloc ngl (by decide) hi)
    have : SegT t := ⟨h20⟩
    exact le_of_sendsOkBS H ht (seg_sendsOkB nloc ngl t ht (by omega) h19) hr hi hb hs

theorem byte_bitsXS {r : Nat} (hr : r < tr.height 16) : ∀ i, i < 16 → rowNat tr 16 r i ≤ 1 := by
  intro i hi
  have hc := table_constrXS H (show 16 < (wasmBaseSegAir nloc ngl).tables.length by simp [seg_air_len]) hr
  rw [seg_t16] at hc
  have := hc (Chips.bool (v i)) (by
    simp only [Byte.table, Byte.constraints, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨i, hi, rfl⟩)
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at this
  rcases bool_nat (rowNat_lt _ _ _ _) this with h | h <;> omega

end

end SegSha

end WasmBase
