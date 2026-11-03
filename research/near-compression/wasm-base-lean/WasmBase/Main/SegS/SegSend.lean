import WasmBase.Main.SegSend
import WasmBase.Main.SegS.SegMemb
/-!
# WasmBase.Main.SegS.SegSend — `SegSend`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegSend.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **Soundness of `BitS`** on row `r` of table `t` of a satisfied trace. -/
theorem bitS_soundS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) {t : Nat}
    (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t] {r : Nat} (hr : r < tr.height t) :
    ∀ e, BitS (bcOf ((wasmBaseSegAir nloc ngl).tables[t]'ht)) (beOf ((wasmBaseSegAir nloc ngl).tables[t]'ht)) e = true →
      e.eval (tr.row pub t r) = 0 ∨ e.eval (tr.row pub t r) = 1 := by
  have hpos : 0 < tr.height t := by omega
  have rowbit : ∀ r', r' < tr.height t → ∀ i ∈ bcOf ((wasmBaseSegAir nloc ngl).tables[t]'ht), tr.cell t r' i = 0 ∨ tr.cell t r' i = 1 := by
    intro r' hr' i hi
    have h := H.constr t ht r' hr' _ (bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', cast_one,
      Trace.row] at h
    exact bit01 h
  have expbit : ∀ a ∈ beOf ((wasmBaseSegAir nloc ngl).tables[t]'ht), a.eval (tr.row pub t r) = 0 ∨ a.eval (tr.row pub t r) = 1 := by
    intro a ha
    have h := H.constr t ht r hr _ (beOf_mem ha)
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cast_one] at h
    exact bit01 h
  intro e
  induction e with
  | mul a b iha ihb =>
    intro h
    simp only [BitS, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hb⟩
    · exact expbit _ (any_mem h)
    · simp only [Expr.eval]
      rcases iha ha with h1 | h1 <;> rcases ihb hb with h2 | h2 <;> rw [h1, h2] <;> grind
  | sub a b iha ihb =>
    intro h
    simp only [BitS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨rfl, hb⟩
    · exact expbit _ (any_mem h)
    · simp only [Expr.eval, cast_one]
      rcases ihb hb with h2 | h2 <;> rw [h2] <;> grind
  | first => intro _; simp only [Expr.eval]; split <;> simp
  | last => intro _; simp only [Expr.eval]; split <;> simp
  | trans => intro _; simp only [Expr.eval]; split <;> simp
  | c n =>
    intro h
    simp only [BitS, decide_eq_true_eq] at h
    simp only [Expr.eval]
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · left; rfl
    · right; rfl
  | col i =>
    intro h
    simp only [BitS, Bool.or_eq_true] at h
    rcases h with h | h
    · simpa [Expr.eval, Trace.row] using rowbit r hr i (any_mem h)
    · exact expbit _ (any_mem h)
  | nxt i =>
    intro h
    simp only [BitS] at h
    simpa [Expr.eval, Trace.row] using rowbit _ (Nat.mod_lt _ hpos) i (any_mem h)
  | pub i => intro h; exact expbit _ (any_mem h)
  | add a b _ _ => intro h; exact expbit _ (any_mem h)

theorem r16_le_of_sendsOkS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) {t : Nat}
    (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t] (hok : R16SendsOk ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters) (hb : i.bus = busR16) (hs : i.send = true) :
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

/-- `kD ≤ 1` and `kD·(1 − ro) ≤ 1` on a MEMB row (the one-hot `memb_rowS`). -/
theorem memb_kD_leS {r : Nat} (hr : r < tr.height 19) :
    (Memb.kD.eval (tr.row pub 19 r)).toNat ≤ 1 ∧
      ((Memb.kD * (1 - Memb.c "ro")).eval (tr.row pub 19 r)).toNat ≤ 1 := by
  obtain ⟨ha, bp, hs⟩ := memb_rowS H hr
  have hP := P_val
  have e8 : Memb.kD = 0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 +
      Memb.p 7 := rfl
  have hk : Memb.kD.eval (tr.row pub 19 r) =
      ((mbN tr r 1 + mbN tr r 2 + mbN tr r 3 + mbN tr r 4 + mbN tr r 5 + mbN tr r 6 + mbN tr r 7 +
        mbN tr r 8 : Nat) : F) := by
    rw [e8]
    simp only [Expr.eval_add', Expr.eval_ofNat', memb_p_eval tr pub r (show 0 < 9 by decide),
      memb_p_eval tr pub r (show 1 < 9 by decide), memb_p_eval tr pub r (show 2 < 9 by decide),
      memb_p_eval tr pub r (show 3 < 9 by decide), memb_p_eval tr pub r (show 4 < 9 by decide),
      memb_p_eval tr pub r (show 5 < 9 by decide), memb_p_eval tr pub r (show 6 < 9 by decide),
      memb_p_eval tr pub r (show 7 < 9 by decide), Lean.Grind.Semiring.natCast_add]
    grind
  have hsum : mbN tr r 1 + mbN tr r 2 + mbN tr r 3 + mbN tr r 4 + mbN tr r 5 + mbN tr r 6 + mbN tr r 7 +
      mbN tr r 8 ≤ 1 := by omega
  have hro : mbN tr r 11 ≤ 1 := by
    have h := memb_CS H hr (Chips.bool (Memb.c "ro")) (by simp [Memb.constraints])
    rw [Chips.bool, Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.2.2, Expr.eval_ofNat'] at h
    rcases bool_nat (rowNat_lt tr 19 r 11) h with h | h <;> (show rowNat tr 19 r 11 ≤ 1; omega)
  refine ⟨?_, ?_⟩
  · rw [hk, Fp.toNat_cast_of_lt (by omega)]; exact hsum
  · rw [Expr.eval_mul', hk, Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.2.2]
    rw [show ((1 : Nat) : F) = 1 from rfl, one_sub_bit hro, ← Lean.Grind.Semiring.natCast_mul,
      Fp.toNat_cast_of_lt (by
      have : (1 - mbN tr r 11) ≤ 1 := by omega
      have := Nat.mul_le_mul hsum this; omega)]
    have : (1 - mbN tr r 11) ≤ 1 := by omega
    have := Nat.mul_le_mul hsum this; omega

/-- **The R16 send bound of `wasmBaseSegAir`.** -/
theorem seg_hsend_r16S :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 := by
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
    have hc := List.all_eq_true.mp memb_r16_shape i hi
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
    exact r16_le_of_sendsOkS H ht (seg_sendsOk nloc ngl t ht (by omega) h19) hr hi hb hs

end

end WasmBase
