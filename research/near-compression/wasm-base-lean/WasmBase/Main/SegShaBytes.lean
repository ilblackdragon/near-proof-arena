import WasmBase.Main.SegShaMpath

/-!
# WasmBase.Main.SegShaBytes — BYTE lookups on a segment trace (E2E M4b)

MEMB's data limbs encode its byte columns only if those are bytes and the split columns are
`b5 >> 5`, `b2 >> 2` (`Main/SegRows.dataW_eval`).  Both come from lookups: BYTE (bus 4) for the
bytes `bi` and the splits, R16 for the split remainders.  This file gives the BYTE side for
`wasmBaseSegAir` under `HoldsX`:

* `seg_hsend_byte`: every BYTE **send** of a segment trace has count ≤ 1 (the same three routes as
  `seg_hsend_r16`: the instruction chips' `*_counts_of`, MEMB's `kD`/`kD·(1 − ro)`, and the
  syntactic `BitS` check `SendsOkB` for every other table);
* `seg_byte_recv`: the only BYTE receiver is the BYTE table (16), whose messages are
  `[k, X, Y, …]` with `X, Y < 256`;
* `seg_byte_lt`: a BYTE query `[k, x, y, z]` with count 1 has `x, y < 256`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-- Every send on bus `b` of `T` has a `BitS` count. -/
def SendsOkB (b : Nat) (T : Table) : Bool :=
  T.inters.all (fun i => decide (i.bus ≠ b) || !i.send || BitS (bcOf T) (beOf T) i.count)

theorem le_of_sendsOkB {A : Air} {pub : List F} {tr : Trace} (H : HoldsC A pub tr) {b t : Nat}
    (ht : t < A.tables.length) (hok : SendsOkB b (A.tables[t]'ht) = true) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) (hb : i.bus = b) (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  have hc := List.all_eq_true.mp hok i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  rcases hc with (hc | hc) | hc
  · exact absurd hb hc
  · rw [hs] at hc; exact absurd hc (by decide)
  · rcases bitS_sound H ht hr _ hc with h | h <;> rw [h] <;> decide

theorem seg_sendsOkB (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 →
      SendsOkB busByte ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 →
      SendsOkB busByte ((wasmBaseSegAir 0 0).tables[t]'ht) = true := by
    decide +kernel
  simp only [e]; exact h0

theorem memb_byte_shape : Memb.table.inters.all (fun i => decide (i.bus ≠ busByte) || !i.send ||
    decide (i.count = Memb.kD) || decide (i.count = Memb.kD * (1 - Memb.c "ro")) ||
    BitS (bcOf Memb.table) (beOf Memb.table) i.count) = true := by
  decide +kernel

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **The BYTE send bound of `wasmBaseSegAir`.** -/
theorem seg_hsend_byte :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busByte → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqX H ht (chipT t) hT hr
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
      table_constr_eqX H ht RetT.table (seg_t14' nloc ngl) hr
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
    · rw [hc]; exact (memb_kD_le H hr).1
    · rw [hc]; exact (memb_kD_le H hr).2
    · have hT := seg_t19 nloc ngl
      rcases bitS_sound H.toC ht hr i.count (by rw [hT]; exact hc) with h | h <;> rw [h] <;> decide
  · exact le_of_sendsOkB H.toC ht (seg_sendsOkB nloc ngl t ht (by omega) h19) hr hi hb hs

omit H in
theorem seg_byte_recv_tables (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 16 →
      ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus = busByte → i.send = true := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), t ≠ 16 →
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => decide (i.bus ≠ busByte) || i.send) = true := by
    decide +kernel
  intro t ht h16 i hi hb
  have := List.all_eq_true.mp (h0 t (by simpa [e] using ht) h16) i (by simpa [e] using hi)
  simpa [hb] using this

omit H in
theorem seg_t16 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[16]'(by simp [seg_air_len]) = Byte.table := rfl

theorem byte_bitsX {r : Nat} (hr : r < tr.height 16) : ∀ i, i < 16 → rowNat tr 16 r i ≤ 1 := by
  intro i hi
  have hc := table_constrX H (show 16 < (wasmBaseSegAir nloc ngl).tables.length by simp [seg_air_len]) hr
  rw [seg_t16] at hc
  have := hc (Chips.bool (v i)) (by
    simp only [Byte.table, Byte.constraints, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨i, hi, rfl⟩)
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at this
  rcases bool_nat (rowNat_lt _ _ _ _) this with h | h <;> omega

/-- The byte-pair predicate of a BYTE message. -/
def BytePair (m : List F) : Prop := ∃ a x y c, x < 256 ∧ y < 256 ∧ m = [a, ((x : Nat) : F), ((y : Nat) : F), c]

/-- Every BYTE receive is a byte pair. -/
theorem seg_byte_recv :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busByte → o.2.1 = false → o.2.2.2 ≠ 0 → BytePair o.2.2.1 := by
  intro o ho hb hs _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  by_cases h16 : t = 16
  · subst h16
    rw [seg_t16] at hi
    have hbit := byte_bitsX H hr
    have hx := bits8_lt (fun i => rowNat tr 16 r i) (fun i hi => hbit i (by omega))
    have hy := bits8_lt (fun i => rowNat tr 16 r (8 + i)) (fun i hi => hbit (8 + i) (by omega))
    have eX : Byte.X.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = ((bits8 fun i => rowNat tr 16 r i : Nat) : F) := by
      simp only [Byte.X, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
        Expr.eval_c, Expr.eval_col, natRow, v, Byte.xb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
      exact cast_bits8 _
    have eY : Byte.Y.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = ((bits8 fun i => rowNat tr 16 r (8 + i) : Nat) : F) := by
      simp only [Byte.Y, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
        Expr.eval_c, Expr.eval_col, natRow, v, Byte.yb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
      exact cast_bits8 (fun i => rowNat tr 16 r (8 + i))
    rw [row_eq_natRow]
    simp only [Byte.table, Byte.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, _, _, hx, hy, by simp only [List.map_cons, List.map_nil, eX, eY]; rfl⟩
  · exact absurd hs (by rw [seg_byte_recv_tables nloc ngl t ht h16 i hi hb]; decide)

/-- **A BYTE query with count 1 on a segment trace has byte operands.** -/
theorem seg_byte_lt {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busByte)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) : BytePair o.2.2.1 :=
  lookup_soundX H busByte (by decide) BytePair (seg_byte_recv H) (seg_hsend_byte H) ho hb hs hc

end
end SegSha

#print axioms SegSha.seg_hsend_byte
#print axioms SegSha.seg_byte_lt

end WasmBase
