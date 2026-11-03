import WasmBase.Main.SegMemb
import WasmBase.Main.RegSend
/-!
# WasmBase.Main.SegSend — the R16 send bound of `wasmBaseSegAir`

`seg_hsend_r16`: on a satisfied segment trace every R16 **send** has count ≤ 1, so the `hsend`
hypothesis of `Main/SegMemb.lean`'s block-order lemmas is discharged
(`memb_blk_strict_of_holds`, `memb_blk_distinct_of_holds`).

Three routes, by table:

* **instruction chips 1–13** (`wasmBaseAir`'s tables at the same indices) and **RET** (14, `RetT` has
  RET's constraints and RET's interactions plus a bus-12 tombstone): the per-chip `*_counts_of`
  lemmas (every count of the chip is ≤ 1, from its own constraints);
* **MEMB** (19): its R16 counts are `kD = p0 + … + p7` and `kD·(1 − ro)` (≤ 1 by the one-hot
  `memb_row`: `Σ p_i = act` with `act` a bit), or `p8`, `trans·p8·nxt.p0`;
* **every other table**: a decidable syntactic check `R16SendsOk` — every R16 send count is built
  by products and `1 − ·` from bool-constrained columns (current or **next** row), bool-constrained
  expressions, the selectors `first/last/trans` and the constants 0, 1 (`bitS_sound`).  This
  extends `RegSendM2`'s `BitE` with next-row columns and selectors (the segment tables use them).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## The extended bit checker -/

/-- The column `i` of a constraint `bool (v i)`. -/
def boolCol? : Expr → Option Nat
  | .mul (.col i) (.sub (.col j) (.c 1)) => if i = j then some i else none
  | _ => none

/-- The expression `e` of a constraint `bool e`. -/
def boolExp? : Expr → Option Expr
  | .mul a (.sub b (.c 1)) => if a = b then some a else none
  | _ => none

theorem boolCol?_spec {e : Expr} {i : Nat} (h : boolCol? e = some i) : e = bool (v i) := by
  unfold boolCol? at h
  split at h
  · rename_i i' j
    split at h
    · rename_i hij; subst hij; cases h; rfl
    · cases h
  · cases h

theorem boolExp?_spec {e a : Expr} (h : boolExp? e = some a) : e = bool a := by
  unfold boolExp? at h
  split at h
  · rename_i a' b
    split at h
    · rename_i hab; subst hab; cases h; rfl
    · cases h
  · cases h

def bcOf (T : Table) : List Nat := T.constraints.filterMap boolCol?
def beOf (T : Table) : List Expr := T.constraints.filterMap boolExp?

theorem bcOf_mem {T : Table} {i : Nat} (h : i ∈ bcOf T) : bool (v i) ∈ T.constraints := by
  obtain ⟨e, he, hs⟩ := List.mem_filterMap.mp h
  rw [← boolCol?_spec hs]; exact he

theorem beOf_mem {T : Table} {a : Expr} (h : a ∈ beOf T) : bool a ∈ T.constraints := by
  obtain ⟨e, he, hs⟩ := List.mem_filterMap.mp h
  rw [← boolExp?_spec hs]; exact he

/-- `e` is a bit by construction from `bc` (bool columns, current or next row), `be` (bool
expressions, current row), selectors, `0`, `1`, products and `1 − ·`. -/
def BitS (bc : List Nat) (be : List Expr) : Expr → Bool
  | .mul a b => be.any (fun x => decide (x = .mul a b)) || (BitS bc be a && BitS bc be b)
  | .sub a b => be.any (fun x => decide (x = .sub a b)) || (decide (a = .c 1) && BitS bc be b)
  | .first => true
  | .last => true
  | .trans => true
  | .c n => decide (n ≤ 1)
  | .col i => bc.any (fun x => decide (x = i)) || be.any (fun x => decide (x = .col i))
  | .nxt i => bc.any (fun x => decide (x = i))
  | e => be.any (fun x => decide (x = e))

theorem any_mem {α : Type} [DecidableEq α] {l : List α} {a : α} (h : l.any (fun x => decide (x = a)) = true) :
    a ∈ l := by
  obtain ⟨x, hx, he⟩ := List.any_eq_true.mp h
  rw [decide_eq_true_eq] at he; exact he ▸ hx

theorem bit01 {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := bool_cases h

/-- **Soundness of `BitS`** on row `r` of table `t` of a satisfied trace. -/
theorem bitS_sound {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) {r : Nat} (hr : r < tr.height t) :
    ∀ e, BitS (bcOf (A.tables[t]'ht)) (beOf (A.tables[t]'ht)) e = true →
      e.eval (tr.row pub t r) = 0 ∨ e.eval (tr.row pub t r) = 1 := by
  have hpos : 0 < tr.height t := by omega
  have rowbit : ∀ r', r' < tr.height t → ∀ i ∈ bcOf (A.tables[t]'ht), tr.cell t r' i = 0 ∨ tr.cell t r' i = 1 := by
    intro r' hr' i hi
    have h := H.constr t ht r' hr' _ (bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', cast_one,
      Trace.row] at h
    exact bit01 h
  have expbit : ∀ a ∈ beOf (A.tables[t]'ht), a.eval (tr.row pub t r) = 0 ∨ a.eval (tr.row pub t r) = 1 := by
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

/-- Every R16 send count of `T` passes `BitS`. -/
def R16SendsOk (T : Table) : Bool :=
  T.inters.all (fun i => decide (i.bus ≠ busR16) || !i.send || BitS (bcOf T) (beOf T) i.count)

theorem r16_le_of_sendsOk {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) (hok : R16SendsOk (A.tables[t]'ht) = true) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) (hb : i.bus = busR16) (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  have hc := List.all_eq_true.mp hok i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  rcases hc with (hc | hc) | hc
  · exact absurd hb hc
  · rw [hs] at hc; exact absurd hc (by decide)
  · rcases bitS_sound H ht hr _ hc with h | h <;> rw [h] <;> decide

/-! ## The tables -/

/-- Every segment table except the instruction chips (1–14) and MEMB (19) passes the check. -/
theorem seg_sendsOk (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 →
      R16SendsOk ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 →
      R16SendsOk ((wasmBaseSegAir 0 0).tables[t]'ht) = true := by
    decide +kernel
  simp only [e]; exact h0

/-- Tables 1–13 of the segment AIR are the instruction chips. -/
theorem seg_chipT (nloc ngl t : Nat) (h1 : 1 ≤ t) (h13 : t ≤ 13) :
    (wasmBaseSegAir nloc ngl).tables[t]'(by simp [seg_air_len]; omega) = chipT t := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
    t = 12 ∨ t = 13 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem seg_t14' (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[14]'(by simp [seg_air_len]) = RetT.table := rfl

/-- MEMB's R16 sends: counts `kD`, `kD·(1 − ro)`, or a `BitS` count. -/
theorem memb_r16_shape : Memb.table.inters.all (fun i => decide (i.bus ≠ busR16) || !i.send ||
    decide (i.count = Memb.kD) || decide (i.count = Memb.kD * (1 - Memb.c "ro")) ||
    BitS (bcOf Memb.table) (beOf Memb.table) i.count) = true := by
  decide +kernel

section send
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- `kD ≤ 1` and `kD·(1 − ro) ≤ 1` on a MEMB row (the one-hot `memb_row`). -/
theorem memb_kD_le {r : Nat} (hr : r < tr.height 19) :
    (Memb.kD.eval (tr.row pub 19 r)).toNat ≤ 1 ∧
      ((Memb.kD * (1 - Memb.c "ro")).eval (tr.row pub 19 r)).toNat ≤ 1 := by
  obtain ⟨ha, bp, hs⟩ := memb_row H hr
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
    have h := memb_C H hr (Chips.bool (Memb.c "ro")) (by simp [Memb.constraints])
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
theorem seg_hsend_r16 :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eq H ht (chipT t) hT hr
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
      table_constr_eq H ht RetT.table (seg_t14' nloc ngl) hr
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
    · rw [hc]; exact (memb_kD_le H hr).1
    · rw [hc]; exact (memb_kD_le H hr).2
    · have hT := seg_t19 nloc ngl
      rcases bitS_sound H ht hr i.count (by rw [hT]; exact hc) with h | h <;> rw [h] <;> decide
  · exact r16_le_of_sendsOk H ht (seg_sendsOk nloc ngl t ht (by omega) h19) hr hi hb hs

/-- **`memb_blk_strict` without `hsend`.** -/
theorem memb_blk_strict_of_holds :
    ∀ b d, 9 * (b + d + 1) + 8 < tr.height 19 → mbN tr (9 * (b + d + 1) + 8) 0 = 1 →
      mbN tr (9 * b + 8) 10 < mbN tr (9 * (b + d + 1) + 8) 10 :=
  memb_blk_strict H (seg_hsend_r16 H)

/-- **`memb_blk_distinct` without `hsend`: the touched blocks of a segment are distinct.** -/
theorem memb_blk_distinct_of_holds {b b' : Nat} (hb : b ≠ b') (hr : 9 * b + 8 < tr.height 19)
    (hr' : 9 * b' + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) (ha' : mbN tr (9 * b' + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 ≠ mbN tr (9 * b' + 8) 10 :=
  memb_blk_distinct H (seg_hsend_r16 H) hb hr hr' ha ha'

end send

end WasmBase

#print axioms WasmBase.seg_hsend_r16
#print axioms WasmBase.memb_blk_strict_of_holds
#print axioms WasmBase.memb_blk_distinct_of_holds
