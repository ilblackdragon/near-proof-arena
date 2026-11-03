import WasmBase.Main.SegGrow

/-!
# WasmBase.Main.SegGrowSend — the R16 send bound of `wasmBaseSegAirG` (E2E M4c, GROW follow-up)

Discharges `SegGSendR16` (`Main/SegGrow.lean`) from `HoldsX (wasmBaseSegAirG …)` alone, as
`seg_hsend_r16` does for `wasmBaseSegAir`:

* tables 1–14: the instruction chips and RET + tombstone (`*_counts_of`);
* MEMB (19) and MEMBH (35, MEMB's constraints): counts `kD`, `kD·(1 − ro)` or `BitS` counts;
  `kD ≤ 1` by the one-hot position flags (`onehot_kd`, stated for any table carrying MEMB-shaped
  constraints, so it serves both indices);
* MEMBG (34): counts `kD` (`onehot_kd` again: the same one-hot constraints) or `BitS` counts;
* every other table (incl. MEMG 32 and SEGG 33): the decidable `R16SendsOk` check.

So `segG_grow_ok`, `segG_grow_fail` and `membg_range` hold with no send-bound premise
(`segG_grow_ok'`, `segG_grow_fail'`, `membg_range'`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

/-! ## One-hot position flags -/

/-- The sum of the 8 data-row flags `p0 … p7` (columns 1–8), MEMB's and MEMBG's `kD`. -/
def kd8 : Expr := sumE ((List.range 8).map fun i => v (1 + i))

theorem memb_kD_eq : Memb.kD = kd8 := by decide
theorem membg_kD_eq : MembG.kD = kd8 := by decide
theorem memb_ro_eq : Memb.c "ro" = v 11 := by decide

theorem kd8_unfold : kd8 = 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 + v 8 := rfl
theorem sum9_unfold : sumE ((List.range 9).map fun i => v (1 + i)) =
    0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 + v 8 + v 9 := rfl

/-- **One-hot flags**: if `act` (column 0) and `p0 … p8` (columns 1–9) are bits summing to `act`,
then `kD = p0 + … + p7` is a bit. -/
theorem onehot_kd {tr : Trace} {pub : List F} {t r : Nat} {cs : List Expr}
    (C : ∀ e ∈ cs, e.eval (tr.row pub t r) = 0)
    (hb : ∀ i, i < 9 → Chips.bool (v (1 + i)) ∈ cs) (ha : Chips.bool (v 0) ∈ cs)
    (hs : sumE ((List.range 9).map fun i => v (1 + i)) - v 0 ∈ cs) :
    kd8.eval (tr.row pub t r) = 0 ∨ kd8.eval (tr.row pub t r) = 1 := by
  have one : ((1 : Nat) : F) = 1 := rfl
  have cx : ∀ i, (v i).eval (tr.row pub t r) = tr.cell t r i := fun i => by
    simp [Chips.v, Expr.eval_col, Trace.row]
  have bit : ∀ i, Chips.bool (v i) ∈ cs → ∃ n : Nat, n ≤ 1 ∧ tr.cell t r i = (n : F) := by
    intro i hi
    have h := C _ hi
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', cx, Expr.eval_ofNat', one] at h
    exact bit_nat (bool_cases h)
  obtain ⟨a, ha1, ea⟩ := bit 0 ha
  obtain ⟨n1, h1, e1⟩ := bit 1 (hb 0 (by decide))
  obtain ⟨n2, h2, e2⟩ := bit 2 (hb 1 (by decide))
  obtain ⟨n3, h3, e3⟩ := bit 3 (hb 2 (by decide))
  obtain ⟨n4, h4, e4⟩ := bit 4 (hb 3 (by decide))
  obtain ⟨n5, h5, e5⟩ := bit 5 (hb 4 (by decide))
  obtain ⟨n6, h6, e6⟩ := bit 6 (hb 5 (by decide))
  obtain ⟨n7, h7, e7⟩ := bit 7 (hb 6 (by decide))
  obtain ⟨n8, h8, e8⟩ := bit 8 (hb 7 (by decide))
  obtain ⟨n9, h9, e9⟩ := bit 9 (hb 8 (by decide))
  have hsum := C _ hs
  rw [sum9_unfold] at hsum
  simp only [Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', cx, e1, e2, e3, e4, e5, e6, e7, e8, e9, ea] at hsum
  have hP := P_val
  have enat : n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 = a := by
    refine natEq ?_ (by omega) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add]
    have : ((0 : Nat) : F) = 0 := rfl
    grind
  rw [kd8_unfold]
  simp only [Expr.eval_add', Expr.eval_ofNat', cx, e1, e2, e3, e4, e5, e6, e7, e8]
  have hk : n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 ≤ 1 := by omega
  have eq : ((0 : Nat) : F) + (n1 : F) + (n2 : F) + (n3 : F) + (n4 : F) + (n5 : F) + (n6 : F) + (n7 : F) + (n8 : F) =
      ((n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add]
    have : ((0 : Nat) : F) = 0 := rfl
    grind
  rw [eq]
  rcases (show n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 = 0 ∨ n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 = 1 by omega)
    with h | h <;> rw [h]
  · left; rfl
  · right; rfl

theorem bit_toNat {x : F} (h : x = 0 ∨ x = 1) : x.toNat ≤ 1 := by
  rcases h with rfl | rfl <;> decide

theorem bit_mul_sub {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : x * (1 - y) = 0 ∨ x * (1 - y) = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> grind

/-! ## The constraint shapes -/

theorem all9 {cs : List Expr}
    (h : (List.range 9).all (fun i => cs.any (fun e => decide (e = Chips.bool (v (1 + i))))) = true) :
    ∀ i, i < 9 → Chips.bool (v (1 + i)) ∈ cs := by
  intro i hi
  exact any_mem (List.all_eq_true.mp h i (List.mem_range.mpr hi))

theorem memb_onehot_mem : (∀ i, i < 9 → Chips.bool (v (1 + i)) ∈ Memb.constraints) ∧ Chips.bool (v 0) ∈ Memb.constraints ∧
    sumE ((List.range 9).map fun i => v (1 + i)) - v 0 ∈ Memb.constraints ∧ Chips.bool (v 11) ∈ Memb.constraints :=
  ⟨all9 (by decide), any_mem (by decide), any_mem (by decide), any_mem (by decide)⟩

theorem membg_onehot_mem : (∀ i, i < 9 → Chips.bool (v (1 + i)) ∈ MembG.constraints) ∧ Chips.bool (v 0) ∈ MembG.constraints ∧
    sumE ((List.range 9).map fun i => v (1 + i)) - v 0 ∈ MembG.constraints :=
  ⟨all9 (by decide), any_mem (by decide), any_mem (by decide)⟩

/-- MEMBH's R16 sends: counts `kD`, `kD·(1 − ro)`, or a `BitS` count (as MEMB's). -/
theorem membh_r16_shape : MembH.table.inters.all (fun i => decide (i.bus ≠ busR16) || !i.send ||
    decide (i.count = Memb.kD) || decide (i.count = Memb.kD * (1 - Memb.c "ro")) ||
    BitS (bcOf MembH.table) (beOf MembH.table) i.count) = true := by
  decide +kernel

/-- MEMBG's R16 sends: count `kD`, or a `BitS` count. -/
theorem membg_r16_shape : MembG.table.inters.all (fun i => decide (i.bus ≠ busR16) || !i.send ||
    decide (i.count = MembG.kD) || BitS (bcOf MembG.table) (beOf MembG.table) i.count) = true := by
  decide +kernel

/-- Every grow-AIR table except 1–14, 19, 34, 35 passes the decidable check. -/
theorem segG_sendsOk (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAirG nloc ngl).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 → t ≠ 34 → t ≠ 35 →
      R16SendsOk ((wasmBaseSegAirG nloc ngl).tables[t]'ht) = true := by
  have e : (wasmBaseSegAirG nloc ngl).tables = (wasmBaseSegAirG 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAirG 0 0).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 → t ≠ 34 → t ≠ 35 →
      R16SendsOk ((wasmBaseSegAirG 0 0).tables[t]'ht) = true := by
    decide +kernel
  simp only [e]; exact h0

theorem segG_chipT (nloc ngl t : Nat) (h1 : 1 ≤ t) (h13 : t ≤ 13) :
    (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t (by omega)) = chipT t := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
    t = 12 ∨ t = 13 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem segG_t14' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[14]'(segG_lt nloc ngl 14 (by decide)) = RetT.table := rfl
theorem segG_t19' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[19]'(segG_lt nloc ngl 19 (by decide)) = Memb.table := rfl

/-! ## The bound -/

section send
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- A MEMB-shaped row (table 19 or 35): `kD` and `kD·(1 − ro)` are bits. -/
theorem membLike_kD {t : Nat} (ht : t < 36) (hT : (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht) = Memb.table ∨
    (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht) = MembH.table) {r : Nat} (hr : r < tr.height t) :
    (Memb.kD.eval (tr.row pub t r)).toNat ≤ 1 ∧ ((Memb.kD * (1 - Memb.c "ro")).eval (tr.row pub t r)).toNat ≤ 1 := by
  have hc : ((wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht)).constraints = Memb.constraints := by
    rcases hT with h | h <;> rw [h] <;> rfl
  have C : ∀ e ∈ Memb.constraints, e.eval (tr.row pub t r) = 0 := by
    intro e he; exact H.constr t (segG_lt nloc ngl t ht) r hr e (by rw [hc]; exact he)
  obtain ⟨hb, ha, hs, hro⟩ := memb_onehot_mem
  have k := onehot_kd C hb ha hs
  have one : ((1 : Nat) : F) = 1 := rfl
  have ro : (v 11).eval (tr.row pub t r) = 0 ∨ (v 11).eval (tr.row pub t r) = 1 := by
    have h := C _ hro
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', one] at h
    exact bool_cases h
  rw [memb_kD_eq, memb_ro_eq]
  refine ⟨bit_toNat k, ?_⟩
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', one]
  exact bit_toNat (bit_mul_sub k ro)

theorem membg_kD {r : Nat} (hr : r < tr.height 34) : (MembG.kD.eval (tr.row pub 34 r)).toNat ≤ 1 := by
  have C : ∀ e ∈ MembG.constraints, e.eval (tr.row pub 34 r) = 0 := by
    intro e he; exact H.constr 34 (segG_lt nloc ngl 34 (by decide)) r hr e (by rw [segG_t34']; exact he)
  obtain ⟨hb, ha, hs⟩ := membg_onehot_mem
  rw [membg_kD_eq]
  exact bit_toNat (onehot_kd C hb ha hs)

/-- **The R16 send bound of `wasmBaseSegAirG`**: `SegGSendR16` from `HoldsX` alone. -/
theorem segG_hsend_r16 : SegGSendR16 nloc ngl pub tr := by
  intro o ho hb hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  have ht36 : t < 36 := by rw [segG_len] at ht; exact ht
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have hT := segG_chipT nloc ngl t hc.1 hc.2
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
      table_constr_eqX H ht RetT.table (segG_t14' nloc ngl) hr
    rw [segG_t14'] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ret_counts_of hcon i hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; exact absurd hb (by decide)
  by_cases h19 : t = 19 ∨ t = 35
  · have hT : (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht36) = Memb.table ∨
        (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht36) = MembH.table := by
      rcases h19 with rfl | rfl
      · exact Or.inl (segG_t19' nloc ngl)
      · exact Or.inr (segG_t35' nloc ngl)
    have hk := membLike_kD H ht36 hT hr
    rcases h19 with rfl | rfl
    · rw [segG_t19'] at hi
      have hc := List.all_eq_true.mp memb_r16_shape i hi
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      rcases hc with (((hc | hc) | hc) | hc) | hc
      · exact absurd hb hc
      · rw [hs] at hc; exact absurd hc (by decide)
      · rw [hc]; exact hk.1
      · rw [hc]; exact hk.2
      · rcases bitS_sound H.toC ht hr i.count (by rw [segG_t19']; exact hc) with h | h <;> rw [h] <;> decide
    · rw [segG_t35'] at hi
      have hc := List.all_eq_true.mp membh_r16_shape i hi
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      rcases hc with (((hc | hc) | hc) | hc) | hc
      · exact absurd hb hc
      · rw [hs] at hc; exact absurd hc (by decide)
      · rw [hc]; exact hk.1
      · rw [hc]; exact hk.2
      · rcases bitS_sound H.toC ht hr i.count (by rw [segG_t35']; exact hc) with h | h <;> rw [h] <;> decide
  by_cases h34 : t = 34
  · subst h34
    rw [segG_t34'] at hi
    have hc := List.all_eq_true.mp membg_r16_shape i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · exact absurd hb hc
    · rw [hs] at hc; exact absurd hc (by decide)
    · rw [hc]; exact membg_kD H hr
    · rcases bitS_sound H.toC ht hr i.count (by rw [segG_t34']; exact hc) with h | h <;> rw [h] <;> decide
  · exact r16_le_of_sendsOk H.toC ht (segG_sendsOk nloc ngl t ht (by omega) (by omega) h34 (by omega)) hr hi hb hs

/-- `segG_grow_ok` without the send-bound premise. -/
theorem segG_grow_ok' {r : Nat} (hr : r < tr.height 32)
    (hg : rowNat tr 32 r MemG.fGrow = 1) (hok : rowNat tr 32 r MemG.ok = 1) :
    rowNat tr 32 r MemG.old + (rowNat tr 32 r MemG.n0 + 65536 * rowNat tr 32 r MemG.n1) +
      rowNat tr 32 r MemG.d = maxPagesM3 :=
  segG_grow_ok H (segG_hsend_r16 H) hr hg hok

/-- `segG_grow_fail` without the send-bound premise. -/
theorem segG_grow_fail' {r : Nat} (hr : r < tr.height 32)
    (hg : rowNat tr 32 r MemG.fGrow = 1) (hok : rowNat tr 32 r MemG.ok = 0) :
    rowNat tr 32 r MemG.old + (rowNat tr 32 r MemG.n0 + 65536 * rowNat tr 32 r MemG.n1) =
      maxPagesM3 + 1 + (rowNat tr 32 r MemG.e0 + 65536 * rowNat tr 32 r MemG.e1) :=
  segG_grow_fail H (segG_hsend_r16 H) hr hg hok

/-- `membg_range` without the send-bound premise. -/
theorem membg_range' {r : Nat} (hr : r < tr.height 34) (hp8 : mgN tr r 9 = 1)
    (hold : mgN tr r 13 ≤ 2048) (hnew : mgN tr r 14 ≤ 2048) (hnew1 : 1 ≤ mgN tr r 14)
    (hnin : (pNin pub).toNat ≤ 2 ^ 17) :
    64 * mgN tr r 13 ≤ mgN tr r 10 ∧ mgN tr r 10 < 64 * mgN tr r 14 ∧ (pNin pub).toNat ≤ mgN tr r 10 :=
  membg_range H (segG_hsend_r16 H) hr hp8 hold hnew hnew1 hnin

end send

/-! ## Every grown block belongs to a successful `memory.grow` row of the segment -/

/-- Only MEMG receives on the grow bus 213, only MEMBG sends on it. -/
theorem segG_grow_bus (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAirG nloc ngl).tables.length),
      ((wasmBaseSegAirG nloc ngl).tables[t]'ht).inters.all
        (fun i => i.bus != busGrow || (decide (t = 32) && !i.send) || (decide (t = 34) && i.send)) = true := by
  have e : (wasmBaseSegAirG nloc ngl).tables = (wasmBaseSegAirG 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAirG 0 0).tables.length),
      ((wasmBaseSegAirG 0 0).tables[t]'ht).inters.all
        (fun i => i.bus != busGrow || (decide (t = 32) && !i.send) || (decide (t = 34) && i.send)) = true := by
    decide +kernel
  simp only [e]; exact h0

theorem memg_grow_recv : MemG.table.inters.filter (fun i => i.bus = busGrow ∧ i.send = false) =
    [⟨busGrow, false, v MemG.gm, [v cTs, v MemG.old, MemG.newE]⟩] := by decide +kernel

theorem membg_grow_send : MembG.table.inters.filter (fun i => i.bus = busGrow ∧ i.send = true) =
    [⟨busGrow, true, MembG.p 8, [MembG.c "tg", MembG.c "gold", MembG.c "gnew"]⟩] := by decide +kernel

theorem mem_filter_of {T : Table} {i : Inter} {b : Nat} {s : Bool} (hi : i ∈ T.inters) (hb : i.bus = b)
    (hs : i.send = s) : i ∈ T.inters.filter (fun i => i.bus = b ∧ i.send = s) :=
  List.mem_filter.mpr ⟨hi, by simp [hb, hs]⟩

/-- A successful grow row's offer `[ts, old, old + n]` (field values). -/
def growMsg (tr : Trace) (pub : List F) (r : Nat) : List F :=
  [v cTs, v MemG.old, MemG.newE].map (·.eval (tr.row pub 32 r))

section link
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- **Every grown block of the segment belongs to a successful grow row of the segment**: an active
MEMBG padding row's `[tg, gold, gnew]` is a MEMG row's `[ts, old, old + n]` with `ok = 1`.  (The
link that fuses MEMBG's zero-byte productions into that grow row's productions.) -/
theorem membg_grow_link {r : Nat} (hr : r < tr.height 34) (hp8 : rowNat tr 34 r 9 = 1) :
    ∃ r', r' < tr.height 32 ∧ rowNat tr 32 r' MemG.ok = 1 ∧
      [MembG.c "tg", MembG.c "gold", MembG.c "gnew"].map (·.eval (tr.row pub 34 r)) = growMsg tr pub r' := by
  have hx : busGrow ≠ extBus := by decide
  have hcnt : ((MembG.p 8).eval (tr.row pub 34 r)).toNat = 1 := by
    rw [MembG.p, MembG.c, mg_ix_p 8 (by decide), col_eval_nat, hp8]; decide
  have hi : (⟨busGrow, true, MembG.p 8, [MembG.c "tg", MembG.c "gold", MembG.c "gnew"]⟩ : Inter) ∈
      ((wasmBaseSegAirG nloc ngl).tables[34]'(segG_lt nloc ngl 34 (by decide))).inters := by
    rw [segG_t34']
    have := membg_grow_send ▸ List.mem_singleton_self _
    exact (List.mem_filter.mp this).1
  have ho := occ_of_inter (segG_lt nloc ngl 34 (by decide)) hr hi hcnt
  refine lookup_soundX H busGrow hx
    (fun m => ∃ r', r' < tr.height 32 ∧ rowNat tr 32 r' MemG.ok = 1 ∧ m = growMsg tr pub r') ?_ ?_ ho rfl rfl rfl
  · intro o ho' hb hs hc
    obtain ⟨t, ht, r', hr', i, hi', rfl⟩ := mem_occs.mp ho'
    simp only at hb hs hc ⊢
    have hall := List.all_eq_true.mp (segG_grow_bus nloc ngl t ht) i hi'
    simp only [hb, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      hs, Bool.not_false, and_true, Bool.false_eq_true, and_false, or_false] at hall
    subst hall
    rw [segG_t32'] at hi'
    have hf := mem_filter_of hi' hb hs
    rw [memg_grow_recv, List.mem_singleton] at hf
    subst hf
    refine ⟨r', hr', ?_, rfl⟩
    have hgm : rowNat tr 32 r' MemG.gm ≠ 0 := by
      intro h0; apply hc; simp only [col_eval_nat, h0]; rfl
    have hb' := segG_memg_constr H hr' (e := bool (v MemG.ok)) (by simp [MemG.table, MemG.constraints])
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', col_eval_nat] at hb'
    rcases bool_nat (rowNat_lt tr 32 r' MemG.ok) hb' with h | h
    · exact absurd (segG_grow_gm H hr' h) hgm
    · exact h
  · intro o ho' hb hs
    obtain ⟨t, ht, r', hr', i, hi', rfl⟩ := mem_occs.mp ho'
    simp only at hb hs ⊢
    have hall := List.all_eq_true.mp (segG_grow_bus nloc ngl t ht) i hi'
    simp only [hb, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      hs, Bool.not_true, and_false, false_or, and_true] at hall
    have h34 : t = 34 := by
      rcases hall with ⟨-, h⟩ | h
      · exact absurd h (by decide)
      · exact h
    subst h34
    rw [segG_t34'] at hi'
    have hf := mem_filter_of hi' hb hs
    rw [membg_grow_send, List.mem_singleton] at hf
    subst hf
    have hpb := membg_constr H hr' (e := Chips.bool (MembG.p 8)) (any_mem (by decide))
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at hpb
    exact bit_toNat (bool_cases hpb)

end link

end WasmBase

#print axioms WasmBase.segG_hsend_r16
#print axioms WasmBase.segG_grow_ok'
#print axioms WasmBase.membg_range'
#print axioms WasmBase.membg_grow_link
