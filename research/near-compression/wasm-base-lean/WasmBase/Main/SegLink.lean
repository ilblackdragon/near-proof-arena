import WasmBase.Main.SegCuto
import WasmBase.Main.SegLinkSpec

/-!
# WasmBase.Main.SegLink — the CUTO link (E2E M4b, S3)

(module documentation at the end of the file's development; see `cuto_link`)
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. CUTO row facts, as naturals -/

theorem cuto_ix2 : ix Cut.Out.cols "space" = 47 ∧ ix Cut.Out.cols "slot" = 48 ∧ ix Cut.Out.cols "x2" = 49 ∧
    ix Cut.Out.cols "tp" = 50 ∧ ix Cut.Out.cols "k0" = 51 ∧ ix Cut.Out.cols "k2" = 52 ∧
    ix Cut.Out.cols "k4" = 53 ∧ ix Cut.Out.cols "k5" = 54 ∧ ix Cut.Out.cols "k6" = 55 ∧
    ix Cut.Out.cols "kL" = 56 ∧ ix Cut.Out.cols "clo" = 57 ∧ ix Cut.Out.cols "chi" = 58 ∧
    ix Cut.Out.cols "dep" = 59 ∧ ix Cut.Out.cols "mm" = 60 ∧ ix Cut.Out.cols "rlo" = 64 ∧
    ix Cut.Out.cols "rhi" = 65 := by decide

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- A boolean column of CUTO is 0 or 1. -/
theorem cuto_boolc {r : Nat} (hr : r < tr.height 31) {s : String} {i : Nat} (hi : ix Cut.Out.cols s = i)
    (hm : bool (Cut.Out.c s) ∈ Cut.Out.constraints) : rowNat tr 31 r i = 0 ∨ rowNat tr 31 r i = 1 := by
  have e := cuto_constr H hr hm
  simp only [Chips.bool, Cut.Out.c, Cut.c, hi, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', row_cur] at e
  exact bool_nat (rowNat_lt tr 31 r i) e

/-- The kind flags of a CUTO row: bits, and on an active row exactly one is set. -/
theorem cuto_kinds {r : Nat} (hr : r < tr.height 31) :
    rowNat tr 31 r 51 ≤ 1 ∧ rowNat tr 31 r 52 ≤ 1 ∧ rowNat tr 31 r 53 ≤ 1 ∧ rowNat tr 31 r 54 ≤ 1 ∧
      rowNat tr 31 r 55 ≤ 1 ∧ rowNat tr 31 r 56 ≤ 1 ∧
      rowNat tr 31 r 51 + rowNat tr 31 r 52 + rowNat tr 31 r 53 + rowNat tr 31 r 54 + rowNat tr 31 r 55 +
        rowNat tr 31 r 56 = rowNat tr 31 r 0 := by
  obtain ⟨-, -, -, -, i51, i52, i53, i54, i55, i56, -⟩ := cuto_ix2
  have b51 := cuto_boolc H hr i51 (by simp [Cut.Out.constraints])
  have b52 := cuto_boolc H hr i52 (by simp [Cut.Out.constraints])
  have b53 := cuto_boolc H hr i53 (by simp [Cut.Out.constraints])
  have b54 := cuto_boolc H hr i54 (by simp [Cut.Out.constraints])
  have b55 := cuto_boolc H hr i55 (by simp [Cut.Out.constraints])
  have b56 := cuto_boolc H hr i56 (by simp [Cut.Out.constraints])
  obtain ⟨ba, -⟩ := cuto_bits H hr
  have e := cuto_constr H hr (e := Cut.Out.c "k0" + Cut.Out.c "k2" + Cut.Out.c "k4" + Cut.Out.c "k5" +
    Cut.Out.c "k6" + Cut.Out.c "kL" - Cut.Out.c "act") (by simp [Cut.Out.constraints])
  obtain ⟨i0, -⟩ := cuto_ix
  simp only [Cut.Out.c, Cut.c, i0, i51, i52, i53, i54, i55, i56, v, Expr.eval_add', Expr.eval_sub',
    Expr.eval_col, row_cur] at e
  have hs : ((rowNat tr 31 r 51 + rowNat tr 31 r 52 + rowNat tr 31 r 53 + rowNat tr 31 r 54 +
      rowNat tr 31 r 55 + rowNat tr 31 r 56 : Nat) : F) = ((rowNat tr 31 r 0 : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add]; grind
  have hP := P_val
  have := natEq hs (by omega) (rowNat_lt tr 31 r 0)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, this⟩

end

theorem cuto_evalc (tr : Trace) (pub : List F) (r : Nat) {s : String} {i : Nat} (hi : ix Cut.Out.cols s = i) :
    (Cut.Out.c s).eval (tr.row pub 31 r) = ((rowNat tr 31 r i : Nat) : F) := by
  simp only [Cut.Out.c, Cut.c, hi, v, Expr.eval_col, row_cur]

theorem cuto_evalF (tr : Trace) (pub : List F) (r : Nat) {k : Nat} (hk : k < 7) :
    (Cut.Out.F k).eval (tr.row pub 31 r) = ((cutoF tr r k : Nat) : F) := by
  simp only [Cut.Out.F, Cut.F, Cut.c, cuto_ix_lo k hk, cuto_ix_hi k hk, v, Expr.eval_add', Expr.eval_mul',
    Expr.eval_col, Expr.eval_ofNat', row_cur, fcast, cutoF]

theorem f_sub_eq {a b : F} (h : a - b = 0) : a = b := by grind
theorem f_mul_one_sub {g a : F} (h : (1 - g) * a = 0) (hg : g = 0) : a = 0 := by subst hg; grind
theorem f_mul_g {g a : F} (h : g * a = 0) (hg : g = 1) : a = 0 := by subst hg; grind

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **The field facts of an active CUTO row** (with the chip limb bound): its kind decides the
consumed space and how the hashed fields `F0, F1, F5` come from the raw columns. -/
theorem cuto_fieldfacts (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    (rowNat tr 31 r 56 = 0 → rowNat tr 31 r 47 = 2 * rowNat tr 31 r 52 + 4 * rowNat tr 31 r 53 +
        5 * rowNat tr 31 r 54 + 6 * rowNat tr 31 r 55 ∧ cutoF tr r 0 = rowNat tr 31 r 47) ∧
    (rowNat tr 31 r 56 = 1 → ((rowNat tr 31 r 47 : Nat) : F) =
        16 + ((rowNat tr 31 r 57 : Nat) : F) + ((65536 : Nat) : F) * ((rowNat tr 31 r 58 : Nat) : F)) ∧
    (rowNat tr 31 r 53 = 0 → cutoF tr r 1 = rowNat tr 31 r 48) ∧
    (rowNat tr 31 r 53 = 1 → cutoF tr r 1 = rowNat tr 31 r 59) ∧
    (rowNat tr 31 r 53 = 0 → cutoF tr r 5 = rowNat tr 31 r 49) := by
  obtain ⟨i47, i48, i49, -, -, i52, i53, i54, i55, i56, i57, i58, i59, -⟩ := cuto_ix2
  have hP := P_val
  have hF : ∀ k, k < 7 → cutoF tr r k < P := fun k hk => by have := cutoF_lt H hl hr ha hk; omega
  have hN := rowNat_lt tr 31 r
  have C := fun e he => cuto_constr H hr (e := e) he
  have ev := fun {s : String} {i : Nat} (hi : ix Cut.Out.cols s = i) => cuto_evalc tr pub r hi
  have eF := fun {k : Nat} (hk : k < 7) => cuto_evalF tr pub r hk
  have e2 := C ((1 - Cut.Out.c "kL") * (Cut.Out.c "space" - 2 * Cut.Out.c "k2" - 4 * Cut.Out.c "k4" -
    5 * Cut.Out.c "k5" - 6 * Cut.Out.c "k6")) (by simp [Cut.Out.constraints])
  have e3 := C (Cut.Out.c "kL" * (Cut.Out.c "space" - 16 - Cut.Out.c "clo" - 65536 * Cut.Out.c "chi"))
    (by simp [Cut.Out.constraints])
  have e4 := C ((1 - Cut.Out.c "kL") * (Cut.Out.F 0 - Cut.Out.c "space")) (by simp [Cut.Out.constraints])
  have e5 := C ((1 - Cut.Out.c "k4") * (Cut.Out.F 1 - Cut.Out.c "slot")) (by simp [Cut.Out.constraints])
  have e6 := C (Cut.Out.c "k4" * (Cut.Out.F 1 - Cut.Out.c "dep")) (by simp [Cut.Out.constraints])
  have e7 := C ((1 - Cut.Out.c "k4") * (Cut.Out.F 5 - Cut.Out.c "x2")) (by simp [Cut.Out.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', ev i47, ev i48, ev i49, ev i52, ev i53,
    ev i54, ev i55, ev i56, ev i57, ev i58, ev i59, eF (show 0 < 7 by omega), eF (show 1 < 7 by omega),
    eF (show 5 < 7 by omega)] at e2 e3 e4 e5 e6 e7
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h0 => ?_, fun h1 => ?_, fun h0 => ?_⟩
  · have z : ((rowNat tr 31 r 56 : Nat) : F) = 0 := by rw [h0]; rfl
    have a2 := f_sub_eq (f_mul_one_sub e2 z)
    have a4 := f_sub_eq (f_mul_one_sub e4 z)
    obtain ⟨-, -, b53, b54, b55, -⟩ := cuto_kinds H hr
    have b52 := (cuto_kinds H hr).2.1
    have k2 : ((rowNat tr 31 r 47 : Nat) : F) = ((2 * rowNat tr 31 r 52 + 4 * rowNat tr 31 r 53 +
        5 * rowNat tr 31 r 54 + 6 * rowNat tr 31 r 55 : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at a2 ⊢
      have := a2; grind
    exact ⟨natEq k2 (hN 47) (by omega), natEq a4 (hF 0 (by omega)) (hN 47)⟩
  · have z : ((rowNat tr 31 r 56 : Nat) : F) = 1 := by rw [h1]; rfl
    have a3 := f_mul_g e3 z
    grind
  · have z : ((rowNat tr 31 r 53 : Nat) : F) = 0 := by rw [h0]; rfl
    exact natEq (f_sub_eq (f_mul_one_sub e5 z)) (hF 1 (by omega)) (hN 48)
  · have z : ((rowNat tr 31 r 53 : Nat) : F) = 1 := by rw [h1]; rfl
    exact natEq (f_sub_eq (f_mul_g e6 z)) (hF 1 (by omega)) (hN 59)
  · have z : ((rowNat tr 31 r 53 : Nat) : F) = 0 := by rw [h0]; rfl
    exact natEq (f_sub_eq (f_mul_one_sub e7 z)) (hF 5 (by omega)) (hN 49)

/-- A nonzero CIDMAP multiplicity is on a `k4` row (`(1 − k4)·mm = 0`). -/
theorem cuto_mm {r : Nat} (hr : r < tr.height 31) (hm : rowNat tr 31 r 60 ≠ 0) : rowNat tr 31 r 53 = 1 := by
  obtain ⟨-, -, -, -, -, -, i53, -, -, -, -, -, -, i60, -⟩ := cuto_ix2
  have e := cuto_constr H hr (e := (1 - Cut.Out.c "k4") * Cut.Out.c "mm") (by simp [Cut.Out.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cuto_evalc tr pub r i53,
    cuto_evalc tr pub r i60] at e
  have hm' : ((rowNat tr 31 r 60 : Nat) : F) ≠ 0 := fun h0 => hm (natEq (R := 0) h0 (rowNat_lt tr 31 r 60) (by decide))
  have g : (1 : F) - ((rowNat tr 31 r 53 : Nat) : F) = 0 := by
    rcases mul_eq_zero' e with h | h
    · exact h
    · exact absurd h hm'
  rcases Nat.lt_or_eq_of_le (cuto_kinds H hr).2.2.1 with h | h
  · have h0 : rowNat tr 31 r 53 = 0 := by omega
    rw [h0] at g; exact absurd g (by decide)
  · exact h

end

/-! ## 2. CIDMAP (bus 14): only SEGB and CUTO, receive counts are bits, lookups resolve -/

set_option maxRecDepth 100000 in
/-- No table other than `SEGB` (0) and `CUTO` (31) has an interaction on bus 14. -/
theorem seg_cidm_tables (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 0 → t ≠ 31 →
      ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus ≠ 14 := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), t ≠ 0 → t ≠ 31 →
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => i.bus != 14) = true := by
    decide
  have h : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 0 → t ≠ 31 →
      ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != 14) = true := by
    simp only [e]; exact h0
  intro t ht h0' h31 i hi
  have := List.all_eq_true.mp (h t ht h0' h31) i hi
  simpa using this

set_option maxRecDepth 100000 in
theorem segb_cidm :
    Segb.table.inters.filter (fun i => i.bus = 14) =
      [⟨busCidm, false, .first, [Segb.c "cidf", pv pubCidOut]⟩, ⟨busCidm, true, Segb.c "m0", [0, 0]⟩] := by
  decide

set_option maxRecDepth 100000 in
theorem cuto_cidm :
    Cut.Out.table.inters.filter (fun i => i.bus = 14) =
      [⟨busCidm, false, Cut.Out.c "kL", [Cut.Out.c "space" - 16, Cut.Out.F 0 - 16]⟩,
       ⟨busCidm, false, Cut.Out.c "k4", [Cut.Out.c "x2", Cut.Out.F 5]⟩,
       ⟨busCidm, true, Cut.Out.c "mm", [Cut.Out.c "slot", Cut.Out.F 1]⟩] := by
  decide

theorem mem_filter14 {T : Table} {i : Inter} (hi : i ∈ T.inters) (hb : i.bus = 14) :
    i ∈ T.inters.filter (fun i => i.bus = 14) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩

theorem seg_t31' (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[31]'(by simp [seg_air_len]) = Cut.Out.table := rfl

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- Receive counts on bus 14 are bits. -/
theorem cidm_recv_bits :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = 14 → o.2.1 = false → o.2.2.2 ≤ 1 := by
  intro o ho hob hos
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hob hos ⊢
  by_cases h0 : t = 0
  · subst h0
    have hm := mem_filter14 hi hob
    rw [seg_t0, segb_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · simp only [Expr.eval]; split <;> decide
    · simp at hos
  by_cases h31 : t = 31
  · subst h31
    have hm := mem_filter14 hi hob
    rw [seg_t31', cuto_cidm] at hm
    obtain ⟨-, -, -, -, -, -, i53, -, -, i56, -⟩ := cuto_ix2
    obtain ⟨-, -, b53, -, -, b56, -⟩ := cuto_kinds H hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp only [cuto_evalc tr pub r i56, Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 56)]; exact b56
    · simp only [cuto_evalc tr pub r i53, Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 53)]; exact b53
    · simp at hos
  · exact absurd hob (seg_cidm_tables nloc ngl t ht h0 h31 i hi)

/-- **A CIDMAP query of a CUTO row is answered**: by SEGB's `0 ↦ 0`, or by an active `k4` row's
`slot ↦ F1`. -/
theorem cidm_provider {r : Nat} (hr : r < tr.height 31) {i : Inter}
    (hi : i ∈ Cut.Out.table.inters) (hb : i.bus = 14) (hs : i.send = false)
    (hc : (i.count.eval (tr.row pub 31 r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub 31 r)) = [0, 0] ∨
      ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
        i.msg.map (·.eval (tr.row pub 31 r)) =
          [((rowNat tr 31 r' 48 : Nat) : F), ((cutoF tr r' 1 : Nat) : F)] := by
  have ht31 : 31 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hocc := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr
    ⟨31, ht31, r, hr, i, by rw [seg_t31']; exact hi, rfl⟩
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_send H 14 (cidm_recv_bits H) hocc hb hs hc
  obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' hm' hc'
  by_cases h0 : t' = 0
  · subst h0
    have hm := mem_filter14 hi' hb'
    rw [seg_t0, segb_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · simp at hs'
    · left; rw [← hm']; simp; rfl
  by_cases h31 : t' = 31
  · subst h31
    have hm := mem_filter14 hi' hb'
    rw [seg_t31', cuto_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp at hs'
    · simp at hs'
    · right
      obtain ⟨-, i48, -, -, -, -, -, -, -, -, -, -, -, i60, -⟩ := cuto_ix2
      have hmm : rowNat tr 31 r' 60 ≠ 0 := by
        intro h0; simp only [cuto_evalc tr pub r' i60, h0] at hc'; exact hc' rfl
      have h53 := cuto_mm H hr' hmm
      have ha : rowNat tr 31 r' 0 = 1 := by
        have := (cuto_kinds H hr').2.2.2.2.2.2; have := (cuto_bits H hr').1; omega
      refine ⟨r', hr', h53, ha, ?_⟩
      rw [← hm']
      simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r' i48, cuto_evalF tr pub r' (show 1 < 7 by omega)]
  · exact absurd hb' (seg_cidm_tables nloc ngl t' ht' h0 h31 i' hi')

end

/-! ## 3. The two CIDMAP queries of an active CUTO row, resolved -/

/-- The activation id of a locals row (`space − 16`), as a natural: `clo + 2^13·u`, `u` the R16-checked
value of `8·chi`. -/
def cutoCL (tr : Trace) (r : Nat) : Nat :=
  rowNat tr 31 r 57 + 8192 * (((8 : Nat) : F) * ((rowNat tr 31 r 58 : Nat) : F)).toNat

theorem f_eq_add_of_sub {a b : F} {k : Nat} (h : a - ((k : Nat) : F) = b) : a = b + ((k : Nat) : F) := by grind

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **A locals row's query.**  On an active `kL` row the consumed space is `16 + cutoCL` (no wrap,
`cutoCL < 2^30`), and either the id is 0 and `F0 = 16` (SEGB's entry) or an active `k4` row has slot
`cutoCL` and `F0 = 16 + F1'`. -/
theorem cuto_kL_lookup (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (hL : rowNat tr 31 r 56 = 1) :
    rowNat tr 31 r 47 = 16 + cutoCL tr r ∧ cutoCL tr r < 2 ^ 30 ∧
      ((cutoCL tr r = 0 ∧ cutoF tr r 0 = 16) ∨
       ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
         rowNat tr 31 r' 48 = cutoCL tr r ∧ cutoF tr r 0 = 16 + cutoF tr r' 1) := by
  obtain ⟨i47, -, -, -, -, -, -, -, -, i56, i57, i58, -⟩ := cuto_ix2
  have hP := P_val
  have hc : ((Cut.Out.c "kL").eval (tr.row pub 31 r)).toNat = 1 := by
    rw [cuto_evalc tr pub r i56, hL]; rfl
  have l1 := cuto_inter H hr (e := Cut.Out.c "clo") (c := Cut.Out.c "kL") (by simp [Cut.Out.inters]) hc
  have l2 := cuto_inter H hr (e := 8 * Cut.Out.c "chi") (c := Cut.Out.c "kL") (by simp [Cut.Out.inters]) hc
  simp only [cuto_evalc tr pub r i57, Expr.eval_mul', Expr.eval_ofNat', cuto_evalc tr pub r i58,
    Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 57)] at l1 l2
  have hb := big_of_r16 ((rowNat tr 31 r 58 : Nat) : F) 3 (by omega)
  have hlt : cutoCL tr r < 2 ^ 30 := by
    unfold cutoCL; have : (((8 : Nat) : F) * ((rowNat tr 31 r 58 : Nat) : F)).toNat < 65536 := l2; omega
  have hsp := (cuto_fieldfacts H hl hr ha).2.1 hL
  rw [hb] at hsp
  have e47 : ((rowNat tr 31 r 47 : Nat) : F) = ((16 + cutoCL tr r : Nat) : F) := by
    rw [hsp]; unfold cutoCL
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    have : ((2 ^ (16 - 3) : Nat) : F) = ((8192 : Nat) : F) := rfl
    rw [this]; grind
  have h47 := natEq e47 (rowNat_lt tr 31 r 47) (by omega)
  refine ⟨h47, hlt, ?_⟩
  have hF0 := cutoF_lt H hl hr ha (k := 0) (by omega)
  have hmem : (⟨busCidm, false, Cut.Out.c "kL", [Cut.Out.c "space" - 16, Cut.Out.F 0 - 16]⟩ : Inter) ∈
      Cut.Out.table.inters := by simp [Cut.Out.table, Cut.Out.inters]
  rcases cidm_provider H hr hmem rfl rfl hc with h | ⟨r', hr', h53, ha', h⟩
  · simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_ofNat', cuto_evalc tr pub r i47,
      cuto_evalF tr pub r (show 0 < 7 by omega), List.cons.injEq, and_true] at h
    obtain ⟨a, b⟩ := h
    have a' := f_sub_eq a; have b' := f_sub_eq b
    left; constructor
    · have := natEq a' (rowNat_lt tr 31 r 47) (by decide); omega
    · exact natEq b' (by omega) (by decide)
  · simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_ofNat', cuto_evalc tr pub r i47,
      cuto_evalF tr pub r (show 0 < 7 by omega), List.cons.injEq, and_true] at h
    obtain ⟨a, b⟩ := h
    have hF1 := cutoF_lt H hl hr' ha' (k := 1) (by omega)
    right; refine ⟨r', hr', h53, ha', ?_, ?_⟩
    · have a' := f_eq_add_of_sub a
      rw [e47] at a'
      have : ((cutoCL tr r : Nat) : F) = ((rowNat tr 31 r' 48 : Nat) : F) := by
        simp only [Lean.Grind.Semiring.natCast_add] at a'; grind
      exact (natEq this (by omega) (rowNat_lt tr 31 r' 48)).symm
    · have b' := f_eq_add_of_sub b
      have : ((cutoF tr r 0 : Nat) : F) = ((16 + cutoF tr r' 1 : Nat) : F) := by
        rw [b']; simp only [Lean.Grind.Semiring.natCast_add]; grind
      exact natEq this (by omega) (by omega)

/-- **A record row's query.**  On an active `k4` row, either the caller id `x2` is 0 and `F5 = 0`
(SEGB's entry) or an active `k4` row has slot `x2` and `F5 = F1'`. -/
theorem cuto_k4_lookup (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (h4 : rowNat tr 31 r 53 = 1) :
    (rowNat tr 31 r 49 = 0 ∧ cutoF tr r 5 = 0) ∨
      ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
        rowNat tr 31 r' 48 = rowNat tr 31 r 49 ∧ cutoF tr r 5 = cutoF tr r' 1 := by
  obtain ⟨-, -, i49, -, -, -, i53, -⟩ := cuto_ix2
  have hP := P_val
  have hc : ((Cut.Out.c "k4").eval (tr.row pub 31 r)).toNat = 1 := by
    rw [cuto_evalc tr pub r i53, h4]; rfl
  have hF5 := cutoF_lt H hl hr ha (k := 5) (by omega)
  have hmem : (⟨busCidm, false, Cut.Out.c "k4", [Cut.Out.c "x2", Cut.Out.F 5]⟩ : Inter) ∈
      Cut.Out.table.inters := by simp [Cut.Out.table, Cut.Out.inters]
  rcases cidm_provider H hr hmem rfl rfl hc with h | ⟨r', hr', h53, ha', h⟩
  · simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r i49,
      cuto_evalF tr pub r (show 5 < 7 by omega), List.cons.injEq, and_true] at h
    left; exact ⟨natEq h.1 (rowNat_lt tr 31 r 49) (by decide), natEq h.2 (by omega) (by decide)⟩
  · simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r i49,
      cuto_evalF tr pub r (show 5 < 7 by omega), List.cons.injEq, and_true] at h
    have hF1 := cutoF_lt H hl hr' ha' (k := 1) (by omega)
    right; exact ⟨r', hr', h53, ha', (natEq h.1 (rowNat_lt tr 31 r 49) (rowNat_lt tr 31 r' 48)).symm,
      natEq h.2 (by omega) (by omega)⟩

end

/-! ## 4. The record rows: a contiguous block, slots increasing, `dep` = position -/

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- On an active row, `F0 = 4` exactly on record (`k4`) rows. -/
theorem cuto_F0_four (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    cutoF tr r 0 = 4 ↔ rowNat tr 31 r 53 = 1 := by
  obtain ⟨b51, b52, b53, b54, b55, b56, hs⟩ := cuto_kinds H hr
  rcases (by omega : rowNat tr 31 r 56 = 0 ∨ rowNat tr 31 r 56 = 1) with h0 | h1
  · obtain ⟨e1, e2⟩ := (cuto_fieldfacts H hl hr ha).1 h0
    rw [e2, e1]; omega
  · have h53 : rowNat tr 31 r 53 = 0 := by omega
    rw [h53]
    obtain ⟨-, -, h⟩ := cuto_kL_lookup H hl hr ha h1
    rcases h with ⟨-, e⟩ | ⟨r', -, -, -, -, e⟩ <;> omega

omit H in
theorem keyLt_F0 {r r' : Nat} (h : keyLt (cutoRow tr r) (cutoRow tr r')) :
    cutoF tr r 0 ≤ cutoF tr r' 0 := by
  simp only [keyLt, cutoRow, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega : 0 < 7), List.getElem?_range (by omega : 1 < 7), Option.map_some,
    Option.getD_some] at h
  omega

theorem cuto_act_of_k4 {x : Nat} (hx : x < tr.height 31) (h : rowNat tr 31 x 53 = 1) : rowNat tr 31 x 0 = 1 := by
  have := (cuto_kinds H hx).2.2.2.2.2.2; have := (cuto_bits H hx).1; omega

/-- Rows before an active row are active. -/
theorem cuto_prefix_le {m b : Nat} (hb : b < tr.height 31) (hmb : m ≤ b) (hbA : rowNat tr 31 b 0 = 1) :
    rowNat tr 31 m 0 = 1 := by
  have key : ∀ d m, m + d = b → rowNat tr 31 m 0 = 1 := by
    intro d
    induction d with
    | zero => intro m e; rw [show m = b by omega]; exact hbA
    | succ d ih =>
      intro m e
      exact cuto_prefix H (r := m) (by omega) (ih (m + 1) (by omega))
  exact key (b - m) m (by omega)

/-- **The record rows are contiguous**: a row between two `k4` rows is a `k4` row. -/
theorem cuto_k4_between (hl : CutoHiLimbs tr) {a m b : Nat} (hb : b < tr.height 31) (ham : a < m) (hmb : m < b)
    (ha4 : rowNat tr 31 a 53 = 1) (hb4 : rowNat tr 31 b 53 = 1) : rowNat tr 31 m 53 = 1 := by
  have hbA := cuto_act_of_k4 H hb hb4
  have hmA := cuto_prefix_le H hb (Nat.le_of_lt hmb) hbA
  have haA := cuto_act_of_k4 H (by omega) ha4
  have o1 := keyLt_F0 (cuto_order H hl (m - a - 1) a (by omega) (by rw [show a + (m - a - 1) + 1 = m by omega]; exact hmA))
  have o2 := keyLt_F0 (cuto_order H hl (b - m - 1) m (by omega) (by rw [show m + (b - m - 1) + 1 = b by omega]; exact hbA))
  rw [show a + (m - a - 1) + 1 = m by omega] at o1
  rw [show m + (b - m - 1) + 1 = b by omega] at o2
  have fa := (cuto_F0_four H hl (by omega) haA).mpr ha4
  have fb := (cuto_F0_four H hl hb hbA).mpr hb4
  exact (cuto_F0_four H hl (by omega) hmA).mp (by omega)

/-- Consecutive `k4` rows have increasing slots (CUTO's record-order constraint), for slots `< 2^30`. -/
theorem cuto_k4_step {r : Nat} (hr : r + 1 < tr.height 31) (ha : rowNat tr 31 r 53 = 1)
    (hb : rowNat tr 31 (r + 1) 53 = 1) (hs : rowNat tr 31 r 48 < 2 ^ 30) (hs' : rowNat tr 31 (r + 1) 48 < 2 ^ 30) :
    rowNat tr 31 r 48 < rowNat tr 31 (r + 1) 48 := by
  obtain ⟨-, i48, -, -, -, -, i53, -, -, -, -, -, -, -, i64, i65⟩ := cuto_ix2
  have hr' : r < tr.height 31 := by omega
  have e := cuto_constr H hr' (e := Cut.Out.c "k4" * Cut.Out.n "k4" * (Cut.Out.n "slot" - Cut.Out.c "slot" - 1 -
    Cut.Out.c "rlo" - 65536 * Cut.Out.c "rhi")) (by simp [Cut.Out.constraints])
  have hc : ((Cut.Out.c "k4" * Cut.Out.n "k4").eval (tr.row pub 31 r)).toNat = 1 := by
    simp only [Cut.Out.c, Cut.Out.n, Cut.c, Cut.n, i53, v, nv, Expr.eval_mul', Expr.eval_col, Expr.eval_nxt,
      row_cur, row_nxt tr pub hr, ha, hb]; rfl
  have l1 := cuto_inter H hr' (e := Cut.Out.c "rlo") (c := Cut.Out.c "k4" * Cut.Out.n "k4")
    (by simp [Cut.Out.inters]) hc
  have l2 := cuto_inter H hr' (e := 16 * Cut.Out.c "rhi") (c := Cut.Out.c "k4" * Cut.Out.n "k4")
    (by simp [Cut.Out.inters]) hc
  simp only [Cut.Out.c, Cut.Out.n, Cut.c, Cut.n, i48, i53, i64, i65, v, nv, Expr.eval_mul', Expr.eval_sub',
    Expr.eval_col, Expr.eval_nxt, Expr.eval_ofNat', row_cur, row_nxt tr pub hr, ha, hb,
    Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 64)] at e l1 l2
  have one1 : ((1 : Nat) : F) * ((1 : Nat) : F) = 1 := by decide
  rw [one1] at e
  have e' : ((rowNat tr 31 (r + 1) 48 : Nat) : F) - ((rowNat tr 31 r 48 : Nat) : F) - 1 -
      ((rowNat tr 31 r 64 : Nat) : F) - ((65536 : Nat) : F) * ((rowNat tr 31 r 65 : Nat) : F) = 0 := by
    have : ((1 : Nat) : F) = 1 := rfl
    grind
  exact cut_rec_order hs hs' l1 l2 e'

/-- **Slots increase along the record rows** (given every record row's slot is `< 2^30`). -/
theorem cuto_k4_mono (hl : CutoHiLimbs tr)
    (hsl : ∀ x, x < tr.height 31 → rowNat tr 31 x 53 = 1 → rowNat tr 31 x 48 < 2 ^ 30) :
    ∀ d a, a + d + 1 < tr.height 31 → rowNat tr 31 a 53 = 1 → rowNat tr 31 (a + d + 1) 53 = 1 →
      rowNat tr 31 a 48 < rowNat tr 31 (a + d + 1) 48
  | 0, a, hb, ha, hb4 => cuto_k4_step H hb ha hb4 (hsl a (by omega) ha) (hsl _ hb hb4)
  | d + 1, a, hb, ha, hb4 => by
    have hm : rowNat tr 31 (a + d + 1) 53 = 1 :=
      cuto_k4_between H hl (a := a) (m := a + d + 1) (b := a + (d + 1) + 1) hb (by omega) (by omega) ha hb4
    have h1 := cuto_k4_mono hl hsl d a (by omega) ha hm
    have h2 := cuto_k4_step H (r := a + d + 1) (by omega) hm (by simpa [Nat.add_assoc] using hb4)
      (hsl _ (by omega) hm) (hsl _ (by omega) (by simpa [Nat.add_assoc] using hb4))
    rw [show a + (d + 1) + 1 = a + d + 1 + 1 by omega]; omega

end

/-! ## 5. List lemmas: counting a filtered range -/

theorem sum_map_bits {g : Nat → Nat} : ∀ l : List Nat, (∀ x ∈ l, g x ≤ 1) →
    (l.map g).sum = (l.filter (fun x => g x = 1)).length
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x List.mem_cons_self
    have ih := sum_map_bits l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rcases (by omega : g x = 0 ∨ g x = 1) with h0 | h1
    · simp [h0, ih]
    · simp [h1, ih]; omega

/-- The `j`-th element `r` of a filtered range has exactly `j + 1` filtered elements `≤ r`. -/
theorem filter_range_idx (p : Nat → Bool) (h j : Nat) (hj : j < ((List.range h).filter p).length) :
    ((List.range (((List.range h).filter p)[j] + 1)).filter p).length = j + 1 := by
  generalize hr : ((List.range h).filter p)[j] = r
  have hmem : r ∈ (List.range h).filter p := by rw [← hr]; exact List.getElem_mem hj
  have hrh : r < h := List.mem_range.mp (List.mem_filter.mp hmem).1
  have hpr : p r = true := (List.mem_filter.mp hmem).2
  have e1 : List.range h = List.range r ++ r :: (List.range (h - (r + 1))).map ((r + 1) + ·) := by
    have eh : h = (r + 1) + (h - (r + 1)) := by omega
    have ra := @List.range_add (r + 1) (h - (r + 1))
    rw [← eh] at ra
    rw [ra, List.range_succ]
    simp only [List.append_assoc, List.singleton_append]
  have hK : (List.range h).filter p =
      (List.range r).filter p ++ r :: ((List.range (h - (r + 1))).map ((r + 1) + ·)).filter p := by
    rw [e1, List.filter_append, List.filter_cons, hpr]; rfl
  have hnd : ((List.range h).filter p).Nodup := List.nodup_range.filter _
  have hidx : ((List.range h).filter p).idxOf r = ((List.range r).filter p).length := by
    have hn : r ∉ (List.range r).filter p := by
      intro hm; have := List.mem_range.mp (List.mem_filter.mp hm).1; omega
    rw [hK, List.idxOf_append, ite_eq_right_iff.mpr (fun h => absurd h hn), List.idxOf_cons_self]; simp
  have hj' : ((List.range h).filter p).idxOf r = j := by
    rw [← hr]; exact List.Nodup.idxOf_getElem hnd j hj
  rw [List.range_succ, List.filter_append, List.filter_cons, hpr]
  simp only [List.filter_nil, List.length_append, List.length_cons, List.length_nil]
  simp only [ite_true, List.length_singleton]
  omega

/-! ## 6. The consumed message of a CUTO row; `dep` is the depth -/

/-- The CH message an active CUTO row consumes (its first interaction), decoded. -/
def cutoMsg (tr : Trace) (pub : List F) (r : Nat) : Msg :=
  decMsg ([Cut.Out.c "space", Cut.Out.c "slot", Cut.Out.F 2, Cut.Out.F 3, Cut.Out.F 4, Cut.Out.c "x2",
    Cut.Out.F 6, Cut.Out.c "tp"].map (·.eval (tr.row pub 31 r)))

/-- `cutoMsg` is the decoded message of CUTO's channel receive. -/
theorem cutoMsg_recv (tr : Trace) (pub : List F) (r : Nat) :
    cutoMsg tr pub r = decMsg ((chRecv (Cut.Out.c "space") (Cut.Out.c "slot") (Cut.Out.F 2)
      [Cut.Out.F 3, Cut.Out.F 4, Cut.Out.c "x2", Cut.Out.F 6] (Cut.Out.c "tp") (Cut.Out.c "act")).msg.map
        (·.eval (tr.row pub 31 r))) := rfl

theorem cutoMsg_head : Cut.Out.inters.head? = some (chRecv (Cut.Out.c "space") (Cut.Out.c "slot") (Cut.Out.F 2)
      [Cut.Out.F 3, Cut.Out.F 4, Cut.Out.c "x2", Cut.Out.F 6] (Cut.Out.c "tp") (Cut.Out.c "act")) := rfl

/-- **How the final live list meets CUTO** (the bus-split facts the link uses): every active CUTO row's
consumed message is in the final live list, and every live call record (space 4) is consumed by an
active CUTO row. -/
structure CutoFin (tr : Trace) (pub : List F) (fin : List Msg) : Prop where
  mem : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → cutoMsg tr pub r ∈ fin
  cov4 : ∀ x ∈ fin, x.space = 4 → ∃ r, r < tr.height 31 ∧ rowNat tr 31 r 0 = 1 ∧ x = cutoMsg tr pub r

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- The fields of an active row's consumed message. -/
theorem cutoMsg_fields (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    (cutoMsg tr pub r).space = rowNat tr 31 r 47 ∧ (cutoMsg tr pub r).slot = rowNat tr 31 r 48 ∧
      (cutoMsg tr pub r).tag = cutoF tr r 2 ∧ (cutoMsg tr pub r).l0 = cutoF tr r 3 ∧
      (cutoMsg tr pub r).l1 = cutoF tr r 4 ∧ (cutoMsg tr pub r).l2 = rowNat tr 31 r 49 ∧
      (cutoMsg tr pub r).l3 = cutoF tr r 6 := by
  obtain ⟨i47, i48, i49, -⟩ := cuto_ix2
  have hP := P_val
  have hF := fun k (hk : k < 7) => cutoF_lt H hl hr ha hk
  have t2 : (((cutoF tr r 2 : Nat) : F)).toNat = cutoF tr r 2 := Fp.toNat_cast_of_lt (by have := hF 2 (by omega); omega)
  have t3 : (((cutoF tr r 3 : Nat) : F)).toNat = cutoF tr r 3 := Fp.toNat_cast_of_lt (by have := hF 3 (by omega); omega)
  have t4 : (((cutoF tr r 4 : Nat) : F)).toNat = cutoF tr r 4 := Fp.toNat_cast_of_lt (by have := hF 4 (by omega); omega)
  have t6 : (((cutoF tr r 6 : Nat) : F)).toNat = cutoF tr r 6 := Fp.toNat_cast_of_lt (by have := hF 6 (by omega); omega)
  simp only [t2, t3, t4, t6, cutoMsg, decMsg, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    cuto_evalc tr pub r i47, cuto_evalc tr pub r i48, cuto_evalc tr pub r i49,
    cuto_evalF tr pub r (show 2 < 7 by omega), cuto_evalF tr pub r (show 3 < 7 by omega),
    cuto_evalF tr pub r (show 4 < 7 by omega), cuto_evalF tr pub r (show 6 < 7 by omega),
    Fp.toNat_cast_of_lt (rowNat_lt tr 31 r _), t2, t3, t4, t6, and_self]

/-- An active row consumes a call record (space 4) exactly when it is a `k4` row. -/
theorem cutoMsg_space4 (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    (cutoMsg tr pub r).space = 4 ↔ rowNat tr 31 r 53 = 1 := by
  rw [(cutoMsg_fields H hl hr ha).1]
  obtain ⟨b51, b52, b53, b54, b55, b56, hs⟩ := cuto_kinds H hr
  rcases (by omega : rowNat tr 31 r 56 = 0 ∨ rowNat tr 31 r 56 = 1) with h0 | h1
  · rw [((cuto_fieldfacts H hl hr ha).1 h0).1]; omega
  · rw [(cuto_kL_lookup H hl hr ha h1).1]; omega

theorem cuto_dep_count {r : Nat} (hr : r < tr.height 31) :
    rowNat tr 31 r 59 = ((List.range (r + 1)).filter (fun x => decide (rowNat tr 31 x 53 = 1))).length := by
  rw [cuto_dep H r hr, sum_map_bits (List.range (r + 1)) (fun x hx => by
    have := List.mem_range.mp hx; exact (cuto_kinds H (by omega)).2.2.1)]

/-- **`dep` is the depth.**  Given the id facts of the final live list (`IdsOK`, spec side) and how it
meets CUTO (`CutoFin`), every record row's slot is a live id `I[i]` whose caller is `I[i+1]`, and its
`dep` is `σ` of the slot. -/
theorem cuto_k4_dep (hl : CutoHiLimbs tr) {fin : List Msg} {I : List Nat} {σ : Nat → Nat}
    (hI : IdsOK fin I σ) (hF : CutoFin tr pub fin) {r : Nat} (hr : r < tr.height 31)
    (h4 : rowNat tr 31 r 53 = 1) :
    rowNat tr 31 r 59 = σ (rowNat tr 31 r 48) ∧
      ∃ i, ∃ hi : i + 1 < I.length, rowNat tr 31 r 48 = I[i] ∧ rowNat tr 31 r 49 = I[i + 1] := by
  -- every record row's slot and caller are ids
  have slotI : ∀ x, x < tr.height 31 → rowNat tr 31 x 53 = 1 →
      ∃ i, ∃ hi : i + 1 < I.length, rowNat tr 31 x 48 = I[i] ∧ rowNat tr 31 x 49 = I[i + 1] := by
    intro x hx h4x
    have hax := cuto_act_of_k4 H hx h4x
    obtain ⟨f1, f2, -, -, -, f6, -⟩ := cutoMsg_fields H hl hx hax
    obtain ⟨i, hi, e1, e2⟩ := hI.recs _ (hF.mem x hx hax) ((cutoMsg_space4 H hl hx hax).mpr h4x)
    exact ⟨i, hi, by rw [← f2, e1], by rw [← f6, e2]⟩
  have hsl : ∀ x, x < tr.height 31 → rowNat tr 31 x 53 = 1 → rowNat tr 31 x 48 < 2 ^ 30 := by
    intro x hx h4x
    obtain ⟨i, hi, e1, -⟩ := slotI x hx h4x
    have := hI.lt _ (List.getElem_mem (by omega : i < I.length)); omega
  let p : Nat → Bool := fun x => decide (rowNat tr 31 x 53 = 1)
  let K := (List.range (tr.height 31)).filter p
  let S := K.map (fun x => rowNat tr 31 x 48)
  let R := (I.take (I.length - 1)).reverse
  have hK : K.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hS : S.Pairwise (· < ·) := by
    refine List.pairwise_map.mpr (hK.imp_of_mem fun {a b} ha hb hab => ?_)
    obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
    obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
    have := cuto_k4_mono H hl hsl (b - a - 1) a (by have := List.mem_range.mp hb1; omega) (by simpa [p] using ha2)
      (by rw [show a + (b - a - 1) + 1 = b by omega]; simpa [p] using hb2)
    rwa [show a + (b - a - 1) + 1 = b by omega] at this
  have hR : R.Pairwise (· < ·) :=
    List.pairwise_reverse.mpr ((hI.desc.sublist (List.take_sublist _ _)).imp fun h => h)
  have memR : ∀ y, y ∈ R ↔ ∃ i, ∃ hi : i + 1 < I.length, I[i] = y := by
    intro y
    rw [List.mem_reverse, List.mem_iff_getElem]
    simp only [List.length_take, List.getElem_take]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  have hSR : S = R := by
    refine pairwise_eq_of_mem_iff (· < ·) (fun a b h h' => by omega) S R hS hR fun y => ?_
    rw [memR]
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      obtain ⟨i, hi, e1, -⟩ := slotI x (List.mem_range.mp hx1) (by simpa [p] using hx2)
      exact ⟨i, hi, e1.symm⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨x, hx, hx4, hxs⟩ := hI.recEx i hi
      obtain ⟨r', hr', ha', rfl⟩ := hF.cov4 x hx hx4
      have h4' := (cutoMsg_space4 H hl hr' ha').mp hx4
      refine List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨List.mem_range.mpr hr', by simpa [p] using h4'⟩, ?_⟩
      rw [← (cutoMsg_fields H hl hr' ha').2.1, hxs]
  -- `r` is the `j`-th record row
  have hrK : r ∈ K := List.mem_filter.mpr ⟨List.mem_range.mpr hr, by simpa [p] using h4⟩
  obtain ⟨j, hj, hKj⟩ := List.mem_iff_getElem.mp hrK
  have hdep : rowNat tr 31 r 59 = j + 1 := by
    rw [cuto_dep_count H hr, ← hKj]; exact filter_range_idx p _ j hj
  have hjS : j < S.length := by simp [S]; exact hj
  have hSj : S[j] = rowNat tr 31 r 48 := by simp only [S, List.getElem_map, hKj]
  have hlenR : R.length = I.length - 1 := by simp [R]
  have hjR : j < R.length := by rw [← hSR]; exact hjS
  have hRj : R[j] = I[I.length - 2 - j]'(by omega) := by
    simp only [R, List.getElem_reverse, List.getElem_take, List.length_take]
    congr 1; omega
  obtain ⟨i, hi, e1, e2⟩ := slotI r hr h4
  have hnd : I.Nodup := hI.desc.imp fun h => Nat.ne_of_gt h
  have hii : i = I.length - 2 - j := by
    have : I[i] = I[I.length - 2 - j]'(by omega) := by
      rw [← e1, ← hRj, ← hSj]; simp only [hSR]
    exact (List.Nodup.getElem_inj hnd).mp this
  refine ⟨?_, i, hi, e1, e2⟩
  rw [e1, hI.dep i (by omega), hdep]; omega

end

end WasmBase
