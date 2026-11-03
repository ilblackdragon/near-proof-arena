import WasmBase.Main.SegLink
import WasmBase.Main.SegS.SegCuto
/-!
# WasmBase.Main.SegS.SegLink — `SegLink`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegLink.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- A boolean column of CUTO is 0 or 1. -/
theorem cuto_boolcS {r : Nat} (hr : r < tr.height 31) {s : String} {i : Nat} (hi : ix Cut.Out.cols s = i)
    (hm : bool (Cut.Out.c s) ∈ Cut.Out.constraints) : rowNat tr 31 r i = 0 ∨ rowNat tr 31 r i = 1 := by
  have e := cuto_constrS H hr hm
  simp only [Chips.bool, Cut.Out.c, Cut.c, hi, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', row_cur] at e
  exact bool_nat (rowNat_lt tr 31 r i) e

/-- The kind flags of a CUTO row: bits, and on an active row exactly one is set. -/
theorem cuto_kindsS {r : Nat} (hr : r < tr.height 31) :
    rowNat tr 31 r 51 ≤ 1 ∧ rowNat tr 31 r 52 ≤ 1 ∧ rowNat tr 31 r 53 ≤ 1 ∧ rowNat tr 31 r 54 ≤ 1 ∧
      rowNat tr 31 r 55 ≤ 1 ∧ rowNat tr 31 r 56 ≤ 1 ∧
      rowNat tr 31 r 51 + rowNat tr 31 r 52 + rowNat tr 31 r 53 + rowNat tr 31 r 54 + rowNat tr 31 r 55 +
        rowNat tr 31 r 56 = rowNat tr 31 r 0 := by
  obtain ⟨-, -, -, -, i51, i52, i53, i54, i55, i56, -⟩ := cuto_ix2
  have b51 := cuto_boolcS H hr i51 (by simp [Cut.Out.constraints])
  have b52 := cuto_boolcS H hr i52 (by simp [Cut.Out.constraints])
  have b53 := cuto_boolcS H hr i53 (by simp [Cut.Out.constraints])
  have b54 := cuto_boolcS H hr i54 (by simp [Cut.Out.constraints])
  have b55 := cuto_boolcS H hr i55 (by simp [Cut.Out.constraints])
  have b56 := cuto_boolcS H hr i56 (by simp [Cut.Out.constraints])
  obtain ⟨ba, -⟩ := cuto_bitsS H hr
  have e := cuto_constrS H hr (e := Cut.Out.c "k0" + Cut.Out.c "k2" + Cut.Out.c "k4" + Cut.Out.c "k5" +
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

/-- **The field facts of an active CUTO row** (with the chip limb bound): its kind decides the
consumed space and how the hashed fields `F0, F1, F5` come from the raw columns. -/
theorem cuto_fieldfactsS (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    (rowNat tr 31 r 56 = 0 → rowNat tr 31 r 47 = 2 * rowNat tr 31 r 52 + 4 * rowNat tr 31 r 53 +
        5 * rowNat tr 31 r 54 + 6 * rowNat tr 31 r 55 ∧ cutoF tr r 0 = rowNat tr 31 r 47) ∧
    (rowNat tr 31 r 56 = 1 → ((rowNat tr 31 r 47 : Nat) : F) =
        16 + ((rowNat tr 31 r 57 : Nat) : F) + ((65536 : Nat) : F) * ((rowNat tr 31 r 58 : Nat) : F)) ∧
    (rowNat tr 31 r 53 = 0 → cutoF tr r 1 = rowNat tr 31 r 48) ∧
    (rowNat tr 31 r 53 = 1 → cutoF tr r 1 = rowNat tr 31 r 59) ∧
    (rowNat tr 31 r 53 = 0 → cutoF tr r 5 = rowNat tr 31 r 49) := by
  obtain ⟨i47, i48, i49, -, -, i52, i53, i54, i55, i56, i57, i58, i59, -⟩ := cuto_ix2
  have hP := P_val
  have hF : ∀ k, k < 7 → cutoF tr r k < P := fun k hk => by have := cutoF_ltS H hl hr ha hk; omega
  have hN := rowNat_lt tr 31 r
  have C := fun e he => cuto_constrS H hr (e := e) he
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
    obtain ⟨-, -, b53, b54, b55, -⟩ := cuto_kindsS H hr
    have b52 := (cuto_kindsS H hr).2.1
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
theorem cuto_mmS {r : Nat} (hr : r < tr.height 31) (hm : rowNat tr 31 r 60 ≠ 0) : rowNat tr 31 r 53 = 1 := by
  obtain ⟨-, -, -, -, -, -, i53, -, -, -, -, -, -, i60, -⟩ := cuto_ix2
  have e := cuto_constrS H hr (e := (1 - Cut.Out.c "k4") * Cut.Out.c "mm") (by simp [Cut.Out.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cuto_evalc tr pub r i53,
    cuto_evalc tr pub r i60] at e
  have hm' : ((rowNat tr 31 r 60 : Nat) : F) ≠ 0 := fun h0 => hm (natEq (R := 0) h0 (rowNat_lt tr 31 r 60) (by decide))
  have g : (1 : F) - ((rowNat tr 31 r 53 : Nat) : F) = 0 := by
    rcases mul_eq_zero' e with h | h
    · exact h
    · exact absurd h hm'
  rcases Nat.lt_or_eq_of_le (cuto_kindsS H hr).2.2.1 with h | h
  · have h0 : rowNat tr 31 r 53 = 0 := by omega
    rw [h0] at g; exact absurd g (by decide)
  · exact h

/-- Receive counts on bus 14 are bits. -/
theorem cidm_recv_bitsS :
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
    obtain ⟨-, -, b53, -, -, b56, -⟩ := cuto_kindsS H hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp only [cuto_evalc tr pub r i56, Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 56)]; exact b56
    · simp only [cuto_evalc tr pub r i53, Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 53)]; exact b53
    · simp at hos
  · exact absurd hob (seg_cidm_tables nloc ngl t ht h0 h31 i hi)

/-- **A CIDMAP query of a CUTO row is answered**: by SEGB's `0 ↦ 0`, or by an active `k4` row's
`slot ↦ F1`. -/
theorem cidm_providerS {r : Nat} (hr : r < tr.height 31) {i : Inter}
    (hi : i ∈ Cut.Out.table.inters) (hb : i.bus = 14) (hs : i.send = false)
    (hc : (i.count.eval (tr.row pub 31 r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub 31 r)) = [0, 0] ∨
      ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
        i.msg.map (·.eval (tr.row pub 31 r)) =
          [((rowNat tr 31 r' 48 : Nat) : F), ((cutoF tr r' 1 : Nat) : F)] := by
  have ht31 : 31 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hocc := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr
    ⟨31, ht31, r, hr, i, by rw [seg_t31']; exact hi, rfl⟩
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_sendS H 14 (cidm_recv_bitsS H) hocc hb hs hc
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
      have h53 := cuto_mmS H hr' hmm
      have ha : rowNat tr 31 r' 0 = 1 := by
        have := (cuto_kindsS H hr').2.2.2.2.2.2; have := (cuto_bitsS H hr').1; omega
      refine ⟨r', hr', h53, ha, ?_⟩
      rw [← hm']
      simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r' i48, cuto_evalF tr pub r' (show 1 < 7 by omega)]
  · exact absurd hb' (seg_cidm_tables nloc ngl t' ht' h0 h31 i' hi')

/-- **A locals row's query.**  On an active `kL` row the consumed space is `16 + cutoCL` (no wrap,
`cutoCL < 2^30`), and either the id is 0 and `F0 = 16` (SEGB's entry) or an active `k4` row has slot
`cutoCL` and `F0 = 16 + F1'`. -/
theorem cuto_kL_lookupS (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (hL : rowNat tr 31 r 56 = 1) :
    rowNat tr 31 r 47 = 16 + cutoCL tr r ∧ cutoCL tr r < 2 ^ 30 ∧
      ((cutoCL tr r = 0 ∧ cutoF tr r 0 = 16) ∨
       ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
         rowNat tr 31 r' 48 = cutoCL tr r ∧ cutoF tr r 0 = 16 + cutoF tr r' 1) := by
  obtain ⟨i47, -, -, -, -, -, -, -, -, i56, i57, i58, -⟩ := cuto_ix2
  have hP := P_val
  have hc : ((Cut.Out.c "kL").eval (tr.row pub 31 r)).toNat = 1 := by
    rw [cuto_evalc tr pub r i56, hL]; rfl
  have l1 := cuto_interS H hr (e := Cut.Out.c "clo") (c := Cut.Out.c "kL") (by simp [Cut.Out.inters]) hc
  have l2 := cuto_interS H hr (e := 8 * Cut.Out.c "chi") (c := Cut.Out.c "kL") (by simp [Cut.Out.inters]) hc
  simp only [cuto_evalc tr pub r i57, Expr.eval_mul', Expr.eval_ofNat', cuto_evalc tr pub r i58,
    Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 57)] at l1 l2
  have hb := big_of_r16 ((rowNat tr 31 r 58 : Nat) : F) 3 (by omega)
  have hlt : cutoCL tr r < 2 ^ 30 := by
    unfold cutoCL; have : (((8 : Nat) : F) * ((rowNat tr 31 r 58 : Nat) : F)).toNat < 65536 := l2; omega
  have hsp := (cuto_fieldfactsS H hl hr ha).2.1 hL
  rw [hb] at hsp
  have e47 : ((rowNat tr 31 r 47 : Nat) : F) = ((16 + cutoCL tr r : Nat) : F) := by
    rw [hsp]; unfold cutoCL
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    have : ((2 ^ (16 - 3) : Nat) : F) = ((8192 : Nat) : F) := rfl
    rw [this]; grind
  have h47 := natEq e47 (rowNat_lt tr 31 r 47) (by omega)
  refine ⟨h47, hlt, ?_⟩
  have hF0 := cutoF_ltS H hl hr ha (k := 0) (by omega)
  have hmem : (⟨busCidm, false, Cut.Out.c "kL", [Cut.Out.c "space" - 16, Cut.Out.F 0 - 16]⟩ : Inter) ∈
      Cut.Out.table.inters := by simp [Cut.Out.table, Cut.Out.inters]
  rcases cidm_providerS H hr hmem rfl rfl hc with h | ⟨r', hr', h53, ha', h⟩
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
    have hF1 := cutoF_ltS H hl hr' ha' (k := 1) (by omega)
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
theorem cuto_k4_lookupS (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (h4 : rowNat tr 31 r 53 = 1) :
    (rowNat tr 31 r 49 = 0 ∧ cutoF tr r 5 = 0) ∨
      ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
        rowNat tr 31 r' 48 = rowNat tr 31 r 49 ∧ cutoF tr r 5 = cutoF tr r' 1 := by
  obtain ⟨-, -, i49, -, -, -, i53, -⟩ := cuto_ix2
  have hP := P_val
  have hc : ((Cut.Out.c "k4").eval (tr.row pub 31 r)).toNat = 1 := by
    rw [cuto_evalc tr pub r i53, h4]; rfl
  have hF5 := cutoF_ltS H hl hr ha (k := 5) (by omega)
  have hmem : (⟨busCidm, false, Cut.Out.c "k4", [Cut.Out.c "x2", Cut.Out.F 5]⟩ : Inter) ∈
      Cut.Out.table.inters := by simp [Cut.Out.table, Cut.Out.inters]
  rcases cidm_providerS H hr hmem rfl rfl hc with h | ⟨r', hr', h53, ha', h⟩
  · simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r i49,
      cuto_evalF tr pub r (show 5 < 7 by omega), List.cons.injEq, and_true] at h
    left; exact ⟨natEq h.1 (rowNat_lt tr 31 r 49) (by decide), natEq h.2 (by omega) (by decide)⟩
  · simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r i49,
      cuto_evalF tr pub r (show 5 < 7 by omega), List.cons.injEq, and_true] at h
    have hF1 := cutoF_ltS H hl hr' ha' (k := 1) (by omega)
    right; exact ⟨r', hr', h53, ha', (natEq h.1 (rowNat_lt tr 31 r 49) (rowNat_lt tr 31 r' 48)).symm,
      natEq h.2 (by omega) (by omega)⟩

/-- On an active row, `F0 = 4` exactly on record (`k4`) rows. -/
theorem cuto_F0_fourS (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    cutoF tr r 0 = 4 ↔ rowNat tr 31 r 53 = 1 := by
  obtain ⟨b51, b52, b53, b54, b55, b56, hs⟩ := cuto_kindsS H hr
  rcases (by omega : rowNat tr 31 r 56 = 0 ∨ rowNat tr 31 r 56 = 1) with h0 | h1
  · obtain ⟨e1, e2⟩ := (cuto_fieldfactsS H hl hr ha).1 h0
    rw [e2, e1]; omega
  · have h53 : rowNat tr 31 r 53 = 0 := by omega
    rw [h53]
    obtain ⟨-, -, h⟩ := cuto_kL_lookupS H hl hr ha h1
    rcases h with ⟨-, e⟩ | ⟨r', -, -, -, -, e⟩ <;> omega

theorem cuto_act_of_k4S {x : Nat} (hx : x < tr.height 31) (h : rowNat tr 31 x 53 = 1) : rowNat tr 31 x 0 = 1 := by
  have := (cuto_kindsS H hx).2.2.2.2.2.2; have := (cuto_bitsS H hx).1; omega

/-- Rows before an active row are active. -/
theorem cuto_prefix_leS {m b : Nat} (hb : b < tr.height 31) (hmb : m ≤ b) (hbA : rowNat tr 31 b 0 = 1) :
    rowNat tr 31 m 0 = 1 := by
  have key : ∀ d m, m + d = b → rowNat tr 31 m 0 = 1 := by
    intro d
    induction d with
    | zero => intro m e; rw [show m = b by omega]; exact hbA
    | succ d ih =>
      intro m e
      exact cuto_prefixS H (r := m) (by omega) (ih (m + 1) (by omega))
  exact key (b - m) m (by omega)

/-- **The record rows are contiguous**: a row between two `k4` rows is a `k4` row. -/
theorem cuto_k4_betweenS (hl : CutoHiLimbs tr) {a m b : Nat} (hb : b < tr.height 31) (ham : a < m) (hmb : m < b)
    (ha4 : rowNat tr 31 a 53 = 1) (hb4 : rowNat tr 31 b 53 = 1) : rowNat tr 31 m 53 = 1 := by
  have hbA := cuto_act_of_k4S H hb hb4
  have hmA := cuto_prefix_leS H hb (Nat.le_of_lt hmb) hbA
  have haA := cuto_act_of_k4S H (by omega) ha4
  have o1 := keyLt_F0 (cuto_orderS H hl (m - a - 1) a (by omega) (by rw [show a + (m - a - 1) + 1 = m by omega]; exact hmA))
  have o2 := keyLt_F0 (cuto_orderS H hl (b - m - 1) m (by omega) (by rw [show m + (b - m - 1) + 1 = b by omega]; exact hbA))
  rw [show a + (m - a - 1) + 1 = m by omega] at o1
  rw [show m + (b - m - 1) + 1 = b by omega] at o2
  have fa := (cuto_F0_fourS H hl (by omega) haA).mpr ha4
  have fb := (cuto_F0_fourS H hl hb hbA).mpr hb4
  exact (cuto_F0_fourS H hl (by omega) hmA).mp (by omega)

/-- Consecutive `k4` rows have increasing slots (CUTO's record-order constraint), for slots `< 2^30`. -/
theorem cuto_k4_stepS {r : Nat} (hr : r + 1 < tr.height 31) (ha : rowNat tr 31 r 53 = 1)
    (hb : rowNat tr 31 (r + 1) 53 = 1) (hs : rowNat tr 31 r 48 < 2 ^ 30) (hs' : rowNat tr 31 (r + 1) 48 < 2 ^ 30) :
    rowNat tr 31 r 48 < rowNat tr 31 (r + 1) 48 := by
  obtain ⟨-, i48, -, -, -, -, i53, -, -, -, -, -, -, -, i64, i65⟩ := cuto_ix2
  have hr' : r < tr.height 31 := by omega
  have e := cuto_constrS H hr' (e := Cut.Out.c "k4" * Cut.Out.n "k4" * (Cut.Out.n "slot" - Cut.Out.c "slot" - 1 -
    Cut.Out.c "rlo" - 65536 * Cut.Out.c "rhi")) (by simp [Cut.Out.constraints])
  have hc : ((Cut.Out.c "k4" * Cut.Out.n "k4").eval (tr.row pub 31 r)).toNat = 1 := by
    simp only [Cut.Out.c, Cut.Out.n, Cut.c, Cut.n, i53, v, nv, Expr.eval_mul', Expr.eval_col, Expr.eval_nxt,
      row_cur, row_nxt tr pub hr, ha, hb]; rfl
  have l1 := cuto_interS H hr' (e := Cut.Out.c "rlo") (c := Cut.Out.c "k4" * Cut.Out.n "k4")
    (by simp [Cut.Out.inters]) hc
  have l2 := cuto_interS H hr' (e := 16 * Cut.Out.c "rhi") (c := Cut.Out.c "k4" * Cut.Out.n "k4")
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
theorem cuto_k4_monoS (hl : CutoHiLimbs tr)
    (hsl : ∀ x, x < tr.height 31 → rowNat tr 31 x 53 = 1 → rowNat tr 31 x 48 < 2 ^ 30) :
    ∀ d a, a + d + 1 < tr.height 31 → rowNat tr 31 a 53 = 1 → rowNat tr 31 (a + d + 1) 53 = 1 →
      rowNat tr 31 a 48 < rowNat tr 31 (a + d + 1) 48
  | 0, a, hb, ha, hb4 => cuto_k4_stepS H hb ha hb4 (hsl a (by omega) ha) (hsl _ hb hb4)
  | d + 1, a, hb, ha, hb4 => by
    have hm : rowNat tr 31 (a + d + 1) 53 = 1 :=
      cuto_k4_betweenS H hl (a := a) (m := a + d + 1) (b := a + (d + 1) + 1) hb (by omega) (by omega) ha hb4
    have h1 := cuto_k4_monoS hl hsl d a (by omega) ha hm
    have h2 := cuto_k4_stepS H (r := a + d + 1) (by omega) hm (by simpa [Nat.add_assoc] using hb4)
      (hsl _ (by omega) hm) (hsl _ (by omega) (by simpa [Nat.add_assoc] using hb4))
    rw [show a + (d + 1) + 1 = a + d + 1 + 1 by omega]; omega

/-- The fields of an active row's consumed message. -/
theorem cutoMsg_fieldsS (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    (cutoMsg tr pub r).space = rowNat tr 31 r 47 ∧ (cutoMsg tr pub r).slot = rowNat tr 31 r 48 ∧
      (cutoMsg tr pub r).tag = cutoF tr r 2 ∧ (cutoMsg tr pub r).l0 = cutoF tr r 3 ∧
      (cutoMsg tr pub r).l1 = cutoF tr r 4 ∧ (cutoMsg tr pub r).l2 = rowNat tr 31 r 49 ∧
      (cutoMsg tr pub r).l3 = cutoF tr r 6 := by
  obtain ⟨i47, i48, i49, -⟩ := cuto_ix2
  have hP := P_val
  have hF := fun k (hk : k < 7) => cutoF_ltS H hl hr ha hk
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
theorem cutoMsg_space4S (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    (cutoMsg tr pub r).space = 4 ↔ rowNat tr 31 r 53 = 1 := by
  rw [(cutoMsg_fieldsS H hl hr ha).1]
  obtain ⟨b51, b52, b53, b54, b55, b56, hs⟩ := cuto_kindsS H hr
  rcases (by omega : rowNat tr 31 r 56 = 0 ∨ rowNat tr 31 r 56 = 1) with h0 | h1
  · rw [((cuto_fieldfactsS H hl hr ha).1 h0).1]; omega
  · rw [(cuto_kL_lookupS H hl hr ha h1).1]; omega

theorem cuto_dep_countS {r : Nat} (hr : r < tr.height 31) :
    rowNat tr 31 r 59 = ((List.range (r + 1)).filter (fun x => decide (rowNat tr 31 x 53 = 1))).length := by
  rw [cuto_depS H r hr, sum_map_bits (List.range (r + 1)) (fun x hx => by
    have := List.mem_range.mp hx; exact (cuto_kindsS H (by omega)).2.2.1)]

/-- **`dep` is the depth.**  Given the id facts of the final live list (`IdsOK`, spec side) and how it
meets CUTO (`CutoFin`), every record row's slot is a live id `I[i]` whose caller is `I[i+1]`, and its
`dep` is `σ` of the slot. -/
theorem cuto_k4_depS (hl : CutoHiLimbs tr) {fin : List Msg} {I : List Nat} {σ : Nat → Nat}
    (hI : IdsOK fin I σ) (hF : CutoFin tr pub fin) {r : Nat} (hr : r < tr.height 31)
    (h4 : rowNat tr 31 r 53 = 1) :
    rowNat tr 31 r 59 = σ (rowNat tr 31 r 48) ∧
      ∃ i, ∃ hi : i + 1 < I.length, rowNat tr 31 r 48 = I[i] ∧ rowNat tr 31 r 49 = I[i + 1] := by
  -- every record row's slot and caller are ids
  have slotI : ∀ x, x < tr.height 31 → rowNat tr 31 x 53 = 1 →
      ∃ i, ∃ hi : i + 1 < I.length, rowNat tr 31 x 48 = I[i] ∧ rowNat tr 31 x 49 = I[i + 1] := by
    intro x hx h4x
    have hax := cuto_act_of_k4S H hx h4x
    obtain ⟨f1, f2, -, -, -, f6, -⟩ := cutoMsg_fieldsS H hl hx hax
    obtain ⟨i, hi, e1, e2⟩ := hI.recs _ (hF.mem x hx hax) ((cutoMsg_space4S H hl hx hax).mpr h4x)
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
    have := cuto_k4_monoS H hl hsl (b - a - 1) a (by have := List.mem_range.mp hb1; omega) (by simpa [p] using ha2)
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
      have h4' := (cutoMsg_space4S H hl hr' ha').mp hx4
      refine List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨List.mem_range.mpr hr', by simpa [p] using h4'⟩, ?_⟩
      rw [← (cutoMsg_fieldsS H hl hr' ha').2.1, hxs]
  -- `r` is the `j`-th record row
  have hrK : r ∈ K := List.mem_filter.mpr ⟨List.mem_range.mpr hr, by simpa [p] using h4⟩
  obtain ⟨j, hj, hKj⟩ := List.mem_iff_getElem.mp hrK
  have hdep : rowNat tr 31 r 59 = j + 1 := by
    rw [cuto_dep_countS H hr, ← hKj]; exact filter_range_idx p _ j hj
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

/-- A dropped message is in a locals space `16 + c` of a dead activation `c`. -/
theorem drop_deadS {fin : List Msg} (hT : TombDead tr pub fin) {r : Nat} (hr : r < tr.height 18)
    (ha : rowNat tr 18 r 0 = 1) (hi : rowNat tr 18 r 1 = 0) :
    (dropMsg tr pub r).space = 16 + rowNat tr 18 r 2 ∧ rowNat tr 18 r 2 ≠ 0 ∧
      ∀ x ∈ fin, x.space = 4 → x.slot ≠ rowNat tr 18 r 2 := by
  obtain ⟨-, r'', hr'', htk, hc⟩ := drop_only_tombstonedS H hr ha hi
  obtain ⟨a, b, c⟩ := hT r'' hr'' htk
  rw [hc] at a b c
  exact ⟨dropMsg_space tr pub r a, b, c⟩

/-- `CutoFin` from the split and the dead-tombstone fact. -/
theorem cutoFin_ofS {fin : List Msg} (hin : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → cutoMsg tr pub r ∈ fin)
    (hS : FinSplit tr pub fin) (hT : TombDead tr pub fin) : CutoFin tr pub fin := by
  refine ⟨hin, fun x hx h4 => ?_⟩
  rcases hS x hx with h | h | h | ⟨r, hr, ha, hi, rfl⟩
  · exact h
  · omega
  · omega
  · have := (drop_deadS H hT hr ha hi).1; omega

/-- **One CUTO row is one kept, relabelled live message.**  An active row's consumed message is kept
(`keepA`) and its hashed fields are the fields of its depth relabelling (`rlMsg σ`); the hashed space
is neither memory nor the gas register. -/
theorem cuto_row_linkS (hl : CutoHiLimbs tr) {fin : List Msg} {I : List Nat} {σ : Nat → Nat}
    (hI : IdsOK fin I σ) (hF : CutoFin tr pub fin) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) :
    keepA I (cutoMsg tr pub r) ∧ fieldsOf (rlMsg σ (cutoMsg tr pub r)) = cutoRow tr r ∧
      cutoF tr r 0 ≠ 3 ∧ cutoF tr r 0 ≠ 7 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := cutoMsg_fieldsS H hl hr ha
  obtain ⟨b51, b52, b53, b54, b55, b56, hs⟩ := cuto_kindsS H hr
  have ff := cuto_fieldfactsS H hl hr ha
  have hσ0 := hI.sigma_zero.1
  rw [cutoRow_eq]
  rcases (by omega : rowNat tr 31 r 56 = 1 ∨ (rowNat tr 31 r 56 = 0 ∧ rowNat tr 31 r 53 = 1) ∨
    (rowNat tr 31 r 56 = 0 ∧ rowNat tr 31 r 53 = 0)) with hL | ⟨h0, h4⟩ | ⟨h0, h40⟩
  · -- a locals row
    have h40 : rowNat tr 31 r 53 = 0 := by omega
    obtain ⟨hsp, -, hlk⟩ := cuto_kL_lookupS H hl hr ha hL
    have key : cutoCL tr r ∈ I ∧ cutoF tr r 0 = 16 + σ (cutoCL tr r) := by
      rcases hlk with ⟨e1, e2⟩ | ⟨r', hr', h4', ha', e1, e2⟩
      · rw [e1, hσ0]; exact ⟨hI.zero, e2⟩
      · obtain ⟨d1, i, hi, s1, -⟩ := cuto_k4_depS H hl hI hF hr' h4'
        rw [← e1]
        refine ⟨by rw [s1]; exact List.getElem_mem _, ?_⟩
        rw [e2, (cuto_fieldfactsS H hl hr' ha').2.2.2.1 h4', d1]
    have hx16 : (cutoMsg tr pub r).space = 16 + cutoCL tr r := by rw [f0, hsp]
    refine ⟨fun _ => by rw [hx16]; simpa using key.1, ?_, by omega, by omega⟩
    simp only [rlMsg, hx16, show ¬ (16 + cutoCL tr r = 4) by omega, if_false, show 16 ≤ 16 + cutoCL tr r by omega,
      if_true, show 16 + cutoCL tr r - 16 = cutoCL tr r by omega, fieldsOf]
    rw [f1, f2, f3, f4, f5, f6, ← key.2, ff.2.2.1 h40, ff.2.2.2.2 h40]
  · -- a record row
    obtain ⟨e1, e2⟩ := ff.1 h0
    have hsp4 : (cutoMsg tr pub r).space = 4 := by rw [f0, e1]; omega
    obtain ⟨d1, -⟩ := cuto_k4_depS H hl hI hF hr h4
    have hF5 : cutoF tr r 5 = σ (rowNat tr 31 r 49) := by
      rcases cuto_k4_lookupS H hl hr ha h4 with ⟨a1, a2⟩ | ⟨r', hr', h4', ha', a1, a2⟩
      · rw [a1, a2, hσ0]
      · rw [a2, ← a1, (cuto_fieldfactsS H hl hr' ha').2.2.2.1 h4', (cuto_k4_depS H hl hI hF hr' h4').1]
    refine ⟨fun h => by omega, ?_, by omega, by omega⟩
    simp only [rlMsg, hsp4, if_true, fieldsOf]
    rw [f1, f2, f3, f4, f5, f6, e2, e1, ff.2.2.2.1 h4, d1, hF5]
    simp only [List.cons.injEq, and_true]; omega
  · -- operand stack, globals, budget, registers
    obtain ⟨e1, e2⟩ := ff.1 h0
    have hsp : (cutoMsg tr pub r).space = 2 * rowNat tr 31 r 52 + 5 * rowNat tr 31 r 54 + 6 * rowNat tr 31 r 55 := by
      rw [f0, e1, h40]; omega
    have hlow : rlMsg σ (cutoMsg tr pub r) = cutoMsg tr pub r := rlMsg_low (by omega) (by omega)
    refine ⟨fun h => by omega, ?_, by omega, by omega⟩
    rw [hlow]
    simp only [fieldsOf]
    rw [f1, f2, f3, f4, f5, f6, e2, ff.2.2.1 h40, ff.2.2.2.2 h40, f0]

/-- **The CUTO link.**  On a satisfying segment trace (with the chip limb bound), for a final live list
`fin` that CUTO's consumptions lie in (`hin`), that splits into CUTO/MEMB/SEGB/DROP consumptions
(`FinSplit`), whose returned activations are dead (`TombDead`), and whose ids/depth map satisfy
`IdsOK` (spec side, `cutView_eqL`): CUTO's hashed list has as members exactly the fields of the kept,
depth-relabelled live messages outside memory and the gas register. -/
theorem cuto_linkS (hl : CutoHiLimbs tr) {fin : List Msg} {I : List Nat} {σ : Nat → Nat}
    (hI : IdsOK fin I σ) (hin : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → cutoMsg tr pub r ∈ fin)
    (hS : FinSplit tr pub fin) (hT : TombDead tr pub fin) :
    ∀ y, y ∈ cutoList tr ↔ ∃ x ∈ (fin.filter (fun x => decide (keepA I x))).map (rlMsg σ),
      x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y := by
  have hF := cutoFin_ofS H hin hS hT
  intro y
  constructor
  · intro hy
    simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
    obtain ⟨r, ⟨hr, ha⟩, rfl⟩ := hy
    obtain ⟨k, e, n3, n7⟩ := cuto_row_linkS H hl hI hF hr ha
    have hsp : (rlMsg σ (cutoMsg tr pub r)).space = cutoF tr r 0 := by
      have := congrArg (fun l => l.getD 0 0) e
      simpa [fieldsOf, cutoRow_eq] using this
    refine ⟨rlMsg σ (cutoMsg tr pub r), List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hin r hr ha, by simpa using k⟩, rfl⟩,
      by rw [hsp]; exact n3, by rw [hsp]; exact n7, e⟩
  · rintro ⟨x', hx', n3, n7, rfl⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨hxf, hk⟩ := List.mem_filter.mp hx
    simp only [decide_eq_true_eq] at hk
    have hs := rlMsg_space σ x
    rcases hS x hxf with ⟨r, hr, ha, rfl⟩ | h3 | h7 | ⟨r, hr, ha, hi, rfl⟩
    · obtain ⟨-, e, -⟩ := cuto_row_linkS H hl hI hF hr ha
      rw [e]
      simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨r, ⟨hr, ha⟩, rfl⟩
    · rw [h3] at hs; simp at hs; exact absurd hs n3
    · rw [h7] at hs; simp at hs; exact absurd hs n7
    · exfalso
      obtain ⟨dsp, d0, dno⟩ := drop_deadS H hT hr ha hi
      have hc : rowNat tr 18 r 2 ∈ I := by have := hk (by omega); rwa [dsp, show 16 + rowNat tr 18 r 2 - 16 = rowNat tr 18 r 2 by omega] at this
      obtain ⟨i, hi', hci⟩ := List.mem_iff_getElem.mp hc
      by_cases hlast : i + 1 < I.length
      · obtain ⟨z, hz, hz4, hzs⟩ := hI.recEx i hlast
        exact dno z hz hz4 (by rw [hzs, hci])
      · have := hI.dep i hi'
        have h0 : I[i] = 0 := by
          refine Classical.byContradiction fun hne => ?_
          obtain ⟨i0, hi0, e0⟩ := List.mem_iff_getElem.mp hI.zero
          have := hI.sigma_zero.2 i0 hi0 e0
          have : i0 < i := by
            rcases Nat.lt_trichotomy i0 i with h | h | h
            · exact h
            · subst h; exact absurd e0 hne
            · omega
          have := List.pairwise_iff_getElem.mp hI.desc i0 i hi0 hi' this
          omega
        exact d0 (by rw [← hci, h0])

end

end WasmBase
