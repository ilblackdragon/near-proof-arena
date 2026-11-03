import WasmBase.SegAirMP
import WasmBase.Main.SegMpath
import WasmBase.Main.BusCount
/-!
# WasmBase.Main.SegMP — the multiproof MPATH of `wasmBaseSegAirMP` (E2E M4b)

PLACEHOLDER
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## The table -/

theorem segMP_lt (nloc ngl t : Nat) (h : t < 32) : t < (wasmBaseSegAirMP nloc ngl).tables.length := by
  rw [segMP_len]; exact h

theorem segMP_t20' (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables[20]'(segMP_lt nloc ngl 20 (by decide)) = MpathMP.table := by
  have h := segMP_t20 nloc ngl
  rw [List.getElem?_eq_getElem (segMP_lt nloc ngl 20 (by decide))] at h
  exact Option.some.inj h

theorem segMP_t0' (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables[0]'(segMP_lt nloc ngl 0 (by decide)) = Segb.table := rfl

theorem segMP_t19' (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables[19]'(segMP_lt nloc ngl 19 (by decide)) = Memb.table := rfl

theorem mpm_ix : ix MpathMP.cols "act" = 0 ∧ ix MpathMP.cols "top" = 1 ∧ ix MpathMP.cols "ro" = 2 ∧
    ix MpathMP.cols "lvl" = 3 ∧ ix MpathMP.cols "idx" = 4 ∧ ix MpathMP.cols "lfL" = 5 ∧
    ix MpathMP.cols "ndL" = 6 ∧ ix MpathMP.cols "lfR" = 7 ∧ ix MpathMP.cols "ndR" = 8 ∧
    ix MpathMP.cols "rL" = 9 ∧ ix MpathMP.cols "rR" = 10 := by decide

theorem mpm_ix_limbs : ∀ l, l < 18 → ix MpathMP.cols s!"oL{l}" = 13 + l ∧ ix MpathMP.cols s!"nL{l}" = 31 + l ∧
    ix MpathMP.cols s!"oR{l}" = 49 + l ∧ ix MpathMP.cols s!"nR{l}" = 67 + l ∧
    ix MpathMP.cols s!"po{l}" = 85 + l ∧ ix MpathMP.cols s!"pn{l}" = 103 + l := by decide

theorem mpm_ix_bits : ∀ i, i < 5 → ix MpathMP.cols s!"a{i}" = 133 + i ∧ ix MpathMP.cols s!"b{i}" = 138 + i := by
  decide

theorem mpm_cx {pub : List F} {tr : Trace} (r i : Nat) : (Chips.v i).eval (tr.row pub 20 r) = mc tr r i := rfl

/-- The depth `D` (public value 103). -/
abbrev pD (pub : List F) : F := pub.getD pubDepth 0

section rows
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAirMP nloc ngl) pub tr)
include H

theorem mpm_C {r : Nat} (hr : r < tr.height 20) :
    ∀ e ∈ MpathMP.constraints, e.eval (tr.row pub 20 r) = 0 := by
  intro e he
  exact H.constr 20 (segMP_lt nloc ngl 20 (by decide)) r hr e (by rw [segMP_t20']; exact he)

/-- **Row facts of the multiproof MPATH.** -/
theorem mpm_row {r : Nat} (hr : r < tr.height 20) :
    -- booleans
    (mc tr r 0 = 0 ∨ mc tr r 0 = 1) ∧ (mc tr r 1 = 0 ∨ mc tr r 1 = 1) ∧ (mc tr r 2 = 0 ∨ mc tr r 2 = 1) ∧
    (mc tr r 5 = 0 ∨ mc tr r 5 = 1) ∧ (mc tr r 6 = 0 ∨ mc tr r 6 = 1) ∧
    (mc tr r 7 = 0 ∨ mc tr r 7 = 1) ∧ (mc tr r 8 = 0 ∨ mc tr r 8 = 1) ∧
    -- inactive rows carry nothing
    (mc tr r 0 = 0 → mc tr r 1 = 0 ∧ mc tr r 2 = 0 ∧ mc tr r 5 = 0 ∧ mc tr r 6 = 0 ∧ mc tr r 7 = 0 ∧ mc tr r 8 = 0) ∧
    -- a child is a leaf or a node, not both; leaves at level 1
    (mc tr r 5 * mc tr r 6 = 0) ∧ (mc tr r 7 * mc tr r 8 = 0) ∧
    (mc tr r 5 = 1 → mc tr r 3 = 1) ∧ (mc tr r 7 = 1 → mc tr r 3 = 1) ∧
    -- the root
    (mc tr r 1 = 1 → mc tr r 3 = pD pub ∧ mc tr r 4 = 0) := by
  have C := mpm_C H hr
  obtain ⟨ia, it, iro, ilv, iidx, ilfL, indL, ilfR, indR, -, -⟩ := mpm_ix
  have one : ((1 : Nat) : F) = 1 := rfl
  have px : (Chips.pv pubDepth).eval (tr.row pub 20 r) = pD pub := by
    simp [Chips.pv, Expr.eval_pub, Trace.row]
  have bb : ∀ n i, ix MpathMP.cols n = i → Chips.bool (MpathMP.c n) ∈ MpathMP.constraints →
      mc tr r i = 0 ∨ mc tr r i = 1 := by
    intro n i hi hm
    have h := C _ hm
    simp only [Chips.bool, MpathMP.c, hi, Expr.eval_mul', Expr.eval_sub', mpm_cx, Expr.eval_ofNat', one] at h
    exact bool_cases h
  have z : ∀ e, e ∈ MpathMP.constraints → e.eval (tr.row pub 20 r) = 0 := C
  have b0 := bb "act" 0 ia (by simp [MpathMP.constraints])
  have b1 := bb "top" 1 it (by simp [MpathMP.constraints])
  have b2 := bb "ro" 2 iro (by simp [MpathMP.constraints])
  have b5 := bb "lfL" 5 ilfL (by simp [MpathMP.constraints])
  have b6 := bb "ndL" 6 indL (by simp [MpathMP.constraints])
  have b7 := bb "lfR" 7 ilfR (by simp [MpathMP.constraints])
  have b8 := bb "ndR" 8 indR (by simp [MpathMP.constraints])
  have i1 := z ((1 - MpathMP.c "act") * MpathMP.c "top") (by simp [MpathMP.constraints])
  have i2 := z ((1 - MpathMP.c "act") * MpathMP.c "ro") (by simp [MpathMP.constraints])
  have i5 := z ((1 - MpathMP.c "act") * MpathMP.c "lfL") (by simp [MpathMP.constraints])
  have i6 := z ((1 - MpathMP.c "act") * MpathMP.c "ndL") (by simp [MpathMP.constraints])
  have i7 := z ((1 - MpathMP.c "act") * MpathMP.c "lfR") (by simp [MpathMP.constraints])
  have i8 := z ((1 - MpathMP.c "act") * MpathMP.c "ndR") (by simp [MpathMP.constraints])
  have x1 := z (MpathMP.c "lfL" * MpathMP.c "ndL") (by simp [MpathMP.constraints])
  have x2 := z (MpathMP.c "lfR" * MpathMP.c "ndR") (by simp [MpathMP.constraints])
  have l1 := z (MpathMP.c "lfL" * (MpathMP.c "lvl" - 1)) (by simp [MpathMP.constraints])
  have l2 := z (MpathMP.c "lfR" * (MpathMP.c "lvl" - 1)) (by simp [MpathMP.constraints])
  have t1 := z (MpathMP.c "top" * (MpathMP.c "lvl" - Chips.pv pubDepth)) (by simp [MpathMP.constraints])
  have t2 := z (MpathMP.c "top" * MpathMP.c "idx") (by simp [MpathMP.constraints])
  simp only [MpathMP.c, ia, it, iro, ilv, iidx, ilfL, indL, ilfR, indR, Expr.eval_mul', Expr.eval_sub',
    mpm_cx, Expr.eval_ofNat', one, px] at i1 i2 i5 i6 i7 i8 x1 x2 l1 l2 t1 t2
  refine ⟨b0, b1, b2, b5, b6, b7, b8, fun h0 => ?_, x1, x2, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h0] at i1 i2 i5 i6 i7 i8
    exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
  · rw [h] at l1; grind
  · rw [h] at l2; grind
  · rw [h] at t1 t2; exact ⟨by grind, by grind⟩


theorem mpm_limbs {r : Nat} (hr : r < tr.height 20) :
    (mc tr r 5 = 0 → mc tr r 6 = 0 → mdig tr r 31 = mdig tr r 13) ∧
    (mc tr r 7 = 0 → mc tr r 8 = 0 → mdig tr r 67 = mdig tr r 49) ∧
    (mc tr r 2 = 1 → mdig tr r 31 = mdig tr r 13 ∧ mdig tr r 67 = mdig tr r 49 ∧ mdig tr r 103 = mdig tr r 85) := by
  have C := mpm_C H hr
  obtain ⟨-, -, iro, -, -, ilfL, indL, ilfR, indR, -, -⟩ := mpm_ix
  have one : ((1 : Nat) : F) = 1 := rfl
  have mem : ∀ l Z, l < 18 → Z ∈ [(1 - MpathMP.c "lfL" - MpathMP.c "ndL") * (MpathMP.c s!"nL{l}" - MpathMP.c s!"oL{l}"),
      (1 - MpathMP.c "lfR" - MpathMP.c "ndR") * (MpathMP.c s!"nR{l}" - MpathMP.c s!"oR{l}"),
      MpathMP.c "ro" * (MpathMP.c s!"nL{l}" - MpathMP.c s!"oL{l}"),
      MpathMP.c "ro" * (MpathMP.c s!"nR{l}" - MpathMP.c s!"oR{l}"),
      MpathMP.c "ro" * (MpathMP.c s!"pn{l}" - MpathMP.c s!"po{l}")] → Z ∈ MpathMP.constraints := by
    intro l Z hl hZ
    unfold MpathMP.constraints
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, hZ⟩)
  have lim : ∀ l, l < 18 →
      (mc tr r 5 = 0 → mc tr r 6 = 0 → mc tr r (31 + l) = mc tr r (13 + l)) ∧
      (mc tr r 7 = 0 → mc tr r 8 = 0 → mc tr r (67 + l) = mc tr r (49 + l)) ∧
      (mc tr r 2 = 1 → mc tr r (31 + l) = mc tr r (13 + l) ∧ mc tr r (67 + l) = mc tr r (49 + l) ∧
        mc tr r (103 + l) = mc tr r (85 + l)) := by
    intro l hl
    obtain ⟨joL, jnL, joR, jnR, jpo, jpn⟩ := mpm_ix_limbs l hl
    have e1 := C _ (mem l ((1 - MpathMP.c "lfL" - MpathMP.c "ndL") * (MpathMP.c s!"nL{l}" - MpathMP.c s!"oL{l}")) hl (by simp))
    have e2 := C _ (mem l ((1 - MpathMP.c "lfR" - MpathMP.c "ndR") * (MpathMP.c s!"nR{l}" - MpathMP.c s!"oR{l}")) hl (by simp))
    have e3 := C _ (mem l (MpathMP.c "ro" * (MpathMP.c s!"nL{l}" - MpathMP.c s!"oL{l}")) hl (by simp))
    have e4 := C _ (mem l (MpathMP.c "ro" * (MpathMP.c s!"nR{l}" - MpathMP.c s!"oR{l}")) hl (by simp))
    have e5 := C _ (mem l (MpathMP.c "ro" * (MpathMP.c s!"pn{l}" - MpathMP.c s!"po{l}")) hl (by simp))
    simp only [MpathMP.c, iro, ilfL, indL, ilfR, indR, joL, jnL, joR, jnR, jpo, jpn, Expr.eval_mul', Expr.eval_sub',
      mpm_cx, Expr.eval_ofNat', one] at e1 e2 e3 e4 e5
    refine ⟨fun h5 h6 => ?_, fun h7 h8 => ?_, fun h2 => ?_⟩
    · rw [h5, h6] at e1; grind
    · rw [h7, h8] at e2; grind
    · rw [h2] at e3 e4 e5; exact ⟨by grind, by grind, by grind⟩
  refine ⟨fun h5 h6 => mdig_eq fun l hl => (lim l hl).1 h5 h6, fun h7 h8 => mdig_eq fun l hl => (lim l hl).2.1 h7 h8,
    fun h2 => ⟨mdig_eq fun l hl => ((lim l hl).2.2 h2).1, mdig_eq fun l hl => ((lim l hl).2.2 h2).2.1,
      mdig_eq fun l hl => ((lim l hl).2.2 h2).2.2⟩⟩

omit H in
theorem bits5_a : MpathMP.bits5 "a" =
    0 + Expr.c 1 * v 133 + Expr.c 2 * v 134 + Expr.c 4 * v 135 + Expr.c 8 * v 136 + Expr.c 16 * v 137 := by
  decide
omit H in
theorem bits5_b : MpathMP.bits5 "b" =
    0 + Expr.c 1 * v 138 + Expr.c 2 * v 139 + Expr.c 4 * v 140 + Expr.c 8 * v 141 + Expr.c 16 * v 142 := by
  decide

omit H in
theorem bit_nat {x : F} (h : x = 0 ∨ x = 1) : ∃ n : Nat, n ≤ 1 ∧ x = (n : F) := by
  rcases h with h | h
  · exact ⟨0, by omega, h⟩
  · exact ⟨1, Nat.le_refl _, h⟩

/-- **Level range.**  An active row has `lvl = 1 + a` and `D = 1 + a + b` with `a, b < 32`. -/
theorem mpm_level {r : Nat} (hr : r < tr.height 20) (hact : mc tr r 0 = 1) :
    ∃ a b : Nat, a < 32 ∧ b < 32 ∧ mc tr r 3 = ((1 + a : Nat) : F) ∧ pD pub = ((1 + a + b : Nat) : F) := by
  have C := mpm_C H hr
  obtain ⟨ia, -, -, ilv, -, -, -, -, -, -, -⟩ := mpm_ix
  have one : ((1 : Nat) : F) = 1 := rfl
  have px : (Chips.pv pubDepth).eval (tr.row pub 20 r) = pD pub := by
    simp [Chips.pv, Expr.eval_pub, Trace.row]
  have bitc : ∀ i, i < 5 → (mc tr r (133 + i) = 0 ∨ mc tr r (133 + i) = 1) ∧
      (mc tr r (138 + i) = 0 ∨ mc tr r (138 + i) = 1) := by
    intro i hi
    obtain ⟨ja, jb⟩ := mpm_ix_bits i hi
    have mem : ∀ Z, Z ∈ [Chips.bool (MpathMP.c s!"a{i}"), Chips.bool (MpathMP.c s!"b{i}")] → Z ∈ MpathMP.constraints := by
      intro Z hZ
      unfold MpathMP.constraints
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hZ⟩))
    have e1 := C _ (mem (Chips.bool (MpathMP.c s!"a{i}")) (by simp))
    have e2 := C _ (mem (Chips.bool (MpathMP.c s!"b{i}")) (by simp))
    simp only [Chips.bool, MpathMP.c, ja, jb, Expr.eval_mul', Expr.eval_sub', mpm_cx, Expr.eval_ofNat', one] at e1 e2
    exact ⟨bool_cases e1, bool_cases e2⟩
  have ea := C (MpathMP.c "act" * (MpathMP.c "lvl" - 1 - MpathMP.bits5 "a")) (by simp [MpathMP.constraints])
  have eb := C (MpathMP.c "act" * (Chips.pv pubDepth - MpathMP.c "lvl" - MpathMP.bits5 "b")) (by simp [MpathMP.constraints])
  rw [bits5_a] at ea; rw [bits5_b] at eb
  simp only [MpathMP.c, ia, ilv, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', mpm_cx, Expr.eval_ofNat', Expr.eval_c,
    one, px, hact] at ea eb
  obtain ⟨a0, ha0, e0⟩ := bit_nat (bitc 0 (by decide)).1
  obtain ⟨a1, ha1, e1⟩ := bit_nat (bitc 1 (by decide)).1
  obtain ⟨a2, ha2, e2⟩ := bit_nat (bitc 2 (by decide)).1
  obtain ⟨a3, ha3, e3⟩ := bit_nat (bitc 3 (by decide)).1
  obtain ⟨a4, ha4, e4⟩ := bit_nat (bitc 4 (by decide)).1
  obtain ⟨b0, hb0, f0⟩ := bit_nat (bitc 0 (by decide)).2
  obtain ⟨b1, hb1, f1⟩ := bit_nat (bitc 1 (by decide)).2
  obtain ⟨b2, hb2, f2⟩ := bit_nat (bitc 2 (by decide)).2
  obtain ⟨b3, hb3, f3⟩ := bit_nat (bitc 3 (by decide)).2
  obtain ⟨b4, hb4, f4⟩ := bit_nat (bitc 4 (by decide)).2
  simp only [Nat.add_zero] at e0 f0
  rw [e0, e1, e2, e3, e4] at ea
  rw [f0, f1, f2, f3, f4] at eb
  refine ⟨a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4, b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4, by omega, by omega, ?_, ?_⟩
  · have : mc tr r 3 = 1 + ((0 : Nat) : F) + ((1 : Nat) : F) * (a0 : F) + ((2 : Nat) : F) * (a1 : F) +
        ((4 : Nat) : F) * (a2 : F) + ((8 : Nat) : F) * (a3 : F) + ((16 : Nat) : F) * (a4 : F) := by grind
    rw [this]; fp_ring
  · have hl : mc tr r 3 = 1 + ((0 : Nat) : F) + ((1 : Nat) : F) * (a0 : F) + ((2 : Nat) : F) * (a1 : F) +
        ((4 : Nat) : F) * (a2 : F) + ((8 : Nat) : F) * (a3 : F) + ((16 : Nat) : F) * (a4 : F) := by grind
    have : pD pub = mc tr r 3 + (((0 : Nat) : F) + ((1 : Nat) : F) * (b0 : F) + ((2 : Nat) : F) * (b1 : F) +
        ((4 : Nat) : F) * (b2 : F) + ((8 : Nat) : F) * (b3 : F) + ((16 : Nat) : F) * (b4 : F)) := by grind
    rw [this, hl]; fp_ring

end rows

/-! ## The buses 15 (leaf), 16 (RCH), 17 (node) -/

theorem segMP_tables_eq (nloc ngl : Nat) : (wasmBaseSegAirMP nloc ngl).tables = (wasmBaseSegAirMP 0 0).tables := rfl

/-- Only SEGB (0), MEMB (19) and MPATH (20) use buses 15, 16, 17. -/
theorem segMP_bus_other (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAirMP nloc ngl).tables.length), t ≠ 0 → t ≠ 19 → t ≠ 20 →
      ∀ i ∈ ((wasmBaseSegAirMP nloc ngl).tables[t]'ht).inters, i.bus ≠ 15 ∧ i.bus ≠ 16 ∧ i.bus ≠ 17 := by
  have h0 : ∀ t (ht : t < (wasmBaseSegAirMP 0 0).tables.length), t ≠ 0 → t ≠ 19 → t ≠ 20 →
      ((wasmBaseSegAirMP 0 0).tables[t]'ht).inters.all (fun i => i.bus != 15 && i.bus != 16 && i.bus != 17) = true := by
    decide
  have h : ∀ t (ht : t < (wasmBaseSegAirMP nloc ngl).tables.length), t ≠ 0 → t ≠ 19 → t ≠ 20 →
      ((wasmBaseSegAirMP nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != 15 && i.bus != 16 && i.bus != 17) = true := by
    simp only [segMP_tables_eq]; exact h0
  intro t ht a b c i hi
  have := List.all_eq_true.mp (h t ht a b c) i hi
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem segb_bus : Segb.table.inters.all (fun i => i.bus != 15 && i.bus != 17) = true := by decide
theorem memb_bus : Memb.table.inters.all (fun i => i.bus != 16 && i.bus != 17 &&
    (i.bus != 15 || (i.send && decide (i.count = Memb.p 8)))) = true := by decide +kernel

theorem mpm_f15 : MpathMP.table.inters.filter (fun i => i.bus = 15) =
    [⟨busLeaf, false, MpathMP.c "lfL", [2 * MpathMP.c "idx", MpathMP.c "rL"] ++ MpathMP.dig "oL" ++ MpathMP.dig "nL"⟩,
     ⟨busLeaf, false, MpathMP.c "lfR", [2 * MpathMP.c "idx" + 1, MpathMP.c "rR"] ++ MpathMP.dig "oR" ++ MpathMP.dig "nR"⟩] := by
  decide
theorem mpm_f16 : MpathMP.table.inters.filter (fun i => i.bus = 16) =
    [⟨busRch, false, MpathMP.c "top", [0] ++ MpathMP.dig "po"⟩,
     ⟨busRch, true, MpathMP.c "top", [1] ++ MpathMP.dig "pn"⟩] := by
  decide
theorem mpm_f17 : MpathMP.table.inters.filter (fun i => i.bus = 17) =
    [⟨busNode, false, MpathMP.c "ndL", [MpathMP.c "lvl" - 1, 2 * MpathMP.c "idx"] ++ MpathMP.dig "oL" ++ MpathMP.dig "nL"⟩,
     ⟨busNode, false, MpathMP.c "ndR", [MpathMP.c "lvl" - 1, 2 * MpathMP.c "idx" + 1] ++ MpathMP.dig "oR" ++ MpathMP.dig "nR"⟩,
     ⟨busNode, true, MpathMP.c "act" - MpathMP.c "top", [MpathMP.c "lvl", MpathMP.c "idx"] ++ MpathMP.dig "po" ++ MpathMP.dig "pn"⟩] := by
  decide

theorem mpm_dig_eval (tr : Trace) (pub : List F) (r : Nat) (base : Nat) (s : String)
    (hix : ∀ l, l < 18 → ix MpathMP.cols s!"{s}{l}" = base + l) :
    (MpathMP.dig s).map (·.eval (tr.row pub 20 r)) = mdig tr r base := by
  simp only [MpathMP.dig, names, mdig, List.map_map]
  apply List.map_congr_left; intro l hl
  simp only [Function.comp, MpathMP.c, hix l (List.mem_range.mp hl)]
  rfl

/-- The node bus message a row sends: `[lvl, idx] ++ po ++ pn`. -/
def sendN (tr : Trace) (r : Nat) : List F := [mc tr r 3, mc tr r 4] ++ mdig tr r 85 ++ mdig tr r 103
/-- The node bus message of the left / right child receive: `[lvl − 1, 2·idx + s] ++ oX ++ nX`. -/
def recvNL (tr : Trace) (r : Nat) : List F :=
  [mc tr r 3 - 1, ((2 : Nat) : F) * mc tr r 4] ++ mdig tr r 13 ++ mdig tr r 31
def recvNR (tr : Trace) (r : Nat) : List F :=
  [mc tr r 3 - 1, ((2 : Nat) : F) * mc tr r 4 + 1] ++ mdig tr r 49 ++ mdig tr r 67
/-- The leaf bus message of the left / right child receive: `[2·idx + s, rX] ++ oX ++ nX`. -/
def recvLL (tr : Trace) (r : Nat) : List F := [((2 : Nat) : F) * mc tr r 4, mc tr r 9] ++ mdig tr r 13 ++ mdig tr r 31
def recvLR (tr : Trace) (r : Nat) : List F :=
  [((2 : Nat) : F) * mc tr r 4 + 1, mc tr r 10] ++ mdig tr r 49 ++ mdig tr r 67

theorem mpm_dig_oL (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.dig "oL").map (·.eval (tr.row pub 20 r)) = mdig tr r 13 :=
  mpm_dig_eval tr pub r 13 "oL" fun l hl => (mpm_ix_limbs l hl).1
theorem mpm_dig_nL (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.dig "nL").map (·.eval (tr.row pub 20 r)) = mdig tr r 31 :=
  mpm_dig_eval tr pub r 31 "nL" fun l hl => (mpm_ix_limbs l hl).2.1
theorem mpm_dig_oR (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.dig "oR").map (·.eval (tr.row pub 20 r)) = mdig tr r 49 :=
  mpm_dig_eval tr pub r 49 "oR" fun l hl => (mpm_ix_limbs l hl).2.2.1
theorem mpm_dig_nR (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.dig "nR").map (·.eval (tr.row pub 20 r)) = mdig tr r 67 :=
  mpm_dig_eval tr pub r 67 "nR" fun l hl => (mpm_ix_limbs l hl).2.2.2.1
theorem mpm_dig_po (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.dig "po").map (·.eval (tr.row pub 20 r)) = mdig tr r 85 :=
  mpm_dig_eval tr pub r 85 "po" fun l hl => (mpm_ix_limbs l hl).2.2.2.2.1
theorem mpm_dig_pn (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.dig "pn").map (·.eval (tr.row pub 20 r)) = mdig tr r 103 :=
  mpm_dig_eval tr pub r 103 "pn" fun l hl => (mpm_ix_limbs l hl).2.2.2.2.2

/-- The evaluated bus-17 interactions of an MPATH row. -/
theorem mpm_occ17_row (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.table.inters.filter (fun i => i.bus = 17)).map (fun i =>
      ((i.bus, i.send, i.msg.map (·.eval (tr.row pub 20 r)), (i.count.eval (tr.row pub 20 r)).toNat) : Occ)) =
    [(17, false, recvNL tr r, (mc tr r 6).toNat), (17, false, recvNR tr r, (mc tr r 8).toNat),
     (17, true, sendN tr r, (mc tr r 0 - mc tr r 1).toNat)] := by
  obtain ⟨ia, it, -, ilv, iidx, -, indL, -, indR, -, -⟩ := mpm_ix
  rw [mpm_f17]
  simp only [List.map_cons, List.map_nil, List.map_append, MpathMP.c, ia, it, ilv, iidx, indL, indR,
    Expr.eval_sub', Expr.eval_mul', Expr.eval_add', Expr.eval_ofNat', mpm_cx, mpm_dig_oL, mpm_dig_nL, mpm_dig_oR,
    mpm_dig_nR, mpm_dig_po, mpm_dig_pn, recvNL, recvNR, sendN]
  rfl

theorem mpm_occ15_row (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.table.inters.filter (fun i => i.bus = 15)).map (fun i =>
      ((i.bus, i.send, i.msg.map (·.eval (tr.row pub 20 r)), (i.count.eval (tr.row pub 20 r)).toNat) : Occ)) =
    [(15, false, recvLL tr r, (mc tr r 5).toNat), (15, false, recvLR tr r, (mc tr r 7).toNat)] := by
  obtain ⟨-, -, -, -, iidx, ilfL, -, ilfR, -, irL, irR⟩ := mpm_ix
  rw [mpm_f15]
  simp only [List.map_cons, List.map_nil, List.map_append, MpathMP.c, iidx, ilfL, ilfR, irL, irR,
    Expr.eval_mul', Expr.eval_add', Expr.eval_ofNat', mpm_cx, mpm_dig_oL, mpm_dig_nL, mpm_dig_oR,
    mpm_dig_nR, recvLL, recvLR]
  rfl

theorem mpm_occ16_row (tr : Trace) (pub : List F) (r : Nat) :
    (MpathMP.table.inters.filter (fun i => i.bus = 16)).map (fun i =>
      ((i.bus, i.send, i.msg.map (·.eval (tr.row pub 20 r)), (i.count.eval (tr.row pub 20 r)).toNat) : Occ)) =
    [(16, false, [0] ++ mdig tr r 85, (mc tr r 1).toNat), (16, true, [1] ++ mdig tr r 103, (mc tr r 1).toNat)] := by
  obtain ⟨-, it, -, -, -, -, -, -, -, -, -⟩ := mpm_ix
  rw [mpm_f16]
  simp only [List.map_cons, List.map_nil, List.map_append, MpathMP.c, it, Expr.eval_ofNat', mpm_cx,
    mpm_dig_po, mpm_dig_pn]
  rfl

/-- An occurrence of an MPATH interaction on bus `b` is among the evaluated filter. -/
theorem mpm_occ_mem {tr : Trace} {pub : List F} {r : Nat} {i : Inter} (hi : i ∈ MpathMP.table.inters) (b : Nat)
    (hb : i.bus = b) :
    ((i.bus, i.send, i.msg.map (·.eval (tr.row pub 20 r)), (i.count.eval (tr.row pub 20 r)).toNat) : Occ) ∈
      (MpathMP.table.inters.filter (fun i => i.bus = b)).map (fun i =>
        ((i.bus, i.send, i.msg.map (·.eval (tr.row pub 20 r)), (i.count.eval (tr.row pub 20 r)).toNat) : Occ)) :=
  List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hb]⟩, rfl⟩

/-- `Expr.first` on SEGB rows. -/
theorem segb_first_eval (tr : Trace) (pub : List F) (r : Nat) :
    Expr.first.eval (tr.row pub 0 r) = if r = 0 then 1 else 0 := by
  by_cases h : r = 0 <;> simp [Expr.eval, Trace.row, h]

/-- **Every occurrence on buses 15, 16, 17.** -/
theorem segMP_occ {nloc ngl : Nat} {pub : List F} {tr : Trace} {o : Occ}
    (ho : o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub) :
    (o.1 = 17 → ∃ r, r < tr.height 20 ∧ (o = (17, false, recvNL tr r, (mc tr r 6).toNat) ∨
        o = (17, false, recvNR tr r, (mc tr r 8).toNat) ∨ o = (17, true, sendN tr r, (mc tr r 0 - mc tr r 1).toNat))) ∧
    (o.1 = 15 → (o.2.1 = true ∧ ∃ r, r < tr.height 19 ∧ o.2.2.2 = ((Memb.p 8).eval (tr.row pub 19 r)).toNat) ∨
      ∃ r, r < tr.height 20 ∧ (o = (15, false, recvLL tr r, (mc tr r 5).toNat) ∨
        o = (15, false, recvLR tr r, (mc tr r 7).toNat))) ∧
    (o.1 = 16 → (∃ r, r < tr.height 0 ∧
        (o = (16, true, [0] ++ pubDig pub pubMemIn, (if r = 0 then (1 : F) else 0).toNat) ∨
         o = (16, false, [tr.cell 0 r 3] ++ pubDig pub pubMemOut, (if r = 0 then (1 : F) else 0).toNat))) ∨
      ∃ r, r < tr.height 20 ∧ (o = (16, false, [0] ++ mdig tr r 85, (mc tr r 1).toNat) ∨
        o = (16, true, [1] ++ mdig tr r 103, (mc tr r 1).toNat))) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  have hp : (tr.row pub t r).pub = fun i => pub.getD i 0 := rfl
  by_cases h20 : t = 20
  · subst h20
    rw [segMP_t20'] at hi
    refine ⟨fun hb => ⟨r, hr, ?_⟩, fun hb => Or.inr ⟨r, hr, ?_⟩, fun hb => Or.inr ⟨r, hr, ?_⟩⟩
    · have := mpm_occ_mem (tr := tr) (pub := pub) (r := r) hi 17 hb
      rw [mpm_occ17_row] at this
      simpa only [List.mem_cons, List.mem_nil_iff, or_false] using this
    · have := mpm_occ_mem (tr := tr) (pub := pub) (r := r) hi 15 hb
      rw [mpm_occ15_row] at this
      simpa only [List.mem_cons, List.mem_nil_iff, or_false] using this
    · have := mpm_occ_mem (tr := tr) (pub := pub) (r := r) hi 16 hb
      rw [mpm_occ16_row] at this
      simpa only [List.mem_cons, List.mem_nil_iff, or_false] using this
  by_cases h0 : t = 0
  · subst h0
    rw [segMP_t0'] at hi
    have hs := List.all_eq_true.mp segb_bus i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
    refine ⟨fun hb => absurd hb hs.2, fun hb => absurd hb hs.1, fun hb => Or.inl ⟨r, hr, ?_⟩⟩
    have hm : i ∈ Segb.table.inters.filter (fun i => i.bus = 16) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [segb_rch] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · left
      simp only [List.map_append, List.map_cons, List.map_nil, Expr.eval_ofNat', segb_first_eval]
      rw [pubs_eval _ pub hp]; rfl
    · right
      simp only [List.map_append, List.map_cons, List.map_nil, Segb.c, segb_ix_nbt, segb_first_eval]
      rw [pubs_eval _ pub hp]; rfl
  by_cases h19 : t = 19
  · subst h19
    rw [segMP_t19'] at hi
    have hs := List.all_eq_true.mp memb_bus i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hs
    refine ⟨fun hb => absurd hb hs.1.2, fun hb => ?_, fun hb => absurd hb hs.1.1⟩
    rcases hs.2 with h | ⟨h1, h2⟩
    · exact absurd hb h
    · exact Or.inl ⟨h1, r, hr, by rw [h2]⟩
  have hn := segMP_bus_other nloc ngl t ht h0 h19 h20 i hi
  exact ⟨fun hb => absurd hb hn.2.2, fun hb => absurd hb hn.1, fun hb => absurd hb hn.2.1⟩

/-- With bit counts on both sides, `busNat` send `≥ 2` and receive `≤ 1` is impossible. -/
theorem no_double {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.2.2 ≤ 1) (m : List F)
    (h2 : 2 ≤ busNat A tr pub b true m) (h1 : busNat A tr pub b false m ≤ 1) : False := by
  have := perm_exact H b hbit m
  omega

theorem mpm_in17 (tr : Trace) (pub : List F) (r : Nat) :
    (17, false, recvNL tr r, (mc tr r 6).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r ∧
    (17, false, recvNR tr r, (mc tr r 8).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r ∧
    (17, true, sendN tr r, (mc tr r 0 - mc tr r 1).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r := by
  have h := mpm_occ17_row tr pub r
  refine ⟨mem_rowOccsT_of_filter (b := 17) ?_, mem_rowOccsT_of_filter (b := 17) ?_,
    mem_rowOccsT_of_filter (b := 17) ?_⟩ <;> rw [h] <;> simp

theorem mpm_in15 (tr : Trace) (pub : List F) (r : Nat) :
    (15, false, recvLL tr r, (mc tr r 5).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r ∧
    (15, false, recvLR tr r, (mc tr r 7).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r := by
  have h := mpm_occ15_row tr pub r
  refine ⟨mem_rowOccsT_of_filter (b := 15) ?_, mem_rowOccsT_of_filter (b := 15) ?_⟩ <;> rw [h] <;> simp

theorem mpm_in16 (tr : Trace) (pub : List F) (r : Nat) :
    (16, false, [0] ++ mdig tr r 85, (mc tr r 1).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r ∧
    (16, true, [1] ++ mdig tr r 103, (mc tr r 1).toNat) ∈ rowOccsT MpathMP.table tr pub 20 r := by
  have h := mpm_occ16_row tr pub r
  refine ⟨mem_rowOccsT_of_filter (b := 16) ?_, mem_rowOccsT_of_filter (b := 16) ?_⟩ <;> rw [h] <;> simp

theorem segb_in16 (tr : Trace) (pub : List F) :
    (16, true, [0] ++ pubDig pub pubMemIn, 1) ∈ rowOccsT Segb.table tr pub 0 0 := by
  have hp : (tr.row pub 0 0).pub = fun i => pub.getD i 0 := rfl
  have hm : (⟨busRch, true, .first, [0] ++ Segb.pubs pubMemIn 18⟩ : Inter) ∈ Segb.table.inters := by
    simp [Segb.table, Segb.inters]
  refine List.mem_map.mpr ⟨_, hm, ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil, Expr.eval_ofNat', segb_first_eval, ite_true]
  rw [pubs_eval _ pub hp]; rfl

theorem toNat_bit {x : F} (h : x = 0 ∨ x = 1) : x.toNat ≤ 1 := by
  rcases h with h | h <;> rw [h] <;> decide

theorem toNat_ne_zero_bit {x : F} (h : x = 0 ∨ x = 1) (hn : x.toNat ≠ 0) : x = 1 := by
  rcases h with h | h
  · rw [h] at hn; exact absurd rfl hn
  · exact h

section bus
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAirMP nloc ngl) pub tr)
include H

omit H in
theorem mpm_occ {r : Nat} (hr : r < tr.height 20) {o : Occ} (h : o ∈ rowOccsT MpathMP.table tr pub 20 r) :
    o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub :=
  mem_occs_of_rowOccsT (segMP_lt nloc ngl 20 (by decide)) hr (by rw [segMP_t20']; exact h)

theorem sub_bit {r : Nat} (hr : r < tr.height 20) :
    (mc tr r 0 - mc tr r 1 = 0 ∨ mc tr r 0 - mc tr r 1 = 1) ∧
    (mc tr r 0 - mc tr r 1 = 1 → mc tr r 0 = 1 ∧ mc tr r 1 = 0) := by
  obtain ⟨b0, b1, -, -, -, -, -, hz, -⟩ := mpm_row H hr
  rcases b0 with h0 | h0
  · have := (hz h0).1; rw [h0, this]
    refine ⟨Or.inl (by grind), fun h => absurd h (by grind)⟩
  · rcases b1 with h1 | h1 <;> rw [h0, h1]
    · exact ⟨Or.inr (by grind), fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨Or.inl (by grind), fun h => absurd h (by grind)⟩

theorem bits17 : ∀ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 17 → o.2.2.2 ≤ 1 := by
  intro o ho hb
  obtain ⟨r, hr, h | h | h⟩ := (segMP_occ ho).1 hb <;> subst h <;> simp only
  · exact toNat_bit (mpm_row H hr).2.2.2.2.1
  · exact toNat_bit (mpm_row H hr).2.2.2.2.2.2.1
  · exact toNat_bit (sub_bit H hr).1

theorem bits16 : ∀ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 16 → o.2.2.2 ≤ 1 := by
  intro o ho hb
  rcases (segMP_occ ho).2.2 hb with ⟨r, -, h | h⟩ | ⟨r, hr, h | h⟩ <;> subst h <;> simp only
  · by_cases e : r = 0 <;> simp [e] <;> decide
  · by_cases e : r = 0 <;> simp [e] <;> decide
  · exact toNat_bit (mpm_row H hr).2.1
  · exact toNat_bit (mpm_row H hr).2.1

theorem memb_p8_bit {r : Nat} (hr : r < tr.height 19) :
    ((Memb.p 8).eval (tr.row pub 19 r)).toNat ≤ 1 := by
  have h8 : Chips.bool (Memb.p 8) ∈ (List.range 9).map (fun i => Chips.bool (Memb.p i)) :=
    List.mem_map.mpr ⟨8, List.mem_range.mpr (by decide), rfl⟩
  have hm : Chips.bool (Memb.p 8) ∈ Memb.constraints := by
    unfold Memb.constraints; simp only [List.mem_append, h8, true_or, or_true]
  have h := H.constr 19 (segMP_lt nloc ngl 19 (by decide)) r hr _ (by rw [segMP_t19']; exact hm)
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cast_one] at h
  exact toNat_bit (bool_cases h)

theorem bits15 : ∀ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 → o.2.2.2 ≤ 1 := by
  intro o ho hb
  rcases (segMP_occ ho).2.1 hb with ⟨-, r, hr, h⟩ | ⟨r, hr, h | h⟩
  · rw [h]; exact memb_p8_bit H hr
  · subst h; exact toNat_bit (mpm_row H hr).2.2.2.1
  · subst h; exact toNat_bit (mpm_row H hr).2.2.2.2.2.1

/-- **A node row's message is received by a parent.** -/
theorem node_send_recv {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) (ht : mc tr r 1 = 0) :
    ∃ q, q < tr.height 20 ∧ ((mc tr q 6 = 1 ∧ recvNL tr q = sendN tr r) ∨ (mc tr q 8 = 1 ∧ recvNR tr q = sendN tr r)) := by
  have ho := mpm_occ (nloc := nloc) (ngl := ngl) hr (mpm_in17 tr pub r).2.2
  have hc : (mc tr r 0 - mc tr r 1).toNat = 1 := by rw [ha, ht]; decide
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 17 (fun o ho hb _ => bits17 H o ho hb) ho rfl rfl hc
  obtain ⟨q, hq, h | h | h⟩ := (segMP_occ ho').1 hb'
  · subst h; simp only at hm' hc'
    exact ⟨q, hq, Or.inl ⟨toNat_ne_zero_bit (mpm_row H hq).2.2.2.2.1 hc', hm'⟩⟩
  · subst h; simp only at hm' hc'
    exact ⟨q, hq, Or.inr ⟨toNat_ne_zero_bit (mpm_row H hq).2.2.2.2.2.2.1 hc', hm'⟩⟩
  · subst h; simp at hs'

/-- **A touched node child is some row's message.** -/
theorem node_recv_send {q : Nat} (hq : q < tr.height 20) :
    (mc tr q 6 = 1 → ∃ r, r < tr.height 20 ∧ mc tr r 0 = 1 ∧ mc tr r 1 = 0 ∧ sendN tr r = recvNL tr q) ∧
    (mc tr q 8 = 1 → ∃ r, r < tr.height 20 ∧ mc tr r 0 = 1 ∧ mc tr r 1 = 0 ∧ sendN tr r = recvNR tr q) := by
  have go : ∀ m c, (17, false, m, c) ∈ rowOccsT MpathMP.table tr pub 20 q → c = 1 →
      ∃ r, r < tr.height 20 ∧ mc tr r 0 = 1 ∧ mc tr r 1 = 0 ∧ sendN tr r = m := by
    intro m c hm hc
    subst hc
    obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_send H 17 (fun o ho hb _ => bits17 H o ho hb)
      (mpm_occ (nloc := nloc) (ngl := ngl) hq hm) rfl rfl rfl
    obtain ⟨r, hr, h | h | h⟩ := (segMP_occ ho').1 hb' <;> subst h <;> simp only at hs' hm' hc'
    · exact absurd hs' (by decide)
    · exact absurd hs' (by decide)
    · have := (sub_bit H hr).2 (toNat_ne_zero_bit (sub_bit H hr).1 hc')
      exact ⟨r, hr, this.1, this.2, hm'⟩
  refine ⟨fun h6 => go _ _ (mpm_in17 tr pub q).1 (by rw [h6]; rfl),
    fun h8 => go _ _ (mpm_in17 tr pub q).2.1 (by rw [h8]; rfl)⟩

/-- **A touched leaf child is a bus-15 send** (MEMB's padding row). -/
theorem leaf_recv_send {q : Nat} (hq : q < tr.height 20) :
    (mc tr q 5 = 1 → ∃ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 ∧ o.2.1 = true ∧ o.2.2.1 = recvLL tr q ∧ o.2.2.2 ≠ 0) ∧
    (mc tr q 7 = 1 → ∃ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 ∧ o.2.1 = true ∧ o.2.2.1 = recvLR tr q ∧ o.2.2.2 ≠ 0) := by
  refine ⟨fun h5 => ?_, fun h7 => ?_⟩
  · have hm := (mpm_in15 tr pub q).1
    rw [h5] at hm
    exact recv_has_send H 15 (fun o ho hb _ => bits15 H o ho hb) (mpm_occ (nloc := nloc) (ngl := ngl) hq hm) rfl rfl rfl
  · have hm := (mpm_in15 tr pub q).2
    rw [h7] at hm
    exact recv_has_send H 15 (fun o ho hb _ => bits15 H o ho hb) (mpm_occ (nloc := nloc) (ngl := ngl) hq hm) rfl rfl rfl

/-- **Every leaf message (bus-15 send with count 1) is received by a node row at level 1.** -/
theorem leaf_send_recv {o : Occ} (ho : o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub) (hb : o.1 = 15)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ q, q < tr.height 20 ∧ ((mc tr q 5 = 1 ∧ recvLL tr q = o.2.2.1) ∨ (mc tr q 7 = 1 ∧ recvLR tr q = o.2.2.1)) := by
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 15 (fun o ho hb _ => bits15 H o ho hb) ho hb hs hc
  rcases (segMP_occ ho').2.1 hb' with ⟨h, -⟩ | ⟨q, hq, h | h⟩
  · rw [hs'] at h; exact absurd h (by decide)
  · subst h; exact ⟨q, hq, Or.inl ⟨toNat_ne_zero_bit (mpm_row H hq).2.2.2.1 hc', hm'⟩⟩
  · subst h; exact ⟨q, hq, Or.inr ⟨toNat_ne_zero_bit (mpm_row H hq).2.2.2.2.2.1 hc', hm'⟩⟩

theorem segb_h0 : 0 < tr.height 0 := by
  have := H.heightPos 0 (segMP_lt nloc ngl 0 (by decide)); omega

/-- **RCH.**  A root's `[1] ++ pn` is SEGB's `[nbt] ++ memOut`; SEGB's `[0] ++ memIn` is received
by SEGB itself (`nbt = 0`, `memOut = memIn`) or by a root (`po = memIn`). -/
theorem rch_root {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 1 = 1) :
    tr.cell 0 0 3 = 1 ∧ mdig tr r 103 = pubDig pub pubMemOut := by
  have hm := (mpm_in16 tr pub r).2
  rw [ht] at hm
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 16 (fun o ho hb _ => bits16 H o ho hb)
    (mpm_occ (nloc := nloc) (ngl := ngl) hr hm) rfl rfl rfl
  rcases (segMP_occ ho').2.2 hb' with ⟨r', -, h | h⟩ | ⟨q, hq, h | h⟩
  · subst h; simp at hs'
  · subst h
    simp only at hm' hc'
    by_cases e : r' = 0
    · subst e
      obtain ⟨h1, h2⟩ := cons_append_inj hm'
      exact ⟨h1, h2.symm⟩
    · simp only [e, ite_false] at hc'; exact absurd (by decide) hc'
  · subst h
    simp only at hm'
    exact absurd (cons_append_inj hm').1 (by decide)
  · subst h; simp at hs'

theorem rch_in :
    (tr.cell 0 0 3 = 0 ∧ pubDig pub pubMemIn = pubDig pub pubMemOut) ∨
    (∃ q, q < tr.height 20 ∧ mc tr q 1 = 1 ∧ mdig tr q 85 = pubDig pub pubMemIn) := by
  have ho := mem_occs_of_rowOccsT (segMP_lt nloc ngl 0 (by decide)) (segb_h0 H) (by rw [segMP_t0']; exact segb_in16 tr pub)
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recv H 16 (fun o ho hb _ => bits16 H o ho hb) ho rfl rfl rfl
  rcases (segMP_occ ho').2.2 hb' with ⟨r', -, h | h⟩ | ⟨q, hq, h | h⟩
  · subst h; simp at hs'
  · subst h
    simp only at hm' hc'
    by_cases e : r' = 0
    · subst e
      obtain ⟨h1, h2⟩ := cons_append_inj hm'
      exact Or.inl ⟨h1, h2.symm⟩
    · simp only [e, ite_false] at hc'; exact absurd (by decide) hc'
  · subst h
    simp only at hm' hc'
    exact Or.inr ⟨q, hq, toNat_ne_zero_bit (mpm_row H hq).2.1 hc', (cons_append_inj hm').2⟩
  · subst h; simp at hs'

/-- **At most one root.** -/
theorem root_unique {r r' : Nat} (hr : r < tr.height 20) (hr' : r' < tr.height 20) (ht : mc tr r 1 = 1)
    (ht' : mc tr r' 1 = 1) : r = r' := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨n1, e1⟩ := rch_root H hr ht
  obtain ⟨-, e2⟩ := rch_root H hr' ht'
  have hm := (mpm_in16 tr pub r).2
  have hm' := (mpm_in16 tr pub r').2
  rw [ht] at hm; rw [ht', e2, ← e1] at hm'
  have h20 := segMP_lt nloc ngl 20 (by decide)
  have two := two_le_busNat' h20 hr hr' hne (by rw [segMP_t20']; exact hm) (by rw [segMP_t20']; exact hm')
  have one : busNat (wasmBaseSegAirMP nloc ngl) tr pub 16 false ([1] ++ mdig tr r 103) ≤
      rowCnt (wasmBaseSegAirMP nloc ngl) tr pub 16 false ([1] ++ mdig tr r 103) 0 0 (segMP_lt nloc ngl 0 (by decide)) := by
    apply busNat_le_row
    intro t ht r1 hr1 hne1
    rw [rowCnt_filter_bus]
    by_cases h0 : t = 0
    · subst h0
      have hr1 : r1 ≠ 0 := by omega
      simp only [segMP_t0', segb_rch, List.map_cons, List.map_nil, cntM_cons, cntM_nil, segb_first_eval, hr1]
      simp <;> intros <;> decide
    by_cases h20' : t = 20
    · subst h20'
      simp only [segMP_t20', mpm_occ16_row, cntM_cons, cntM_nil]
      have : ¬ ([0] ++ mdig tr r1 85 = [1] ++ mdig tr r 103) := by
        intro h; exact absurd (cons_append_inj h).1 (by decide)
      simp only [this, false_and, and_false, ite_false]
      simp <;> intro h <;> exact absurd h (by decide)
    by_cases h19 : t = 19
    · subst h19
      rw [List.filter_eq_nil_iff.mpr (by
        intro i hi; have := List.all_eq_true.mp memb_bus i (by rw [← segMP_t19' nloc ngl]; exact hi)
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this; simpa using this.1.1)]
      rfl
    rw [List.filter_eq_nil_iff.mpr (by
      intro i hi; simpa using (segMP_bus_other nloc ngl t ht h0 h19 h20' i hi).2.1)]
    rfl
  have hle : rowCnt (wasmBaseSegAirMP nloc ngl) tr pub 16 false ([1] ++ mdig tr r 103) 0 0
      (segMP_lt nloc ngl 0 (by decide)) ≤ 1 := by
    rw [rowCnt_filter_bus]
    have t1 : Fp.toNat 1 = 1 := by decide
    simp only [segMP_t0', segb_rch, List.map_cons, List.map_nil, cntM_cons, cntM_nil, segb_first_eval, ite_true]
    simp only [Bool.true_eq_false, false_and, and_false, ite_false, t1]
    split <;> omega
  exact no_double H 16 (bits16 H) _ two (by omega)

end bus

end WasmBase
