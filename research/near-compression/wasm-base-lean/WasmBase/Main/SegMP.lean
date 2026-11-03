import WasmBase.SegAirMP
import WasmBase.Main.SegMpath
import WasmBase.Main.BusCount
import WasmBase.Main.SegHoldsX
/-!
# WasmBase.Main.SegMP — the multiproof MPATH of `wasmBaseSegAirMP` (E2E M4b)

`wasmBaseSegAirMP` (`WasmBase/SegAirMP.lean`) is `wasmBaseSegAir` with table 20 replaced by a
batched Merkle multiproof: one row per touched tree node `(lvl, idx)`, with per child a touched-leaf
flag `lfX` (bus 15, MEMB's `[blk, ro, hoI, hoO]`), a touched-node flag `ndX` (the new node bus 17)
or an untouched witness digest used for both trees.  This file proves, **at bus level**, what the
table computes.

## Main statement

**`mp_tree`**: on a `wasmBaseSegAirMP` trace satisfying `HoldsX` (`Main/SegHoldsX.lean`: every
constraint, every bus balanced except the native chip's bus 103 — `Holds` of a segment AIR is
unsatisfiable, `seg_holds_false`, so nothing here is stated from `Holds`) with public depth `D ≤ 30`, given the node
compression as a hypothesis function `node` on the 18-limb digests (`chipO`: every active row's old
output `po = node oL oR`; `chipN`: its new output `pn = node nL nR` unless `ro`), there is a
partial tree `T : PTree` with
* `T.At D 0` — `T` sits at the root position of a depth-`D` binary tree (leaves are block
  indices, stubs stand for untouched subtrees, nodes at `(k, n)` have children at `(k−1, 2n)`,
  `(k−1, 2n+1)`); its leaves are distinct (`PTree.At_nodup`) and lie in `[0, 2^D)` (`PTree.At_leaves`);
* `memIn = T.eval node leafOld` and `memOut = T.eval node leafNew` — the **same** tree (same
  stubs), with the old resp. new leaf digests;
* every leaf `i` of `T` is a bus-15 message `[i, ρ] ++ leafOld i ++ leafNew i` sent with a
  nonzero count (the only bus-15 sender is MEMB's padding row: `memb_bus`, `segMP_occ`);
* every bus-15 message sent with count 1 is such a leaf of `T`.

So a later collision-resistance argument can compare `T` with the full memory tree: if
`T.eval node leafOld = root(M_in)` then (CR) each stub is the full tree's node at its position and
each `leafOld i` is block `i`'s leaf; then `T.eval node leafNew` is the root of `M_in` with the
touched blocks replaced.

## How (the soundness sketch of `SegAirMP.lean`, formally)

* `mpm_row`, `mpm_limbs`, `mpm_level`: the row constraints (booleans, untouched ⇒ `n = o`,
  `ro` ⇒ unchanged, `lvl = 1 + a`, `D = 1 + a + b` from the 5-bit columns).
* `segMP_occ`: every occurrence on buses 15, 16, 17 (only SEGB, MEMB, MPATH use them).
* `rch_root`, `rch_in`, **`root_unique`**: on RCH a root's `[1] ++ pn` is SEGB's
  `[nbt] ++ memOut`; SEGB's `[0] ++ memIn` is a root's `[0] ++ po` (or `memOut = memIn` with no
  root); two roots would send `[1] ++ memOut` twice against SEGB's single receive.
* `pos_of_act`: every active row is at a position `(ℓ, n)`, `1 ≤ ℓ ≤ D`, `n < 2^(D−ℓ)`
  (`Pos`): a non-root row's message is received by a parent one level up (`parent_of`).
* **`pos_unique`**: at most one row per position (two would send one message twice; only the unique
  parent's one side receives it — the counting is `Main/BusCount.lean`'s `two_le_busNat'` /
  `busNat_le_row`, exact by the bit counts on bus 17).
* `mpTree`: the tree read off the rows (`rowAt`: the row at a position); `mpTree_eval`: the subtree
  of a row evaluates to its `po` (old leaves) and `pn` (new leaves); `mpTree_leaves`,
  `mpTree_sub`, `exists_root`: its leaves are exactly the touched leaf children.

## Named hypotheses, domain conditions, open

* `node`, `chipO`, `chipN`: the SHA-384 node compression on MPATH's limbs — the chip contract
  (sub-lane S2 instantiates it with lane B's `Sha512If`).
* `hD : D ≤ 30` (the verifier fixes `D = 16`): positions are naturals `< 2^30 < p`.
* Not here: MEMB's side (each leaf message's digests are the SHA-384 of the block's bytes) and the
  CR comparison with the full memory tree.
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
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
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

/-- With bit counts on both sides of a bus other than the chip's, `busNat` send `≥ 2` and receive
`≤ 1` is impossible. -/
theorem no_double {A : Air} {tr : Trace} {pub : List F} (H : HoldsX A pub tr) (b : Nat) (hx : b ≠ extBus)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.2.2 ≤ 1) (m : List F)
    (h2 : 2 ≤ busNat A tr pub b true m) (h1 : busNat A tr pub b false m ≤ 1) : False := by
  have := perm_exactX H b hx hbit m
  omega

/-- `send_has_recv` for `HoldsX` (a bus other than the chip's). -/
theorem send_has_recvX {A : Air} {tr : Trace} {pub : List F} (H : HoldsX A pub tr) (b : Nat) (hx : b ≠ extBus)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ o' ∈ occs A tr pub, o'.1 = b ∧ o'.2.1 = false ∧ o'.2.2.1 = o.2.2.1 ∧ o'.2.2.2 ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have h0 : busNat A tr pub b false o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' =>
      Classical.byContradiction fun hc' => hn ⟨o', ho', hb', hs', hm', hc'⟩
  have hbal := H.balance b o.2.2.1 hx
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltX H b true o.2.2.1 hbit
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

/-- `recv_has_send` for `HoldsX` (a bus other than the chip's). -/
theorem recv_has_sendX {A : Air} {tr : Trace} {pub : List F} (H : HoldsX A pub tr) (b : Nat) (hx : b ≠ extBus)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = false) (hc : o.2.2.2 = 1) :
    ∃ o' ∈ occs A tr pub, o'.1 = b ∧ o'.2.1 = true ∧ o'.2.2.1 = o.2.2.1 ∧ o'.2.2.2 ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have h0 : busNat A tr pub b true o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' =>
      Classical.byContradiction fun hc' => hn ⟨o', ho', hb', hs', hm', hc'⟩
  have hbal := H.balance b o.2.2.1 hx
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltX H b false o.2.2.1 hbit
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hlt] at hbal
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
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
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
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recvX H 17 (by decide) (fun o ho hb _ => bits17 H o ho hb) ho rfl rfl hc
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
    obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_sendX H 17 (by decide) (fun o ho hb _ => bits17 H o ho hb)
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
    exact recv_has_sendX H 15 (by decide) (fun o ho hb _ => bits15 H o ho hb) (mpm_occ (nloc := nloc) (ngl := ngl) hq hm) rfl rfl rfl
  · have hm := (mpm_in15 tr pub q).2
    rw [h7] at hm
    exact recv_has_sendX H 15 (by decide) (fun o ho hb _ => bits15 H o ho hb) (mpm_occ (nloc := nloc) (ngl := ngl) hq hm) rfl rfl rfl

/-- **Every leaf message (bus-15 send with count 1) is received by a node row at level 1.** -/
theorem leaf_send_recv {o : Occ} (ho : o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub) (hb : o.1 = 15)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ q, q < tr.height 20 ∧ ((mc tr q 5 = 1 ∧ recvLL tr q = o.2.2.1) ∨ (mc tr q 7 = 1 ∧ recvLR tr q = o.2.2.1)) := by
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recvX H 15 (by decide) (fun o ho hb _ => bits15 H o ho hb) ho hb hs hc
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
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recvX H 16 (by decide) (fun o ho hb _ => bits16 H o ho hb)
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
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := send_has_recvX H 16 (by decide) (fun o ho hb _ => bits16 H o ho hb) ho rfl rfl rfl
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
  exact no_double H 16 (by decide) (bits16 H) _ two (by omega)

end bus

/-! ## Positions: every active row is a node `(ℓ, n)` below the root, and at most one row per node -/

theorem mdig_len (tr : Trace) (r b : Nat) : (mdig tr r b).length = 18 := by simp [mdig]

theorem msg_split {a b c d : F} {l1 l2 l3 l4 : List F} (h1 : l1.length = 18) (h3 : l3.length = 18)
    (h : [a, b] ++ l1 ++ l2 = [c, d] ++ l3 ++ l4) : a = c ∧ b = d ∧ l1 = l3 ∧ l2 = l4 := by
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨ha, hb, h⟩ := h
  obtain ⟨h1', h2'⟩ := List.append_inj h (by rw [h1, h3])
  exact ⟨ha, hb, h1', h2'⟩

/-- The depth as a natural. -/
abbrev Dn (pub : List F) : Nat := (pD pub).toNat

theorem cast_inj_small {a b : Nat} (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) (h : (a : F) = (b : F)) : a = b :=
  natEq h (by rw [P_val]; omega) (by rw [P_val]; omega)

/-- `ℓ` and `n` of a node row: active, `lvl = ℓ`, `idx = n`, `1 ≤ ℓ ≤ D`, `n < 2^(D − ℓ)`. -/
def Pos (tr : Trace) (pub : List F) (r ℓ n : Nat) : Prop :=
  r < tr.height 20 ∧ mc tr r 0 = 1 ∧ mc tr r 3 = ((ℓ : Nat) : F) ∧ mc tr r 4 = ((n : Nat) : F) ∧ 1 ≤ ℓ ∧ ℓ ≤ Dn pub ∧
    n < 2 ^ (Dn pub - ℓ)

section pos
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

theorem lvl_nat {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) :
    ∃ a b : Nat, a < 32 ∧ b < 32 ∧ mc tr r 3 = ((1 + a : Nat) : F) ∧ Dn pub = 1 + a + b := by
  obtain ⟨a, b, ha', hb', h3, hD⟩ := mpm_level H hr ha
  refine ⟨a, b, ha', hb', h3, ?_⟩
  unfold Dn; rw [hD, Fp.toNat_cast_of_lt (by rw [P_val]; omega)]

theorem act_of_nd {q : Nat} (hq : q < tr.height 20) (h : mc tr q 6 = 1 ∨ mc tr q 8 = 1 ∨ mc tr q 5 = 1 ∨ mc tr q 7 = 1) :
    mc tr q 0 = 1 := by
  obtain ⟨b0, -, -, -, -, -, -, hz, -⟩ := mpm_row H hq
  rcases b0 with h0 | h0
  · obtain ⟨-, -, z5, z6, z7, z8⟩ := hz h0
    rcases h with h | h | h | h
    · rw [z6] at h; exact absurd h (by decide)
    · rw [z8] at h; exact absurd h (by decide)
    · rw [z5] at h; exact absurd h (by decide)
    · rw [z7] at h; exact absurd h (by decide)
  · exact h0

/-- The parent of a non-root row: level `+1`, child index `2·idx_q + s`. -/
theorem parent_of {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) (ht : mc tr r 1 = 0) :
    ∃ q s, q < tr.height 20 ∧ mc tr q 0 = 1 ∧ s ≤ 1 ∧ mc tr q 3 = mc tr r 3 + 1 ∧
      mc tr r 4 = ((2 : Nat) : F) * mc tr q 4 + ((s : Nat) : F) ∧
      ((s = 0 ∧ mc tr q 6 = 1 ∧ recvNL tr q = sendN tr r) ∨ (s = 1 ∧ mc tr q 8 = 1 ∧ recvNR tr q = sendN tr r)) := by
  obtain ⟨q, hq, h | h⟩ := node_send_recv H hr ha ht
  · obtain ⟨h6, hm⟩ := h
    obtain ⟨e3, e4, -, -⟩ := msg_split (mdig_len tr q 13) (mdig_len tr r 85) hm
    refine ⟨q, 0, hq, act_of_nd H hq (Or.inl h6), by omega, by grind, ?_, Or.inl ⟨rfl, h6, hm⟩⟩
    rw [← e4]; simp only [cast_zero]; grind
  · obtain ⟨h8, hm⟩ := h
    obtain ⟨e3, e4, -, -⟩ := msg_split (mdig_len tr q 49) (mdig_len tr r 85) hm
    refine ⟨q, 1, hq, act_of_nd H hq (Or.inr (Or.inl h8)), by omega, by grind, ?_, Or.inr ⟨rfl, h8, hm⟩⟩
    rw [← e4, cast_one]

/-- A row at level `D` is the root. -/
theorem top_of_lvlD {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) (hl : mc tr r 3 = ((Dn pub : Nat) : F)) :
    mc tr r 1 = 1 := by
  rcases (mpm_row H hr).2.1 with ht | ht
  · obtain ⟨q, s, hq, hqa, -, hq3, -, -⟩ := parent_of H hr ha ht
    obtain ⟨a, b, ha', hb, h3, hD⟩ := lvl_nat H hq hqa
    rw [h3, hl, ← cast_one, ← Lean.Grind.Semiring.natCast_add] at hq3
    have := cast_inj_small (by omega) (by omega) hq3
    omega
  · exact ht

/-- The root has `lvl = D`. -/
theorem lvl_of_top {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 1 = 1) :
    mc tr r 3 = ((Dn pub : Nat) : F) ∧ mc tr r 4 = 0 := by
  obtain ⟨h3, h4⟩ := (mpm_row H hr).2.2.2.2.2.2.2.2.2.2.2.2 ht
  refine ⟨?_, h4⟩
  rw [h3]; unfold Dn; rw [Fp.cast_toNat]

/-- **Every active row has a position.** -/
theorem pos_of_act (hD : Dn pub ≤ 30) {r : Nat} (hr : r < tr.height 20) (ha : mc tr r 0 = 1) :
    ∃ ℓ n, Pos tr pub r ℓ n := by
  have main : ∀ k r, r < tr.height 20 → mc tr r 0 = 1 → mc tr r 3 = ((Dn pub - k : Nat) : F) → k + 1 ≤ Dn pub →
      ∃ n, n < 2 ^ k ∧ mc tr r 4 = ((n : Nat) : F) := by
    intro k
    induction k with
    | zero =>
      intro r hr ha hl _
      have ht := top_of_lvlD H hr ha (by simpa using hl)
      exact ⟨0, by decide, (lvl_of_top H hr ht).2⟩
    | succ k ih =>
      intro r hr ha hl hk
      rcases (mpm_row H hr).2.1 with ht | ht
      · obtain ⟨q, s, hq, hqa, hs, hq3, hq4, -⟩ := parent_of H hr ha ht
        have hql : mc tr q 3 = ((Dn pub - k : Nat) : F) := by
          rw [hq3, hl, ← cast_one, ← Lean.Grind.Semiring.natCast_add]; congr 1; omega
        obtain ⟨nq, hnq, e⟩ := ih q hq hqa hql (by omega)
        refine ⟨2 * nq + s, by rw [Nat.pow_succ]; omega, ?_⟩
        rw [hq4, e]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
      · have h3 := (lvl_of_top H hr ht).1
        rw [hl] at h3
        have := cast_inj_small (by omega) (by omega) h3
        omega
  obtain ⟨a, b, ha', hb', h3, hDn⟩ := lvl_nat H hr ha
  obtain ⟨n, hn, e⟩ := main b r hr ha (by rw [h3]; congr 1; omega) (by omega)
  exact ⟨1 + a, n, hr, ha, h3, e, by omega, by omega, by rw [show Dn pub - (1 + a) = b by omega]; exact hn⟩

omit H in
theorem pos_lvl_inj (hD : Dn pub ≤ 30) {r ℓ ℓ' n : Nat} (hp : Pos tr pub r ℓ n) (h : mc tr r 3 = ((ℓ' : Nat) : F))
    (hl' : ℓ' ≤ 30) : ℓ = ℓ' := by
  obtain ⟨-, -, h3, -, -, hle, -⟩ := hp
  rw [h3] at h
  exact cast_inj_small (by omega) (by omega) h

omit H in
theorem pos_idx_inj (hD : Dn pub ≤ 30) {r ℓ n n' : Nat} (hp : Pos tr pub r ℓ n) (h : mc tr r 4 = ((n' : Nat) : F))
    (hn' : n' < 2 ^ 30) : n = n' := by
  obtain ⟨-, -, -, h4, h1, hle, hn⟩ := hp
  rw [h4] at h
  have : 2 ^ (Dn pub - ℓ) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
  exact cast_inj_small (by omega) (by omega) h

/-- The parent of a row at `(ℓ, n)`, `ℓ < D`: a row at `(ℓ + 1, n / 2)`, receiving it on side `n % 2`. -/
theorem parent_pos (hD : Dn pub ≤ 30) {r ℓ n : Nat} (hp : Pos tr pub r ℓ n) (hl : ℓ < Dn pub) :
    ∃ q, Pos tr pub q (ℓ + 1) (n / 2) ∧
      ((n % 2 = 0 ∧ mc tr q 6 = 1 ∧ recvNL tr q = sendN tr r) ∨ (n % 2 = 1 ∧ mc tr q 8 = 1 ∧ recvNR tr q = sendN tr r)) := by
  obtain ⟨hr, ha, h3, h4, h1, hle, hn⟩ := hp
  have ht : mc tr r 1 = 0 := by
    rcases (mpm_row H hr).2.1 with ht | ht
    · exact ht
    · have := (lvl_of_top H hr ht).1
      rw [h3] at this
      have := cast_inj_small (by omega) (by omega) this; omega
  obtain ⟨q, s, hq, hqa, hs, hq3, hq4, hside⟩ := parent_of H hr ha ht
  obtain ⟨ℓq, nq, hpq⟩ := pos_of_act H hD hq hqa
  have hlq : ℓq = ℓ + 1 := by
    obtain ⟨-, -, e3, -, -, hle', -⟩ := hpq
    rw [e3, h3, ← cast_one, ← Lean.Grind.Semiring.natCast_add] at hq3
    exact cast_inj_small (by omega) (by omega) hq3
  subst hlq
  have hnq : n = 2 * nq + s := by
    obtain ⟨-, -, -, e4, -, -, hnq⟩ := hpq
    rw [e4, h4] at hq4
    have : 2 ^ (Dn pub - ℓ) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ (Dn pub - ℓ) = 2 * 2 ^ (Dn pub - (ℓ + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    exact cast_inj_small (by omega) (by omega) (by rw [hq4]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul])
  have h2 : n / 2 = nq := by omega
  rw [h2]
  refine ⟨q, hpq, ?_⟩
  rcases hside with ⟨rfl, h6, hm⟩ | ⟨rfl, h8, hm⟩
  · exact Or.inl ⟨by omega, h6, hm⟩
  · exact Or.inr ⟨by omega, h8, hm⟩

end pos

theorem mpm_rowCnt17 (nloc ngl : Nat) (tr : Trace) (pub : List F) (M : List F) (r1 : Nat) :
    rowCnt (wasmBaseSegAirMP nloc ngl) tr pub 17 false M 20 r1 (segMP_lt nloc ngl 20 (by decide)) =
      (if recvNL tr r1 = M then (mc tr r1 6).toNat else 0) + (if recvNR tr r1 = M then (mc tr r1 8).toNat else 0) := by
  rw [rowCnt_filter_bus]
  simp only [segMP_t20', mpm_occ17_row, cntM_cons, cntM_nil]
  simp

theorem rowCnt17_other (nloc ngl : Nat) (tr : Trace) (pub : List F) (M : List F) (t : Nat)
    (ht : t < (wasmBaseSegAirMP nloc ngl).tables.length) (h20 : t ≠ 20) (r1 : Nat) :
    rowCnt (wasmBaseSegAirMP nloc ngl) tr pub 17 false M t r1 ht = 0 := by
  apply rowCnt_zero_of_none
  rintro i hi ⟨hb, -⟩
  by_cases h0 : t = 0
  · subst h0
    rw [segMP_t0'] at hi
    have := List.all_eq_true.mp segb_bus i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.2 hb
  by_cases h19 : t = 19
  · subst h19
    rw [segMP_t19'] at hi
    have := List.all_eq_true.mp memb_bus i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1.2 hb
  exact (segMP_bus_other nloc ngl t ht h0 h19 h20 i hi).2.2 hb

section uniq
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

/-- A row receiving `(ℓ, n)`'s message as a node child sits at `(ℓ + 1, n / 2)`, on side `n % 2`. -/
theorem recv_pos (hD : Dn pub ≤ 30) {r ℓ n r1 : Nat} (hp : Pos tr pub r ℓ n) (hr1 : r1 < tr.height 20)
    (h : (mc tr r1 6 = 1 ∧ recvNL tr r1 = sendN tr r) ∨ (mc tr r1 8 = 1 ∧ recvNR tr r1 = sendN tr r)) :
    Pos tr pub r1 (ℓ + 1) (n / 2) ∧ ((n % 2 = 0 ∧ mc tr r1 6 = 1 ∧ recvNL tr r1 = sendN tr r) ∨
      (n % 2 = 1 ∧ mc tr r1 8 = 1 ∧ recvNR tr r1 = sendN tr r)) := by
  have ha1 : mc tr r1 0 = 1 := act_of_nd H hr1 (by rcases h with h | h; exact Or.inl h.1; exact Or.inr (Or.inl h.1))
  obtain ⟨ℓ1, n1, hp1⟩ := pos_of_act H hD hr1 ha1
  obtain ⟨-, -, h3, h4, h1, hle, hn⟩ := hp
  obtain ⟨-, -, e3, e4, h11, hle1, hn1⟩ := hp1
  have hb : 2 ^ (Dn pub - ℓ1) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
  have hb' : 2 ^ (Dn pub - ℓ) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
  have key : ∀ s : Nat, s ≤ 1 → mc tr r1 3 - 1 = mc tr r 3 → ((2 : Nat) : F) * mc tr r1 4 + ((s : Nat) : F) = mc tr r 4 →
      ℓ1 = ℓ + 1 ∧ n = 2 * n1 + s := by
    intro s hs ha hb2
    rw [e3, h3] at ha
    rw [e4, h4] at hb2
    have hl : ((ℓ1 : Nat) : F) = ((ℓ + 1 : Nat) : F) := by rw [Lean.Grind.Semiring.natCast_add, ← ha]; grind
    have hl' := cast_inj_small (by omega) (by omega) hl
    subst hl'
    have h2 : 2 ^ (Dn pub - ℓ) = 2 * 2 ^ (Dn pub - (ℓ + 1)) := by rw [← Nat.pow_succ']; congr 1; omega
    refine ⟨rfl, cast_inj_small (by omega) (by omega) ?_⟩
    rw [← hb2]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  rcases h with ⟨h6, hm⟩ | ⟨h8, hm⟩
  · obtain ⟨ea, eb, -, -⟩ := msg_split (mdig_len tr r1 13) (mdig_len tr r 85) hm
    obtain ⟨rfl, rfl⟩ := key 0 (by omega) ea (by rw [← eb, cast_zero]; grind)
    refine ⟨⟨hr1, ha1, e3, by rw [e4]; congr 1; omega, h11, hle1, by rw [show (2 * n1 + 0) / 2 = n1 by omega]; exact hn1⟩,
      Or.inl ⟨by omega, h6, hm⟩⟩
  · obtain ⟨ea, eb, -, -⟩ := msg_split (mdig_len tr r1 49) (mdig_len tr r 85) hm
    obtain ⟨rfl, rfl⟩ := key 1 (by omega) ea (by rw [← eb, cast_one])
    refine ⟨⟨hr1, ha1, e3, by rw [e4]; congr 1; omega, h11, hle1, by rw [show (2 * n1 + 1) / 2 = n1 by omega]; exact hn1⟩,
      Or.inr ⟨by omega, h8, hm⟩⟩

/-- **At most one row per node.** -/
theorem pos_unique (hD : Dn pub ≤ 30) : ∀ k r r' ℓ n, Dn pub - ℓ = k → Pos tr pub r ℓ n → Pos tr pub r' ℓ n → r = r' := by
  intro k
  induction k with
  | zero =>
    intro r r' ℓ n hk hp hp'
    have hl : ℓ = Dn pub := by have := hp.2.2.2.2.2.1; omega
    subst hl
    exact root_unique H hp.1 hp'.1 (top_of_lvlD H hp.1 hp.2.1 hp.2.2.1) (top_of_lvlD H hp'.1 hp'.2.1 hp'.2.2.1)
  | succ k ih =>
    intro r r' ℓ n hk hp hp'
    refine Classical.byContradiction fun hne => ?_
    have hl : ℓ < Dn pub := by omega
    obtain ⟨q, hq, hside⟩ := parent_pos H hD hp hl
    obtain ⟨q', hq', hside'⟩ := parent_pos H hD hp' hl
    have hqq : q = q' := ih q q' (ℓ + 1) (n / 2) (by omega) hq hq'
    subst hqq
    -- both send the message the parent receives on side `n % 2`
    have hM : sendN tr r' = sendN tr r := by
      rcases hside with ⟨h2, -, hm⟩ | ⟨h2, -, hm⟩ <;> rcases hside' with ⟨h2', -, hm'⟩ | ⟨h2', -, hm'⟩
      · rw [← hm, ← hm']
      · omega
      · omega
      · rw [← hm, ← hm']
    have h20 := segMP_lt nloc ngl 20 (by decide)
    have c1 : ∀ r0, Pos tr pub r0 ℓ n → (mc tr r0 0 - mc tr r0 1).toNat = 1 := by
      intro r0 hp0
      have ht : mc tr r0 1 = 0 := by
        rcases (mpm_row H hp0.1).2.1 with ht | ht
        · exact ht
        · have := (lvl_of_top H hp0.1 ht).1
          rw [hp0.2.2.1] at this
          have := cast_inj_small (by omega) (by omega) this; omega
      rw [hp0.2.1, ht]; decide
    have m1 := (mpm_in17 tr pub r).2.2
    have m2 := (mpm_in17 tr pub r').2.2
    rw [c1 r hp] at m1; rw [c1 r' hp', hM] at m2
    have two := two_le_busNat' h20 hp.1 hp'.1 hne (by rw [segMP_t20']; exact m1) (by rw [segMP_t20']; exact m2)
    have one : busNat (wasmBaseSegAirMP nloc ngl) tr pub 17 false (sendN tr r) ≤
        rowCnt (wasmBaseSegAirMP nloc ngl) tr pub 17 false (sendN tr r) 20 q h20 := by
      apply busNat_le_row
      intro t ht r1 hr1 hne1
      by_cases e : t = 20
      · subst e
        have hr1q : r1 ≠ q := by omega
        rw [mpm_rowCnt17]
        have z : ∀ c : F, (c = 0 ∨ c = 1) → ¬ c = 1 → c.toNat = 0 := by
          intro c hc hn; rcases hc with h | h
          · rw [h]; rfl
          · exact absurd h hn
        have zL : (if recvNL tr r1 = sendN tr r then (mc tr r1 6).toNat else 0) = 0 := by
          split
          · rename_i hm
            refine z _ (mpm_row H hr1).2.2.2.2.1 fun h6 => hr1q ?_
            exact ih r1 q (ℓ + 1) (n / 2) (by omega) (recv_pos H hD hp hr1 (Or.inl ⟨h6, hm⟩)).1 hq
          · rfl
        have zR : (if recvNR tr r1 = sendN tr r then (mc tr r1 8).toNat else 0) = 0 := by
          split
          · rename_i hm
            refine z _ (mpm_row H hr1).2.2.2.2.2.2.1 fun h8 => hr1q ?_
            exact ih r1 q (ℓ + 1) (n / 2) (by omega) (recv_pos H hD hp hr1 (Or.inr ⟨h8, hm⟩)).1 hq
          · rfl
        rw [zL, zR]
      · exact rowCnt17_other nloc ngl tr pub _ t ht e r1
    have hle : rowCnt (wasmBaseSegAirMP nloc ngl) tr pub 17 false (sendN tr r) 20 q h20 ≤ 1 := by
      rw [mpm_rowCnt17]
      have b6 := toNat_bit (mpm_row H hq.1).2.2.2.2.1
      have b8 := toNat_bit (mpm_row H hq.1).2.2.2.2.2.2.1
      by_cases eL : recvNL tr q = sendN tr r
      · by_cases eR : recvNR tr q = sendN tr r
        · exfalso
          rw [← eR] at eL
          obtain ⟨-, e2, -, -⟩ := msg_split (mdig_len tr q 13) (mdig_len tr q 49) eL
          have : (0 : F) = 1 := by grind
          exact absurd this (by decide)
        · simp only [eL, eR, ite_true, ite_false]; omega
      · simp only [eL, ite_false]; split <;> omega
    exact no_double H 17 (by decide) (bits17 H) _ two (by omega)

end uniq

/-! ## The partial tree -/

/-- **A partial binary Merkle tree**: touched leaves (by index), stubs (a digest standing for an
untouched subtree, the same in the old and the new tree), inner nodes. -/
inductive PTree where
  | leaf (i : Nat)
  | stub (d : List F)
  | node (l r : PTree)

namespace PTree

/-- The root digest, with node compression `h` and leaf digests `lf`. -/
def eval (h : List F → List F → List F) (lf : Nat → List F) : PTree → List F
  | .leaf i => lf i
  | .stub d => d
  | .node l r => h (l.eval h lf) (r.eval h lf)

def leaves : PTree → List Nat
  | .leaf i => [i]
  | .stub _ => []
  | .node l r => l.leaves ++ r.leaves

/-- `T` is the subtree at level `k`, position `n`, of a binary tree with leaves `0 … 2^D − 1` at
level 0 (a leaf sits at its own index; a stub anywhere; a node's children at `(k − 1, 2n)` and
`(k − 1, 2n + 1)`). -/
def At : Nat → Nat → PTree → Prop
  | _, _, .stub _ => True
  | 0, n, .leaf i => i = n
  | k + 1, n, .node l r => At k (2 * n) l ∧ At k (2 * n + 1) r
  | _, _, _ => False

/-- The leaves of a subtree at `(k, n)` are the indices `n·2^k … (n+1)·2^k − 1`. -/
theorem At_leaves : ∀ (k n : Nat) (T : PTree), At k n T → ∀ i ∈ T.leaves, n * 2 ^ k ≤ i ∧ i < (n + 1) * 2 ^ k
  | _, _, .stub _, _ => by simp [leaves]
  | 0, n, .leaf i, h => by simp only [At] at h; subst h; simp [leaves]
  | k + 1, n, .node l r, h => by
    obtain ⟨hl, hr⟩ := h
    intro i hi
    have e1 : n * 2 ^ (k + 1) = 2 * (n * 2 ^ k) := by rw [Nat.pow_succ]; grind
    have e2 : (n + 1) * 2 ^ (k + 1) = 2 * (n * 2 ^ k) + 2 * 2 ^ k := by rw [Nat.pow_succ]; grind
    have e3 : (2 * n) * 2 ^ k = 2 * (n * 2 ^ k) := by grind
    have e4 : (2 * n + 1) * 2 ^ k = 2 * (n * 2 ^ k) + 2 ^ k := by grind
    have e5 : (2 * n + 1 + 1) * 2 ^ k = 2 * (n * 2 ^ k) + 2 * 2 ^ k := by grind
    rw [e1, e2]
    rcases List.mem_append.mp hi with hi | hi
    · have := At_leaves k (2 * n) l hl i hi
      rw [e3, show 2 * n + 1 = 2 * n + 1 from rfl, e4] at this; omega
    · have := At_leaves k (2 * n + 1) r hr i hi
      rw [e4, e5] at this; omega
  | 0, _, .node _ _, h => by simp [At] at h
  | _ + 1, _, .leaf _, h => by simp [At] at h

/-- The leaves of a positioned partial tree are distinct. -/
theorem At_nodup : ∀ (k n : Nat) (T : PTree), At k n T → T.leaves.Nodup
  | _, _, .stub _, _ => by simp [leaves]
  | 0, n, .leaf i, _ => by simp [leaves]
  | k + 1, n, .node l r, h => by
    obtain ⟨hl, hr⟩ := h
    simp only [leaves]
    refine List.nodup_append.mpr ⟨At_nodup k _ l hl, At_nodup k _ r hr, ?_⟩
    intro a ha b hb hab
    subst hab
    have h1 := At_leaves k _ l hl a ha
    have h2 := At_leaves k _ r hr a hb
    have e3 : (2 * n) * 2 ^ k = 2 * (n * 2 ^ k) := by grind
    have e4 : (2 * n + 1) * 2 ^ k = 2 * (n * 2 ^ k) + 2 ^ k := by grind
    have e5 : (2 * n + 1 + 1) * 2 ^ k = 2 * (n * 2 ^ k) + 2 * 2 ^ k := by grind
    rw [e3, e4] at h1; rw [e4, e5] at h2
    omega
  | 0, _, .node _ _, h => by simp [At] at h
  | _ + 1, _, .leaf _, h => by simp [At] at h

end PTree

open Classical in
/-- The row at node `(ℓ, n)`, if any (unique by `pos_unique`). -/
noncomputable def rowAt (tr : Trace) (pub : List F) (ℓ n : Nat) : Option Nat :=
  if h : ∃ r, Pos tr pub r ℓ n then some (Classical.choose h) else none

/-- **The partial tree of the MPATH rows**: at `(ℓ + 1, n)` the row's node, a touched child is the
subtree one level down (a leaf at level 0), an untouched child the stub of its witness digest. -/
noncomputable def mpTree (tr : Trace) (pub : List F) : Nat → Nat → PTree
  | 0, n => .leaf n
  | ℓ + 1, n =>
    match rowAt tr pub (ℓ + 1) n with
    | none => .stub []
    | some r =>
      .node (if mc tr r 5 = 1 ∨ mc tr r 6 = 1 then mpTree tr pub ℓ (2 * n) else .stub (mdig tr r 13))
        (if mc tr r 7 = 1 ∨ mc tr r 8 = 1 then mpTree tr pub ℓ (2 * n + 1) else .stub (mdig tr r 49))

/-- The old / new leaf digests: those the level-1 row receives (MEMB's `hoI` / `hoO`). -/
noncomputable def leafOld (tr : Trace) (pub : List F) (i : Nat) : List F :=
  match rowAt tr pub 1 (i / 2) with
  | some r => if i % 2 = 0 then mdig tr r 13 else mdig tr r 49
  | none => []
noncomputable def leafNew (tr : Trace) (pub : List F) (i : Nat) : List F :=
  match rowAt tr pub 1 (i / 2) with
  | some r => if i % 2 = 0 then mdig tr r 31 else mdig tr r 67
  | none => []

theorem mpTree_At (tr : Trace) (pub : List F) : ∀ ℓ n, (mpTree tr pub ℓ n).At ℓ n
  | 0, n => by simp [mpTree, PTree.At]
  | ℓ + 1, n => by
    simp only [mpTree]
    split
    · simp [PTree.At]
    · simp only [PTree.At]
      constructor
      · split
        · exact mpTree_At tr pub ℓ (2 * n)
        · simp [PTree.At]
      · split
        · exact mpTree_At tr pub ℓ (2 * n + 1)
        · simp [PTree.At]

section tree
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

theorem rowAt_eq (hD : Dn pub ≤ 30) {r ℓ n : Nat} (hp : Pos tr pub r ℓ n) : rowAt tr pub ℓ n = some r := by
  have h : ∃ r, Pos tr pub r ℓ n := ⟨r, hp⟩
  unfold rowAt
  rw [dif_pos h]
  congr 1
  exact pos_unique H hD _ _ _ ℓ n rfl (Classical.choose_spec h) hp

theorem mpTree_eq (hD : Dn pub ≤ 30) {r ℓ n : Nat} (hp : Pos tr pub r (ℓ + 1) n) :
    mpTree tr pub (ℓ + 1) n =
      .node (if mc tr r 5 = 1 ∨ mc tr r 6 = 1 then mpTree tr pub ℓ (2 * n) else .stub (mdig tr r 13))
        (if mc tr r 7 = 1 ∨ mc tr r 8 = 1 then mpTree tr pub ℓ (2 * n + 1) else .stub (mdig tr r 49)) := by
  conv => lhs; unfold mpTree
  rw [rowAt_eq H hD hp]

/-- A touched child of a row at `(ℓ, n)`: a leaf iff `ℓ = 1`; a node child is a row at `(ℓ − 1, 2n + s)`
whose message is the one received. -/
theorem child_cases (hD : Dn pub ≤ 30) {r ℓ n : Nat} (hp : Pos tr pub r ℓ n) :
    (mc tr r 5 = 1 → ℓ = 1) ∧ (mc tr r 7 = 1 → ℓ = 1) ∧
    (mc tr r 6 = 1 → ∃ c, 2 ≤ ℓ ∧ Pos tr pub c (ℓ - 1) (2 * n) ∧ sendN tr c = recvNL tr r) ∧
    (mc tr r 8 = 1 → ∃ c, 2 ≤ ℓ ∧ Pos tr pub c (ℓ - 1) (2 * n + 1) ∧ sendN tr c = recvNR tr r) := by
  obtain ⟨hr, ha, h3, h4, h1, hle, hn⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, l5, l7, -⟩ := mpm_row H hr
  have hb : 2 ^ (Dn pub - ℓ) ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
  -- a sender `c` of the received message `[ℓ − 1, 2n + s] ++ …`
  have key : ∀ c s : Nat, s ≤ 1 → c < tr.height 20 → mc tr c 0 = 1 → mc tr c 3 = mc tr r 3 - 1 →
      mc tr c 4 = ((2 : Nat) : F) * mc tr r 4 + ((s : Nat) : F) → 2 ≤ ℓ ∧ Pos tr pub c (ℓ - 1) (2 * n + s) := by
    intro c s hs hc hca e3 e4
    obtain ⟨ℓc, nc, hpc⟩ := pos_of_act H hD hc hca
    obtain ⟨-, -, f3, f4, g1, gle, gn⟩ := hpc
    have hbc : 2 ^ (Dn pub - ℓc) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [f3, h3] at e3
    have hl : ((ℓc + 1 : Nat) : F) = ((ℓ : Nat) : F) := by rw [Lean.Grind.Semiring.natCast_add, e3]; grind
    have hl' := cast_inj_small (by omega) (by omega) hl
    rw [f4, h4] at e4
    have hn' : nc = 2 * n + s := cast_inj_small (by omega) (by omega)
      (by rw [e4]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul])
    subst hn'
    refine ⟨by omega, hc, hca, by rw [f3]; congr 1; omega, f4, by omega, by omega, by rw [show ℓ - 1 = ℓc by omega]; exact gn⟩
  refine ⟨fun h5 => ?_, fun h7 => ?_, fun h6 => ?_, fun h8 => ?_⟩
  · have := l5 h5; rw [h3, ← cast_one] at this; exact cast_inj_small (by omega) (by omega) this
  · have := l7 h7; rw [h3, ← cast_one] at this; exact cast_inj_small (by omega) (by omega) this
  · obtain ⟨c, hc, hca, -, hm⟩ := (node_recv_send H hr).1 h6
    obtain ⟨e3, e4, -, -⟩ := msg_split (mdig_len tr c 85) (mdig_len tr r 13) hm
    obtain ⟨h2, hpc⟩ := key c 0 (by omega) hc hca e3 (by rw [e4, cast_zero]; grind)
    exact ⟨c, h2, hpc, hm⟩
  · obtain ⟨c, hc, hca, -, hm⟩ := (node_recv_send H hr).2 h8
    obtain ⟨e3, e4, -, -⟩ := msg_split (mdig_len tr c 85) (mdig_len tr r 49) hm
    obtain ⟨h2, hpc⟩ := key c 1 (by omega) hc hca e3 (by rw [e4, cast_one])
    exact ⟨c, h2, hpc, hm⟩

/-- **The subtree of a row evaluates to its old and new outputs.** -/
theorem mpTree_eval (hD : Dn pub ≤ 30) (node : List F → List F → List F)
    (chipO : ∀ r, r < tr.height 20 → mc tr r 0 = 1 → mdig tr r 85 = node (mdig tr r 13) (mdig tr r 49))
    (chipN : ∀ r, r < tr.height 20 → mc tr r 0 = 1 → mc tr r 2 = 0 → mdig tr r 103 = node (mdig tr r 31) (mdig tr r 67)) :
    ∀ ℓ r n, Pos tr pub r (ℓ + 1) n →
      (mpTree tr pub (ℓ + 1) n).eval node (leafOld tr pub) = mdig tr r 85 ∧
      (mpTree tr pub (ℓ + 1) n).eval node (leafNew tr pub) = mdig tr r 103 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro r n hp
    obtain ⟨c5, c7, c6, c8⟩ := child_cases H hD hp
    obtain ⟨-, -, -, b5, b6, b7, b8, -⟩ := mpm_row H hp.1
    obtain ⟨u1, u2, u3⟩ := mpm_limbs H hp.1
    have hrow := rowAt_eq H hD hp
    have cL : (if mc tr r 5 = 1 ∨ mc tr r 6 = 1 then mpTree tr pub 0 (2 * n) else .stub (mdig tr r 13)).eval node
        (leafOld tr pub) = mdig tr r 13 ∧
        (if mc tr r 5 = 1 ∨ mc tr r 6 = 1 then mpTree tr pub 0 (2 * n) else .stub (mdig tr r 13)).eval node
        (leafNew tr pub) = mdig tr r 31 := by
      by_cases t : mc tr r 5 = 1 ∨ mc tr r 6 = 1
      · rw [if_pos t]
        rcases t with h5 | h6
        · simp only [mpTree, PTree.eval, leafOld, leafNew, show 2 * n / 2 = n by omega, hrow,
            show 2 * n % 2 = 0 by omega, ite_true]
          refine ⟨?_, ?_⟩ <;> first | trivial | rfl | simp
        · obtain ⟨c, h2, -⟩ := c6 h6; omega
      · rw [if_neg t]
        have h5 : mc tr r 5 = 0 := by rcases b5 with h | h; exact h; exact absurd (Or.inl h) t
        have h6 : mc tr r 6 = 0 := by rcases b6 with h | h; exact h; exact absurd (Or.inr h) t
        exact ⟨rfl, (u1 h5 h6).symm⟩
    have cR : (if mc tr r 7 = 1 ∨ mc tr r 8 = 1 then mpTree tr pub 0 (2 * n + 1) else .stub (mdig tr r 49)).eval node
        (leafOld tr pub) = mdig tr r 49 ∧
        (if mc tr r 7 = 1 ∨ mc tr r 8 = 1 then mpTree tr pub 0 (2 * n + 1) else .stub (mdig tr r 49)).eval node
        (leafNew tr pub) = mdig tr r 67 := by
      by_cases t : mc tr r 7 = 1 ∨ mc tr r 8 = 1
      · rw [if_pos t]
        rcases t with h7 | h8
        · simp only [mpTree, PTree.eval, leafOld, leafNew, show (2 * n + 1) / 2 = n by omega, hrow,
            show (2 * n + 1) % 2 = 1 by omega]
          refine ⟨?_, ?_⟩ <;> first | trivial | rfl | simp
        · obtain ⟨c, h2, -⟩ := c8 h8; omega
      · rw [if_neg t]
        have h7 : mc tr r 7 = 0 := by rcases b7 with h | h; exact h; exact absurd (Or.inl h) t
        have h8 : mc tr r 8 = 0 := by rcases b8 with h | h; exact h; exact absurd (Or.inr h) t
        exact ⟨rfl, (u2 h7 h8).symm⟩
    rw [mpTree_eq H hD hp]
    simp only [PTree.eval]
    rw [cL.1, cR.1, cL.2, cR.2]
    refine ⟨(chipO r hp.1 hp.2.1).symm, ?_⟩
    rcases (mpm_row H hp.1).2.2.1 with h2 | h2
    · exact (chipN r hp.1 hp.2.1 h2).symm
    · obtain ⟨v1, v2, v3⟩ := u3 h2
      rw [v1, v2, v3]; exact (chipO r hp.1 hp.2.1).symm
  | succ ℓ ih =>
    intro r n hp
    obtain ⟨c5, c7, c6, c8⟩ := child_cases H hD hp
    obtain ⟨-, -, -, b5, b6, b7, b8, -⟩ := mpm_row H hp.1
    obtain ⟨u1, u2, u3⟩ := mpm_limbs H hp.1
    have cL : (if mc tr r 5 = 1 ∨ mc tr r 6 = 1 then mpTree tr pub (ℓ + 1) (2 * n) else .stub (mdig tr r 13)).eval node
        (leafOld tr pub) = mdig tr r 13 ∧
        (if mc tr r 5 = 1 ∨ mc tr r 6 = 1 then mpTree tr pub (ℓ + 1) (2 * n) else .stub (mdig tr r 13)).eval node
        (leafNew tr pub) = mdig tr r 31 := by
      by_cases t : mc tr r 5 = 1 ∨ mc tr r 6 = 1
      · rw [if_pos t]
        rcases t with h5 | h6
        · have := c5 h5; omega
        · obtain ⟨c, -, hpc, hm⟩ := c6 h6
          rw [show ℓ + 1 + 1 - 1 = ℓ + 1 by omega] at hpc
          obtain ⟨-, -, f1, f2⟩ := msg_split (mdig_len tr c 85) (mdig_len tr r 13) hm
          rw [(ih c (2 * n) hpc).1, (ih c (2 * n) hpc).2]
          exact ⟨f1, f2⟩
      · rw [if_neg t]
        have h5 : mc tr r 5 = 0 := by rcases b5 with h | h; exact h; exact absurd (Or.inl h) t
        have h6 : mc tr r 6 = 0 := by rcases b6 with h | h; exact h; exact absurd (Or.inr h) t
        exact ⟨rfl, (u1 h5 h6).symm⟩
    have cR : (if mc tr r 7 = 1 ∨ mc tr r 8 = 1 then mpTree tr pub (ℓ + 1) (2 * n + 1) else .stub (mdig tr r 49)).eval node
        (leafOld tr pub) = mdig tr r 49 ∧
        (if mc tr r 7 = 1 ∨ mc tr r 8 = 1 then mpTree tr pub (ℓ + 1) (2 * n + 1) else .stub (mdig tr r 49)).eval node
        (leafNew tr pub) = mdig tr r 67 := by
      by_cases t : mc tr r 7 = 1 ∨ mc tr r 8 = 1
      · rw [if_pos t]
        rcases t with h7 | h8
        · have := c7 h7; omega
        · obtain ⟨c, -, hpc, hm⟩ := c8 h8
          rw [show ℓ + 1 + 1 - 1 = ℓ + 1 by omega] at hpc
          obtain ⟨-, -, f1, f2⟩ := msg_split (mdig_len tr c 85) (mdig_len tr r 49) hm
          rw [(ih c (2 * n + 1) hpc).1, (ih c (2 * n + 1) hpc).2]
          exact ⟨f1, f2⟩
      · rw [if_neg t]
        have h7 : mc tr r 7 = 0 := by rcases b7 with h | h; exact h; exact absurd (Or.inl h) t
        have h8 : mc tr r 8 = 0 := by rcases b8 with h | h; exact h; exact absurd (Or.inr h) t
        exact ⟨rfl, (u2 h7 h8).symm⟩
    rw [mpTree_eq H hD hp]
    simp only [PTree.eval]
    rw [cL.1, cR.1, cL.2, cR.2]
    refine ⟨(chipO r hp.1 hp.2.1).symm, ?_⟩
    rcases (mpm_row H hp.1).2.2.1 with h2 | h2
    · exact (chipN r hp.1 hp.2.1 h2).symm
    · obtain ⟨v1, v2, v3⟩ := u3 h2
      rw [v1, v2, v3]; exact (chipO r hp.1 hp.2.1).symm

end tree

section main
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
include H

omit H in
theorem rowAt_some {ℓ n r : Nat} (h : rowAt tr pub ℓ n = some r) : Pos tr pub r ℓ n := by
  unfold rowAt at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

/-- Every leaf of the tree of `(ℓ + 1, n)` is a touched leaf child of a level-1 row. -/
theorem mpTree_leaves (hD : Dn pub ≤ 30) : ∀ ℓ n, ∀ i ∈ (mpTree tr pub (ℓ + 1) n).leaves,
    ∃ r1 n1, Pos tr pub r1 1 n1 ∧ ((i = 2 * n1 ∧ mc tr r1 5 = 1) ∨ (i = 2 * n1 + 1 ∧ mc tr r1 7 = 1)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro n i hi
    unfold mpTree at hi
    split at hi
    · simp [PTree.leaves] at hi
    · rename_i r hr
      have hp := rowAt_some hr
      obtain ⟨-, -, c6, c8⟩ := child_cases H hD hp
      simp only [PTree.leaves] at hi
      rcases List.mem_append.mp hi with hi | hi
      · split at hi
        · rename_i t
          simp only [mpTree, PTree.leaves, List.mem_singleton] at hi
          rcases t with h5 | h6
          · exact ⟨r, n, hp, Or.inl ⟨hi, h5⟩⟩
          · obtain ⟨c, h2, -⟩ := c6 h6; exact absurd h2 (by decide)
        · simp [PTree.leaves] at hi
      · split at hi
        · rename_i t
          simp only [mpTree, PTree.leaves, List.mem_singleton] at hi
          rcases t with h7 | h8
          · exact ⟨r, n, hp, Or.inr ⟨hi, h7⟩⟩
          · obtain ⟨c, h2, -⟩ := c8 h8; exact absurd h2 (by decide)
        · simp [PTree.leaves] at hi
  | succ ℓ ih =>
    intro n i hi
    unfold mpTree at hi
    split at hi
    · simp [PTree.leaves] at hi
    · simp only [PTree.leaves] at hi
      rcases List.mem_append.mp hi with hi | hi
      · split at hi
        · exact ih _ i hi
        · simp [PTree.leaves] at hi
      · split at hi
        · exact ih _ i hi
        · simp [PTree.leaves] at hi

/-- The leaf message of a touched leaf child (MEMB's `[blk, ro, hoI, hoO]`). -/
theorem leaf_msg (hD : Dn pub ≤ 30) {r1 n1 : Nat} (hp : Pos tr pub r1 1 n1) :
    (mc tr r1 5 = 1 → ∃ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 ∧ o.2.1 = true ∧ o.2.2.2 ≠ 0 ∧
      o.2.2.1 = [((2 * n1 : Nat) : F), mc tr r1 9] ++ leafOld tr pub (2 * n1) ++ leafNew tr pub (2 * n1)) ∧
    (mc tr r1 7 = 1 → ∃ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 ∧ o.2.1 = true ∧ o.2.2.2 ≠ 0 ∧
      o.2.2.1 = [((2 * n1 + 1 : Nat) : F), mc tr r1 10] ++ leafOld tr pub (2 * n1 + 1) ++ leafNew tr pub (2 * n1 + 1)) := by
  have hrow := rowAt_eq H hD hp
  have h4 := hp.2.2.2.1
  refine ⟨fun h5 => ?_, fun h7 => ?_⟩
  · obtain ⟨o, ho, hb, hs, hm, hc⟩ := (leaf_recv_send H hp.1).1 h5
    refine ⟨o, ho, hb, hs, hc, ?_⟩
    rw [hm, recvLL, h4]
    simp only [leafOld, leafNew, show 2 * n1 / 2 = n1 by omega, hrow, show 2 * n1 % 2 = 0 by omega, ite_true,
      Lean.Grind.Semiring.natCast_mul]
  · obtain ⟨o, ho, hb, hs, hm, hc⟩ := (leaf_recv_send H hp.1).2 h7
    refine ⟨o, ho, hb, hs, hc, ?_⟩
    rw [hm, recvLR, h4]
    simp only [leafOld, leafNew, show (2 * n1 + 1) / 2 = n1 by omega, hrow, show (2 * n1 + 1) % 2 = 1 by omega,
      Lean.Grind.Semiring.natCast_mul, Lean.Grind.Semiring.natCast_add, cast_one]
    simp

/-- The leaves below a row are leaves of the whole tree. -/
theorem mpTree_sub (hD : Dn pub ≤ 30) : ∀ k r ℓ n, Dn pub - ℓ = k → Pos tr pub r ℓ n →
    ∀ i ∈ (mpTree tr pub ℓ n).leaves, i ∈ (mpTree tr pub (Dn pub) 0).leaves := by
  intro k
  induction k with
  | zero =>
    intro r ℓ n hk hp i hi
    have hl : ℓ = Dn pub := by have := hp.2.2.2.2.2.1; omega
    have hn : n = 0 := by have := hp.2.2.2.2.2.2; rw [hl, Nat.sub_self] at this; omega
    subst hl; subst hn; exact hi
  | succ k ih =>
    intro r ℓ n hk hp i hi
    have hl : ℓ < Dn pub := by omega
    obtain ⟨q, hq, hside⟩ := parent_pos H hD hp hl
    apply ih q (ℓ + 1) (n / 2) (by omega) hq
    rw [mpTree_eq H hD hq]
    simp only [PTree.leaves]
    rcases hside with ⟨h2, h6, -⟩ | ⟨h2, h8, -⟩
    · apply List.mem_append_left
      rw [ite_cond_eq_true _ _ (eq_true (Or.inr h6)), show 2 * (n / 2) = n by omega]; exact hi
    · apply List.mem_append_right
      rw [ite_cond_eq_true _ _ (eq_true (Or.inr h8)), show 2 * (n / 2) + 1 = n by omega]; exact hi

/-- A row hangs below a root. -/
theorem exists_root (hD : Dn pub ≤ 30) : ∀ k r ℓ n, Dn pub - ℓ = k → Pos tr pub r ℓ n →
    ∃ ρ, ρ < tr.height 20 ∧ mc tr ρ 1 = 1 := by
  intro k
  induction k with
  | zero =>
    intro r ℓ n hk hp
    have hl : ℓ = Dn pub := by have := hp.2.2.2.2.2.1; omega
    subst hl
    exact ⟨r, hp.1, top_of_lvlD H hp.1 hp.2.1 hp.2.2.1⟩
  | succ k ih =>
    intro r ℓ n hk hp
    obtain ⟨q, hq, -⟩ := parent_pos H hD hp (by omega)
    exact ih q (ℓ + 1) (n / 2) (by omega) hq

/-- **The multiproof MPATH, bus level.**  On a `wasmBaseSegAirMP` trace satisfying `HoldsX` with depth
`D ≤ 30`, if every MPATH row's old output is the node compression `node` of its old children (and
its new output of its new children unless `ro`), there is a partial tree `T` at the root position
`(D, 0)` such that
* `memIn` (public) is `T`'s root with the old leaf digests, `memOut` with the new ones (the stubs,
  i.e. the untouched subtrees, are the same in both);
* every leaf `i` of `T` is a bus-15 message `[i, ρ] ++ old_i ++ new_i` (sent by MEMB);
* every bus-15 message sent with count 1 is a leaf of `T`.
`T`'s leaves are distinct (`PTree.At_nodup`). -/
theorem mp_tree (hD : Dn pub ≤ 30) (node : List F → List F → List F)
    (chipO : ∀ r, r < tr.height 20 → mc tr r 0 = 1 → mdig tr r 85 = node (mdig tr r 13) (mdig tr r 49))
    (chipN : ∀ r, r < tr.height 20 → mc tr r 0 = 1 → mc tr r 2 = 0 → mdig tr r 103 = node (mdig tr r 31) (mdig tr r 67)) :
    ∃ T : PTree, T.At (Dn pub) 0 ∧
      T.eval node (leafOld tr pub) = pubDig pub pubMemIn ∧ T.eval node (leafNew tr pub) = pubDig pub pubMemOut ∧
      (∀ i ∈ T.leaves, ∃ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 ∧ o.2.1 = true ∧ o.2.2.2 ≠ 0 ∧
        ∃ ρ, o.2.2.1 = [((i : Nat) : F), ρ] ++ leafOld tr pub i ++ leafNew tr pub i) ∧
      (∀ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 → o.2.1 = true → o.2.2.2 = 1 →
        ∃ i ∈ T.leaves, ∃ ρ, o.2.2.1 = [((i : Nat) : F), ρ] ++ leafOld tr pub i ++ leafNew tr pub i) := by
  -- a touched leaf message is received by a level-1 row
  have recv1 : ∀ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = 15 → o.2.1 = true → o.2.2.2 = 1 →
      ∃ q nq, Pos tr pub q 1 nq ∧ ((mc tr q 5 = 1 ∧ o.2.2.1 = [((2 * nq : Nat) : F), mc tr q 9] ++
        leafOld tr pub (2 * nq) ++ leafNew tr pub (2 * nq)) ∨ (mc tr q 7 = 1 ∧ o.2.2.1 =
        [((2 * nq + 1 : Nat) : F), mc tr q 10] ++ leafOld tr pub (2 * nq + 1) ++ leafNew tr pub (2 * nq + 1))) := by
    intro o ho hb hs hc
    obtain ⟨q, hq, hcase⟩ := leaf_send_recv H ho hb hs hc
    have hqa : mc tr q 0 = 1 := act_of_nd H hq (by
      rcases hcase with h | h; exact Or.inr (Or.inr (Or.inl h.1)); exact Or.inr (Or.inr (Or.inr h.1)))
    obtain ⟨ℓq, nq, hpq⟩ := pos_of_act H hD hq hqa
    obtain ⟨c5, c7, -, -⟩ := child_cases H hD hpq
    have hrow := rowAt_eq H hD hpq
    have h4 := hpq.2.2.2.1
    rcases hcase with ⟨h5, hm⟩ | ⟨h7, hm⟩
    · have := c5 h5; subst this
      refine ⟨q, nq, hpq, Or.inl ⟨h5, ?_⟩⟩
      rw [← hm, recvLL, h4]
      simp only [leafOld, leafNew, show 2 * nq / 2 = nq by omega, hrow, show 2 * nq % 2 = 0 by omega, ite_true,
        Lean.Grind.Semiring.natCast_mul]
    · have := c7 h7; subst this
      refine ⟨q, nq, hpq, Or.inr ⟨h7, ?_⟩⟩
      rw [← hm, recvLR, h4]
      simp only [leafOld, leafNew, show (2 * nq + 1) / 2 = nq by omega, hrow, show (2 * nq + 1) % 2 = 1 by omega,
        Lean.Grind.Semiring.natCast_mul, Lean.Grind.Semiring.natCast_add, cast_one]
      simp
  by_cases hroot : ∃ ρ, ρ < tr.height 20 ∧ mc tr ρ 1 = 1
  · obtain ⟨ρ, hρ, htop⟩ := hroot
    have ha : mc tr ρ 0 = 1 := by
      rcases (mpm_row H hρ).1 with h | h
      · have := ((mpm_row H hρ).2.2.2.2.2.2.2.1 h).1; rw [this] at htop; exact absurd htop (by decide)
      · exact h
    obtain ⟨ℓ, n, hp⟩ := pos_of_act H hD hρ ha
    obtain ⟨l3, l4⟩ := lvl_of_top H hρ htop
    have hl := pos_lvl_inj hD hp l3 hD
    have hn := pos_idx_inj hD hp (by rw [l4]; rfl) (by decide)
    subst hl; subst hn
    have hD1 := hp.2.2.2.2.1
    obtain ⟨d, hd⟩ : ∃ d, Dn pub = d + 1 := ⟨Dn pub - 1, by omega⟩
    obtain ⟨e1, e2⟩ := mpTree_eval H hD node chipO chipN d ρ 0 (by rw [← hd]; exact hp)
    obtain ⟨n1, eo⟩ := rch_root H hρ htop
    have ei : mdig tr ρ 85 = pubDig pub pubMemIn := by
      rcases rch_in H with ⟨h0, -⟩ | ⟨q, hq, hqt, hqi⟩
      · rw [h0] at n1; exact absurd n1 (by decide)
      · rw [← root_unique H hq hρ hqt htop]; exact hqi
    refine ⟨mpTree tr pub (Dn pub) 0, mpTree_At tr pub _ _, by rw [hd, e1, ei], by rw [hd, e2, eo], ?_, ?_⟩
    · intro i hi
      rw [hd] at hi
      obtain ⟨r1, n1, hp1, hcase⟩ := mpTree_leaves H hD d 0 i hi
      rcases hcase with ⟨rfl, h5⟩ | ⟨rfl, h7⟩
      · obtain ⟨o, ho, hb, hs, hc, hm⟩ := (leaf_msg H hD hp1).1 h5
        exact ⟨o, ho, hb, hs, hc, _, hm⟩
      · obtain ⟨o, ho, hb, hs, hc, hm⟩ := (leaf_msg H hD hp1).2 h7
        exact ⟨o, ho, hb, hs, hc, _, hm⟩
    · intro o ho hb hs hc
      obtain ⟨q, nq, hpq, hcase⟩ := recv1 o ho hb hs hc
      have hsub := mpTree_sub H hD _ q 1 nq rfl hpq
      rcases hcase with ⟨h5, hm⟩ | ⟨h7, hm⟩
      · refine ⟨2 * nq, hsub _ ?_, _, hm⟩
        rw [mpTree_eq H hD hpq, if_pos (Or.inl h5)]
        simp [PTree.leaves, mpTree]
      · refine ⟨2 * nq + 1, hsub _ ?_, _, hm⟩
        rw [mpTree_eq H hD hpq, if_pos (Or.inl h7)]
        simp [PTree.leaves, mpTree]
  · have hno : ∀ q nq, ¬ Pos tr pub q 1 nq := fun q nq hp =>
      hroot (exists_root H hD _ q 1 nq rfl hp)
    have heq : pubDig pub pubMemIn = pubDig pub pubMemOut := by
      rcases rch_in H with ⟨-, h⟩ | ⟨q, hq, hqt, -⟩
      · exact h
      · exact absurd ⟨q, hq, hqt⟩ hroot
    refine ⟨.stub (pubDig pub pubMemIn), by simp [PTree.At], rfl, heq, by simp [PTree.leaves], ?_⟩
    intro o ho hb hs hc
    obtain ⟨q, nq, hpq, -⟩ := recv1 o ho hb hs hc
    exact absurd hpq (hno q nq)

end main

#print axioms segMP_same
#print axioms two_le_busNat'
#print axioms busNat_le_row
#print axioms root_unique
#print axioms pos_of_act
#print axioms pos_unique
#print axioms mpTree_eval
#print axioms PTree.At_nodup
#print axioms mp_tree

end WasmBase
