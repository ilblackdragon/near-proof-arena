import WasmBase.Main.SegMpath
import WasmBase.Main.M2RegAbsentFacts
/-!
# WasmBase.Main.SegMemb — MEMB's leaf link and block order (E2E M4)

`MEMB` (table 19 of `wasmBaseSegAir`) has one row per 128 bytes of a touched 1 KiB memory block:
eight data rows (`p0 … p7`) and a ninth SHA-384 padding row (`p8`).  `MPATH` (table 20) proves the
Merkle update of each touched block (`Main/SegMpath.lean`).  This file proves the two MEMB facts
that `SegMpath` leaves open:

* **The LEAF link** (`leaf_link`): every MPATH `bot` row's `[blk, ro, co, cn]` (block, read-only
  flag, old and new leaf digests) is the `[blk, ro, hoI[0..18], hoO[0..18]]` of a MEMB padding row
  (`p8 = 1`).  Bus 15 is touched only by MEMB (sends, count `p8`) and MPATH (receives, count `bot`)
  (`seg_leaf_tables`, by `decide`), so this is the bus balance (`recv_has_send`).
* **The block walk** (`memb_pos`, `memb_blk_const`): active MEMB rows form a prefix, row `r` of it is
  row `r mod 9` of its block (`p_{r mod 9} = 1`), and `blk`, `ro` are constant within a block.
* **Strictly increasing blocks** (`memb_blk_step`, `memb_blk_strict`, `memb_blk_distinct`): the
  padding rows' `blk` values strictly increase in row order, hence are distinct.  At a block boundary
  `R16(nxt.blk − blk − 1)` with `blk`, `nblk − 1 − blk` R16-checked on the padding row; every value
  is below `2^16`, so the field equation is exact (no wrap).
* **The byte messages** (`memb_byte_msg`, `memb_addr_inj`): data row `9b + k` (`k < 8`) sends, for
  each `i < 128` and with count 1, the CH message `[3, 1024·blk + 128·k + i, 0, bi_i, 0, 0, 0, t_in]`;
  over the eight rows these are the 1,024 addresses `1024·blk + j`, `j < 1024`, each exactly once,
  and different blocks give disjoint address ranges.

The R16 facts go through `lookup_sound`, so the order lemmas take the **R16 send bound of
`wasmBaseSegAir`** (`hsend`) as a hypothesis, exactly as `regLenAgree_groupG` did before `RegSend`.
(For this AIR it is not derived here: the base chips' counts need `occ_bits_of`'s per-chip lemmas,
and `RET`/`MEMB` have sum-of-flags counts, `fRet + …` and `kD = p0 + … + p7`.)
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem seg_t19 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[19]'(by simp [seg_air_len]) = Memb.table := rfl

/-- MEMB's column indices. -/
theorem mb_ix : ix Memb.cols "act" = 0 ∧ ix Memb.cols "blk" = 10 ∧ ix Memb.cols "ro" = 11 := by decide
theorem mb_ix_p : ∀ i, i < 9 → ix Memb.cols s!"p{i}" = 1 + i := by decide
theorem mb_ix_p0 : ix Memb.cols "p0" = 1 := by decide
theorem mb_ix_bi : ∀ i, i < 128 → ix Memb.cols s!"bi{i}" = 14 + i := by decide
theorem mb_ix_ho : ∀ l, l < 18 → ix Memb.cols s!"hoI{l}" = 486 + l ∧ ix Memb.cols s!"hoO{l}" = 534 + l := by
  decide

/-- The cell `i` of row `r` of MEMB. -/
abbrev bc (tr : Trace) (r i : Nat) : F := tr.cell 19 r i

/-- An 18-limb digest of MEMB starting at column `base`. -/
def bdig (tr : Trace) (r base : Nat) : List F := (List.range 18).map fun l => bc tr r (base + l)

/-! ## The LEAF bus (15) -/

theorem memb_leaf : Memb.table.inters.filter (fun i => i.bus = 15) =
    [⟨busLeaf, true, Memb.p 8, [Memb.c "blk", Memb.c "ro"] ++ (names "hoI" 18).map Memb.c ++
      (names "hoO" 18).map Memb.c⟩] := by decide

theorem mpath_leaf : Mpath.table.inters.filter (fun i => i.bus = 15) =
    [⟨busLeaf, false, Mpath.c "bot", [Mpath.c "blk", Mpath.c "ro"] ++ Mpath.dig "co" ++ Mpath.dig "cn"⟩] := by
  decide

theorem seg_leaf_tables (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 19 → t ≠ 20 →
      ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus ≠ 15 := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), t ≠ 19 → t ≠ 20 →
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => i.bus != 15) = true := by
    decide
  have h : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 19 → t ≠ 20 →
      ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != 15) = true := by
    simp only [e]; exact h0
  intro t ht h19 h20 i hi
  have := List.all_eq_true.mp (h t ht h19 h20) i hi
  simpa using this

theorem bdig_eval (tr : Trace) (pub : List F) (r : Nat) (base : Nat) (s : String)
    (hix : ∀ l, l < 18 → ix Memb.cols s!"{s}{l}" = base + l) :
    ((names s 18).map Memb.c).map (·.eval (tr.row pub 19 r)) = bdig tr r base := by
  simp only [names, bdig, List.map_map]
  apply List.map_congr_left; intro l hl
  simp only [Function.comp, Memb.c, hix l (List.mem_range.mp hl)]
  rfl

section leaf
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **Every LEAF occurrence**: a MEMB row's send `[blk, ro] ++ hoI ++ hoO` (count `p8`) or an MPATH
row's receive `[blk, ro] ++ co ++ cn` (count `bot`). -/
theorem leaf_occ {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = 15) :
    (∃ r, r < tr.height 19 ∧
      o = (15, true, [bc tr r 10, bc tr r 11] ++ bdig tr r 486 ++ bdig tr r 534, (bc tr r 9).toNat)) ∨
    (∃ r, r < tr.height 20 ∧
      o = (15, false, [mc tr r 5, mc tr r 4] ++ mdig tr r 12 ++ mdig tr r 30, (mc tr r 1).toNat)) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb
  by_cases h19 : t = 19
  · subst h19
    rw [seg_t19] at hi
    have hm : i ∈ Memb.table.inters.filter (fun i => i.bus = 15) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [memb_leaf] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    subst hm
    left; refine ⟨r, hr, ?_⟩
    obtain ⟨-, ib, iro⟩ := mb_ix
    simp only [List.map_append, List.map_cons, List.map_nil, Memb.c, Memb.p, ib, iro, mb_ix_p 8 (by decide)]
    rw [bdig_eval tr pub r 486 "hoI" (fun l hl => (mb_ix_ho l hl).1),
      bdig_eval tr pub r 534 "hoO" (fun l hl => (mb_ix_ho l hl).2)]
    rfl
  by_cases h20 : t = 20
  · subst h20
    rw [seg_t20] at hi
    have hm : i ∈ Mpath.table.inters.filter (fun i => i.bus = 15) := List.mem_filter.mpr ⟨hi, by simpa using hb⟩
    rw [mpath_leaf] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    subst hm
    right; refine ⟨r, hr, ?_⟩
    obtain ⟨-, ibot, -, -, iro, iblk, -⟩ := mp_ix_names
    simp only [List.map_append, List.map_cons, List.map_nil, Mpath.c, ibot, iro, iblk]
    rw [dig_eval tr pub r 12 "co" (fun l hl => (mp_ix_limbs l hl).1),
      dig_eval tr pub r 30 "cn" (fun l hl => (mp_ix_limbs l hl).2.1)]
    rfl
  · exact absurd hb (seg_leaf_tables nloc ngl t ht h19 h20 i hi)

/-- The LEAF receives (MPATH's `bot`) are bits. -/
theorem leaf_recv_bits :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = 15 → o.2.1 = false → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  rcases leaf_occ H ho hb with ⟨r, -, rfl⟩ | ⟨r, hr, rfl⟩
  · simp at hs
  · show (mc tr r 1).toNat ≤ 1
    rcases (mp_bool H hr).2.1 with h | h <;> rw [h] <;> decide

/-- `p8` is a bit on a MEMB row. -/
theorem memb_p_bit {r : Nat} (hr : r < tr.height 19) {i : Nat} (hi : i < 9) :
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

/-- **The LEAF link.**  Every MPATH bottom row's `[blk, ro, old leaf, new leaf]` is the
`[blk, ro, hoI[0..18], hoO[0..18]]` of a MEMB padding row. -/
theorem leaf_link {r : Nat} (hr : r < tr.height 20) (hbot : mc tr r 1 = 1) :
    ∃ r', r' < tr.height 19 ∧ bc tr r' 9 = 1 ∧
      [bc tr r' 10, bc tr r' 11] ++ bdig tr r' 486 ++ bdig tr r' 534 =
        [mc tr r 5, mc tr r 4] ++ mdig tr r 12 ++ mdig tr r 30 := by
  have hocc : (15, false, [mc tr r 5, mc tr r 4] ++ mdig tr r 12 ++ mdig tr r 30, (mc tr r 1).toNat) ∈
      occs (wasmBaseSegAir nloc ngl) tr pub := by
    have hm : (⟨busLeaf, false, Mpath.c "bot", [Mpath.c "blk", Mpath.c "ro"] ++ Mpath.dig "co" ++
        Mpath.dig "cn"⟩ : Inter) ∈ ((wasmBaseSegAir nloc ngl).tables[20]'(by simp [seg_air_len])).inters := by
      rw [seg_t20]
      have : (⟨busLeaf, false, Mpath.c "bot", [Mpath.c "blk", Mpath.c "ro"] ++ Mpath.dig "co" ++
          Mpath.dig "cn"⟩ : Inter) ∈ Mpath.table.inters.filter (fun i => i.bus = 15) := by
        rw [mpath_leaf]; simp
      exact (List.mem_filter.mp this).1
    refine mem_occs.mpr ⟨20, by simp [seg_air_len], r, hr, _, hm, ?_⟩
    obtain ⟨-, ibot, -, -, iro, iblk, -⟩ := mp_ix_names
    simp only [List.map_append, List.map_cons, List.map_nil, Mpath.c, ibot, iro, iblk]
    rw [dig_eval tr pub r 12 "co" (fun l hl => (mp_ix_limbs l hl).1),
      dig_eval tr pub r 30 "cn" (fun l hl => (mp_ix_limbs l hl).2.1)]
    rfl
  have hc : (mc tr r 1).toNat = 1 := by rw [hbot]; decide
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ :=
    recv_has_send H 15 (leaf_recv_bits H) hocc rfl rfl hc
  rcases leaf_occ H ho' hb' with ⟨r', hr', rfl⟩ | ⟨r', -, rfl⟩
  · refine ⟨r', hr', ?_, hm'⟩
    rcases memb_p_bit H hr' (i := 8) (by decide) with h | h
    · simp only at hc'; rw [show (1 + 8 : Nat) = 9 from rfl] at h; rw [h] at hc'; exact absurd rfl hc'
    · exact h
  · simp at hs'

end leaf


/-! ## R16 answers on `wasmBaseSegAir` -/

/-- Every table of the segment AIR but RANGE16 (index 15) only sends on R16. -/
theorem seg_r16_send_only (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 15 →
      ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus = busR16 → i.send = true := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), t ≠ 15 →
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => i.bus != busR16 || i.send) = true := by
    decide
  intro t ht h15 i hi hb
  have h1 : ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != busR16 || i.send) = true := by
    simp only [e] at ht ⊢; exact h0 t ht h15
  have := List.all_eq_true.mp h1 i hi
  simpa [hb] using this

theorem seg_t15 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[15]'(by simp [seg_air_len]) = Range16.table := rfl
theorem seg_t27 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[27]'(by simp [seg_air_len]) = RegC.table := rfl

/-- **REG-C at index 27 of the segment AIR satisfies the walk's interface** (so `RegWalkG` applies
to segment traces too, and its `regG_r16_recv` is the RANGE16 answer characterisation). -/
theorem regAt_seg (nloc ngl : Nat) : RegAt (wasmBaseSegAir nloc ngl) 27 where
  lt := by simp [seg_air_len]
  cons := fun e he => by
    rw [seg_t27]; exact List.mem_append_left _ (List.mem_append_left _ he)
  inters := fun i hi => by
    rw [seg_t27]; exact List.mem_append_left _ (List.mem_append_left _ hi)
  r16only := by
    intro T hT hne i hi hb
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hT
    by_cases h15 : t = 15
    · subst h15; exact absurd (seg_t15 nloc ngl) hne
    · exact seg_r16_send_only nloc ngl t ht h15 i hi hb

/-- An R16 query with count 1 on a segment trace is `< 2^16`, given the R16 send bound `hsend`. -/
theorem seg_r16_lt {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) {r : Nat} (hr : r < tr.height t)
    {e c : Expr} (hi : r16 e c ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have hocc := occ_of_inter ht hr hi hc
  obtain ⟨x, hx, hxl⟩ := lookup_r16G H hsend (regG_r16_recv (regAt_seg nloc ngl) H) hocc rfl rfl rfl
  simp only [r16, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

/-! ## MEMB rows as naturals -/

/-- MEMB's cell `i` of row `r` as a natural. -/
abbrev mbN (tr : Trace) (r i : Nat) : Nat := rowNat tr 19 r i

theorem memb_C {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 19) : ∀ e ∈ Memb.constraints, e.eval (tr.row pub 19 r) = 0 := by
  intro e he
  exact H.constr 19 (by simp [seg_air_len]) r hr e (by rw [seg_t19]; exact he)

theorem memb_c_eval (tr : Trace) (pub : List F) (r : Nat) (s : String) :
    (Memb.c s).eval (tr.row pub 19 r) = ((mbN tr r (ix Memb.cols s) : Nat) : F) := by
  simp only [Memb.c, v, Expr.eval_col, Trace.row, cell_cast]

theorem memb_n_eval (tr : Trace) (pub : List F) (r : Nat) (hr : r + 1 < tr.height 19) (s : String) :
    (Memb.n s).eval (tr.row pub 19 r) = ((mbN tr (r + 1) (ix Memb.cols s) : Nat) : F) := by
  simp only [Memb.n, nv, Expr.eval_nxt, Trace.row, Nat.mod_eq_of_lt hr, cell_cast]

theorem memb_p_eval (tr : Trace) (pub : List F) (r : Nat) {i : Nat} (hi : i < 9) :
    (Memb.p i).eval (tr.row pub 19 r) = ((mbN tr r (1 + i) : Nat) : F) := by
  rw [Memb.p, memb_c_eval, mb_ix_p i hi]

theorem trans_eval_one (tr : Trace) (pub : List F) (t r : Nat) (hr : r + 1 < tr.height t) :
    Expr.trans.eval (tr.row pub t r) = 1 := by
  have : (r + 1 == tr.height t) = false := by simp; omega
  simp [Expr.eval, Trace.row, this]

section walk
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **A MEMB row as naturals**: `act` and the nine position flags are bits, and they sum to `act`. -/
theorem memb_row {r : Nat} (hr : r < tr.height 19) :
    mbN tr r 0 ≤ 1 ∧ (∀ i, i < 9 → mbN tr r (1 + i) ≤ 1) ∧
      mbN tr r 1 + mbN tr r 2 + mbN tr r 3 + mbN tr r 4 + mbN tr r 5 + mbN tr r 6 + mbN tr r 7 +
        mbN tr r 8 + mbN tr r 9 = mbN tr r 0 := by
  have C := memb_C H hr
  have ha := C (Chips.bool (Memb.c "act")) (by simp [Memb.constraints])
  rw [Chips.bool, Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.1, Expr.eval_ofNat'] at ha
  have ba := bool_nat (rowNat_lt tr 19 r 0) ha
  have bp : ∀ i, i < 9 → mbN tr r (1 + i) ≤ 1 := by
    intro i hi
    rcases memb_p_bit H hr hi with h | h
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

/-- The position flag of an active row is one-hot: `p_k = 1` forces every other flag to 0. -/
theorem memb_onehot {r : Nat} (hr : r < tr.height 19) {k j : Nat} (hk : k < 9) (hj : j < 9) (hkj : k ≠ j)
    (hpk : mbN tr r (1 + k) = 1) : mbN tr r (1 + j) = 0 := by
  obtain ⟨ha, bp, hs⟩ := memb_row H hr
  have := bp j hj
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> omega

/-- **The block walk.**  Active rows form a prefix, and active row `r` is row `r mod 9` of its block:
`p_{r mod 9} = 1`. -/
theorem memb_pos : ∀ r, r < tr.height 19 → mbN tr r 0 = 1 →
    (∀ r', r' ≤ r → mbN tr r' 0 = 1) ∧ mbN tr r (1 + r % 9) = 1 := by
  intro r
  induction r with
  | zero =>
    intro hr ha
    refine ⟨fun r' h => by rw [show r' = 0 by omega]; exact ha, ?_⟩
    have h := memb_C H hr (Expr.first * Memb.c "act" * (1 - Memb.p 0)) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_p_eval tr pub 0 (show 0 < 9 by decide), ha] at h
    simp only [Expr.eval, Trace.row, beq_self_eq_true, ite_true] at h
    show mbN tr 0 (1 + 0) = 1
    exact natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
  | succ r ih =>
    intro hr ha
    -- the previous row is active (`trans·(1 − act)·nxt.act = 0`)
    have hpre := memb_C H (r := r) (by omega) (Expr.trans * (1 - Memb.c "act") * Memb.n "act")
      (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_n_eval tr pub r hr, trans_eval_one tr pub 19 r hr, ha, cast_one] at hpre
    have ha0 : mbN tr r 0 = 1 :=
      natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    obtain ⟨hpref, hp⟩ := ih (by omega) ha0
    refine ⟨fun r' h => by
      rcases (by omega : r' ≤ r ∨ r' = r + 1) with h' | rfl
      · exact hpref r' h'
      · exact ha, ?_⟩
    have hm : r % 9 < 9 := Nat.mod_lt _ (by decide)
    by_cases h8 : r % 9 = 8
    · -- the next row after a padding row starts a block
      rw [h8] at hp
      have h := memb_C H (r := r) (by omega) (Expr.trans * Memb.p 8 * Memb.n "act" * (1 - Memb.n "p0"))
        (by simp [Memb.constraints])
      simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r (show 8 < 9 by decide),
        memb_n_eval tr pub r hr, mb_ix.1, trans_eval_one tr pub 19 r hr, hp, ha, cast_one] at h
      rw [mb_ix_p0] at h
      have : (r + 1) % 9 = 0 := by omega
      rw [this]
      exact natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    · have hlt : r % 9 < 8 := by omega
      have hmem : Expr.trans * Memb.p (r % 9) * (1 - nv (ix Memb.cols s!"p{r % 9 + 1}")) ∈ Memb.constraints := by
        unfold Memb.constraints
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))))))
        exact List.mem_map.mpr ⟨r % 9, List.mem_range.mpr hlt, rfl⟩
      have h := memb_C H (r := r) (by omega) _ hmem
      rw [mb_ix_p (r % 9 + 1) (by omega)] at h
      simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r hm, nv,
        Expr.eval_nxt, trans_eval_one tr pub 19 r hr, hp, cast_one] at h
      simp only [Trace.row, Nat.mod_eq_of_lt hr, cell_cast] at h
      have : (r + 1) % 9 = r % 9 + 1 := by omega
      rw [this, show 1 + (r % 9 + 1) = 1 + (r % 9 + 1) from rfl]
      exact natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)

/-- **`blk` is constant inside a block**: rows `9b … 9b+8` carry the padding row's `blk`. -/
theorem memb_blk_const {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    ∀ k, k ≤ 8 → mbN tr (9 * b + k) 10 = mbN tr (9 * b + 8) 10 := by
  have step : ∀ k, k < 8 → mbN tr (9 * b + k + 1) 10 = mbN tr (9 * b + k) 10 := by
    intro k hk
    have hr1 : 9 * b + k + 1 < tr.height 19 := by omega
    have ha1 := (memb_pos H (9 * b + 8) hr ha).1 (9 * b + k + 1) (by omega)
    have hp := (memb_pos H (9 * b + k + 1) hr1 ha1).2
    have hmod : (9 * b + k + 1) % 9 = k + 1 := by omega
    rw [hmod] at hp
    have hp0 : mbN tr (9 * b + k + 1) (1 + 0) = 0 := memb_onehot H hr1 (k := k + 1) (by omega) (by decide) (by omega) hp
    have h := memb_C H (r := 9 * b + k) (by omega)
      (Expr.trans * Memb.n "act" * (1 - Memb.n "p0") * (Memb.n "blk" - Memb.c "blk")) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_n_eval tr pub _ hr1, memb_c_eval,
      trans_eval_one tr pub 19 _ hr1, mb_ix.1, mb_ix.2.1, mb_ix_p0, ha1, cast_one] at h
    rw [show (1 : Nat) = 1 + 0 from rfl, hp0] at h
    exact natEq (by grind) (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)
  intro k hk
  induction k with
  | zero =>
    -- walk up from 0 to 8
    have : ∀ j, j ≤ 8 → mbN tr (9 * b + j) 10 = mbN tr (9 * b) 10 := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ihj => rw [← ihj (by omega)]; exact step j (by omega)
    exact (this 8 (Nat.le_refl _)).symm
  | succ k ihk =>
    rw [← ihk (by omega)]; exact step k (by omega)

/-- **Consecutive blocks have strictly increasing `blk`** (from `R16(nxt.blk − blk − 1)` at the
padding row and `blk < 2^16` on both padding rows). -/
theorem memb_blk_step
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {b : Nat} (hr : 9 * (b + 1) + 8 < tr.height 19) (ha : mbN tr (9 * (b + 1) + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 < mbN tr (9 * (b + 1) + 8) 10 ∧ mbN tr (9 * (b + 1) + 8) 10 < 65536 := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hpref := (memb_pos H _ hr ha).1
  have hr8 : 9 * b + 8 < tr.height 19 := by omega
  have ha8 := hpref (9 * b + 8) (by omega)
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_pos H _ hr8 ha8).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have hp8' : mbN tr (9 * (b + 1) + 8) (1 + 8) = 1 := by
    have := (memb_pos H _ hr ha).2; rwa [show (9 * (b + 1) + 8) % 9 = 8 by omega] at this
  have hn1 : 9 * b + 8 + 1 < tr.height 19 := by omega
  have ha9 := hpref (9 * b + 9) (by omega)
  have hp9 : mbN tr (9 * b + 8 + 1) (1 + 0) = 1 := by
    have := (memb_pos H (9 * b + 9) (by omega) ha9).2
    rwa [show (9 * b + 9) % 9 = 0 by omega] at this
  -- the R16 queries of MEMB's last three interactions
  have mem : ∀ x ∈ [r16 (Memb.n "blk" - Memb.c "blk" - 1) (.trans * Memb.p 8 * Memb.n "p0"),
      r16 (Memb.c "blk") (Memb.p 8)], x ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    intro x hx
    rw [seg_t19]
    show x ∈ Memb.inters
    unfold Memb.inters
    refine List.mem_append_right _ ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
    rcases hx with rfl | rfl
    · right; left; rfl
    · right; right; left; rfl
  have cP8 : ∀ r, r < tr.height 19 → mbN tr r (1 + 8) = 1 → ((Memb.p 8).eval (tr.row pub 19 r)).toNat = 1 := by
    intro r _ h; rw [memb_p_eval tr pub r (by decide), h]; decide
  have hb0 := seg_r16_lt H hsend ht hr8 (mem (r16 (Memb.c "blk") (Memb.p 8)) (by simp)) (cP8 _ hr8 hp8)
  have hb1 := seg_r16_lt H hsend ht hr (mem (r16 (Memb.c "blk") (Memb.p 8)) (by simp)) (cP8 _ hr hp8')
  have hgap := seg_r16_lt H hsend ht hr8 (mem (r16 (Memb.n "blk" - Memb.c "blk" - 1) (.trans * Memb.p 8 * Memb.n "p0")) (by simp)) (by
    simp only [Expr.eval_mul', memb_p_eval tr pub _ (show 8 < 9 by decide), memb_n_eval tr pub _ hn1,
      trans_eval_one tr pub 19 _ hn1, hp8, mb_ix_p0]
    rw [show (1 : Nat) = 1 + 0 from rfl, hp9, cast_one]
    decide)
  simp only [memb_c_eval, mb_ix.2.1, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at hb0 hb1
  simp only [Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, memb_n_eval tr pub _ hn1, mb_ix.2.1] at hgap
  -- `blk` of row `9b + 9` is the next block's (`memb_blk_const`)
  have hc := memb_blk_const H (b := b + 1) hr ha 0 (by decide)
  rw [show 9 * (b + 1) + 0 = 9 * b + 8 + 1 by omega] at hc
  rw [hc] at hgap
  simp only [mbN] at hb0 hb1 hgap ⊢
  generalize rowNat tr 19 (9 * b + 8) 10 = x at hb0 hgap ⊢
  generalize rowNat tr 19 (9 * (b + 1) + 8) 10 = y at hb1 hgap ⊢
  have hP := P_val
  refine ⟨Nat.lt_of_not_le fun hle => ?_, hb1⟩
  -- then `y − x − 1 ≡ P − (x − y) − 1` has `toNat ≥ P − 2^16 > 2^16`
  have e : ((y : Nat) : F) - ((x : Nat) : F) - ((1 : Nat) : F) = ((P - (x - y) - 1 : Nat) : F) := by
    have h1 : ((P - (x - y) - 1 : Nat) : F) + ((x - y : Nat) : F) + 1 = ((P : Nat) : F) := by
      rw [← cast_one, ← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add]
      congr 1; omega
    have h2 : ((P : Nat) : F) = 0 := by rw [← Fp.cast_toNat 0]; rfl
    have h3 : ((x - y : Nat) : F) + ((y : Nat) : F) = ((x : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_add]; congr 1; omega
    grind
  rw [e, Fp.toNat_cast_of_lt (by omega)] at hgap
  omega

/-- **The padding rows' `blk` values strictly increase**: block `b` before block `b'` (both active)
has a smaller `blk`. -/
theorem memb_blk_strict
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1) :
    ∀ b d, 9 * (b + d + 1) + 8 < tr.height 19 → mbN tr (9 * (b + d + 1) + 8) 0 = 1 →
      mbN tr (9 * b + 8) 10 < mbN tr (9 * (b + d + 1) + 8) 10 := by
  intro b d
  induction d with
  | zero => intro hr ha; exact (memb_blk_step H hsend hr ha).1
  | succ d ih =>
    intro hr ha
    have hpref := (memb_pos H _ hr ha).1
    have ha' := hpref (9 * (b + d + 1) + 8) (by omega)
    have := ih (by omega) ha'
    have := (memb_blk_step H hsend (b := b + d + 1) (by omega) (by simpa [Nat.add_assoc] using ha)).1
    rw [show b + (d + 1) + 1 = b + d + 1 + 1 by omega]
    omega

/-- **Touched blocks are distinct.** -/
theorem memb_blk_distinct
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {b b' : Nat} (hb : b ≠ b') (hr : 9 * b + 8 < tr.height 19) (hr' : 9 * b' + 8 < tr.height 19)
    (ha : mbN tr (9 * b + 8) 0 = 1) (ha' : mbN tr (9 * b' + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 ≠ mbN tr (9 * b' + 8) 10 := by
  rcases Nat.lt_or_gt_of_ne hb with h | h
  · have := memb_blk_strict H hsend b (b' - b - 1) (by rw [show b + (b' - b - 1) + 1 = b' by omega]; exact hr')
      (by rw [show b + (b' - b - 1) + 1 = b' by omega]; exact ha')
    rw [show b + (b' - b - 1) + 1 = b' by omega] at this
    omega
  · have := memb_blk_strict H hsend b' (b - b' - 1) (by rw [show b' + (b - b' - 1) + 1 = b by omega]; exact hr)
      (by rw [show b' + (b - b' - 1) + 1 = b by omega]; exact ha)
    rw [show b' + (b - b' - 1) + 1 = b by omega] at this
    omega

/-! ## The byte messages of a block -/

theorem memb_send_mem (i : Nat) (hi : i < 128) :
    chSend 3 (Memb.addr i) 0 [Memb.c s!"bi{i}", 0, 0, 0] (pv pubTIn) Memb.kD ∈ Memb.table.inters := by
  show _ ∈ Memb.inters
  unfold Memb.inters
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ ?_)))))
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_cons_self⟩

/-- **A data row's byte messages.**  On active row `r = 9b + k` with `k < 8`, for every `i < 128`
MEMB sends, with count 1, `[3, 1024·blk + 128·k + i, 0, bi_i, 0, 0, 0, t_in]` on the CH bus. -/
theorem memb_byte_msg {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hk : r % 9 < 8)
    {i : Nat} (hi : i < 128) :
    (busStk, true,
      [((3 : Nat) : F), ((1024 * mbN tr r 10 + 128 * (r % 9) + i : Nat) : F), ((0 : Nat) : F),
        ((mbN tr r (14 + i) : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
        pub.getD pubTIn 0], 1) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hp := (memb_pos H r hr ha).2
  obtain ⟨k, hkdef⟩ : ∃ k, k = r % 9 := ⟨_, rfl⟩
  rw [← hkdef] at hp hk ⊢
  have oh : ∀ j, j < 9 → mbN tr r (1 + j) = if j = k then 1 else 0 := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk; simpa using hp
    · rw [if_neg hjk]; exact memb_onehot H hr (k := k) (by omega) hj (Ne.symm hjk) hp
  have pe : ∀ j, j < 9 → (Memb.p j).eval (tr.row pub 19 r) = (((if j = k then 1 else 0 : Nat) : Nat) : F) := by
    intro j hj; rw [memb_p_eval tr pub r hj, oh j hj]
  have kD1 : (Memb.kD.eval (tr.row pub 19 r)).toNat = 1 := by
    have e8 : Memb.kD = 0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 +
        Memb.p 7 := rfl
    rw [e8]
    simp only [Expr.eval_add', Expr.eval_ofNat', pe 0 (by decide), pe 1 (by decide), pe 2 (by decide),
      pe 3 (by decide), pe 4 (by decide), pe 5 (by decide), pe 6 (by decide), pe 7 (by decide)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      h | h | h | h | h | h | h | h <;> simp [h] <;> decide
  have kk : Memb.kk.eval (tr.row pub 19 r) = ((k : Nat) : F) := by
    have e9 : Memb.kk = 0 + Expr.c 0 * Memb.p 0 + Expr.c 1 * Memb.p 1 + Expr.c 2 * Memb.p 2 +
        Expr.c 3 * Memb.p 3 + Expr.c 4 * Memb.p 4 + Expr.c 5 * Memb.p 5 + Expr.c 6 * Memb.p 6 +
        Expr.c 7 * Memb.p 7 + Expr.c 8 * Memb.p 8 := rfl
    rw [e9]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, pe 0 (by decide),
      pe 1 (by decide), pe 2 (by decide), pe 3 (by decide), pe 4 (by decide), pe 5 (by decide),
      pe 6 (by decide), pe 7 (by decide), pe 8 (by decide)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      h | h | h | h | h | h | h | h <;> simp [h] <;> decide
  have hocc := occ_of_inter ht hr (by rw [seg_t19]; exact memb_send_mem H i hi) kD1
  have e : (chSend 3 (Memb.addr i) 0 [Memb.c s!"bi{i}", 0, 0, 0] (pv pubTIn) Memb.kD).msg.map
      (·.eval (tr.row pub 19 r)) =
      [((3 : Nat) : F), ((1024 * mbN tr r 10 + 128 * k + i : Nat) : F), ((0 : Nat) : F),
        ((mbN tr r (14 + i) : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
        pub.getD pubTIn 0] := by
    simp only [chSend, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Memb.addr,
      Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, memb_c_eval, mb_ix.2.1, kk,
      mb_ix_bi i hi, pv, Expr.eval_pub]
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    rfl
  rw [e] at hocc
  exact hocc

end walk

/-- **The 1,024 addresses of a block, each once, and different blocks apart**: `1024·blk + 128·k + i`
(`k < 8`, `i < 128`) is injective in `(blk, k, i)` for `blk < 2^16` (and below `P`, so it is the
field address exactly). -/
theorem memb_addr_inj {blk blk' k k' i i' : Nat} (hk : k < 8) (hk' : k' < 8) (hi : i < 128) (hi' : i' < 128)
    (h : 1024 * blk + 128 * k + i = 1024 * blk' + 128 * k' + i') : blk = blk' ∧ k = k' ∧ i = i' := by
  omega

theorem memb_addr_lt {blk k i : Nat} (hb : blk < 65536) (hk : k < 8) (hi : i < 128) :
    1024 * blk + 128 * k + i < 2 ^ 26 := by omega

end WasmBase

#print axioms WasmBase.leaf_link
#print axioms WasmBase.regAt_seg
#print axioms WasmBase.memb_row
#print axioms WasmBase.memb_pos
#print axioms WasmBase.memb_blk_const
#print axioms WasmBase.memb_blk_step
#print axioms WasmBase.memb_blk_strict
#print axioms WasmBase.memb_blk_distinct
#print axioms WasmBase.memb_byte_msg
#print axioms WasmBase.memb_addr_inj
