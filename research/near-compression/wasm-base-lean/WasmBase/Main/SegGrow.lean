import WasmBase.Main.SegGrowMerkle
import WasmBase.Main.SegMP
import WasmBase.Main.SegBus
import WasmBase.Main.M3Facts

/-!
# WasmBase.Main.SegGrow — row and bus facts of `wasmBaseSegAirG` (E2E M4c, segments with `memory.grow`)

From `HoldsX (wasmBaseSegAirG …) pub tr` alone:

* **the table split** `segG_msgs`: every bus of the grow AIR is `wasmBaseSegAirMP`'s 32 parts on the
  same trace followed by the four new parts (MEMG 32, SEGG 33, MEMBG 34, MEMBH 35); on STATE
  (`segG_state`) the new parts are MEMG's only, on CH (`segG_ch`) MEMG's, SEGG's, MEMBG's and
  MEMBH's; on RCH/NODE (buses 16/17) only SEGG adds traffic, on the leaf bus 15 MEMBG and MEMBH.
* **SEGG** (`segg_row0`, `segg_rows`, `segg_stubs`, `segg_lift_nat`): `64·pin = nblk_in`,
  `64·pout = nblk_out`, `lift = D − D_in ∈ {0, 1}`, a lift needs `D_in = 16`, children are
  touched only on a lift, untouched children are stubs (`nL = oL`, `nR = Z_16`); only row 0 is
  active.
* **the size message as a channel fact** (`segg_size_parts`): SEGG's CH traffic is exactly one
  production `[8, 0, 0, pin, 0, 0, 0, t_in]` and one consumption `[8, 0, 0, pout, 0, 0, 0, tz]`.
* **MEMBG** (`membg_row`, `membg_leaf_parts`): the one-hot row kinds, and every leaf message MEMBG
  sends on bus 15 is `[blk, 0] ++ limbs zleafW ++ out-digest` — the old leaf of a grown block is
  the spec's `zleaf` (`SegGrowMerkle.zleafW_bytes`).

## Named obligations (not proved here)

* `SegGSendR16` — the R16 send bound of `wasmBaseSegAirG` (every R16 send count is `≤ 1`; the
  analogue of `seg_hsend_r16`: tables 0–31 as there, MEMG by `bool f_grow`/`bool act`, MEMBG by its
  one-hot `p`, MEMBH as MEMB).  It is what turns MEMBG's/MEMBH's range checks into
  `64·gold ≤ blk < 64·gnew`, `nblk_in ≤ blk`, `2^16 ≤ blk < nblk_in` (as in `m3_ginit_range`).
* the STATE/CH **permutations** (`seg_hst`/`seg_hch` for this AIR): the parts above are the input;
  MEMG's rows join the action list (`actListM2` + MEMG), SEGG's size message and MEMBG's zero
  bytes join `initS` (MEMBG's at the grow time `tg`, not `t_in`: `seg_initS_tp` becomes
  "`t_in` or a MEMG grow row's `ts`"), and SEGG's final size message joins `finS`.
* `seg_sound` for this AIR: the step relation of `memory.grow`/`memory.size` from MEMG
  (`m3_grow_ok`/`m3_grow_fail` are the arithmetic), the size-message invariant
  `pages(state) = the live space-8 message`, and the memory-root conjunct
  (`SegGrowMerkle.memRootOf_memGrow` + `mp_tree` with SEGG as the root on a lift).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## The tables -/

theorem segG_lt (nloc ngl t : Nat) (h : t < 36) : t < (wasmBaseSegAirG nloc ngl).tables.length := by
  rw [segG_len]; exact h

theorem segG_get (nloc ngl t : Nat) (h : t < 36) (T : Table) (hT : (wasmBaseSegAirG nloc ngl).tables[t]? = some T) :
    (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t h) = T := by
  rw [List.getElem?_eq_getElem (segG_lt nloc ngl t h)] at hT
  exact Option.some.inj hT

theorem segG_t32' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[32]'(segG_lt nloc ngl 32 (by decide)) = MemG.table :=
  segG_get nloc ngl 32 (by decide) _ (segG_t32 nloc ngl)
theorem segG_t33' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[33]'(segG_lt nloc ngl 33 (by decide)) = SegG.table :=
  segG_get nloc ngl 33 (by decide) _ (segG_t33 nloc ngl)
theorem segG_t34' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[34]'(segG_lt nloc ngl 34 (by decide)) = MembG.table :=
  segG_get nloc ngl 34 (by decide) _ (segG_t34 nloc ngl)
theorem segG_t35' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[35]'(segG_lt nloc ngl 35 (by decide)) = MembH.table :=
  segG_get nloc ngl 35 (by decide) _ (segG_t35 nloc ngl)

/-- Tables 0–31 are `wasmBaseSegAirMP`'s. -/
theorem segG_t_mp (nloc ngl t : Nat) (h : t < 32) :
    (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t (by omega)) =
      (wasmBaseSegAirMP nloc ngl).tables[t]'(segMP_lt nloc ngl t h) := by
  have e := segG_same nloc ngl t h
  rw [List.getElem?_eq_getElem (segG_lt nloc ngl t (by omega)),
    List.getElem?_eq_getElem (segMP_lt nloc ngl t h)] at e
  exact Option.some.inj e

/-! ## The table split of every bus -/

/-- **Every bus of the grow AIR is `wasmBaseSegAirMP`'s on the same trace plus the four new parts.** -/
theorem segG_msgs (nloc ngl : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseSegAirG nloc ngl) tr pub b s =
      msgs (wasmBaseSegAirMP nloc ngl) tr pub b s ++
        (part MemG.table tr pub 32 b s ++ (part SegG.table tr pub 33 b s ++
          (part MembG.table tr pub 34 b s ++ part MembH.table tr pub 35 b s))) := by
  rw [msgs_flatMap, msgs_flatMap]
  simp only [wasmBaseSegAirG, List.zipIdx_append, List.flatMap_append, segMP_len]
  simp only [List.zipIdx_cons, List.flatMap_cons, List.zipIdx_nil, List.flatMap_nil, List.append_nil,
    Nat.reduceAdd, part]

/-- SEGG, MEMBG, MEMBH have no STATE traffic. -/
theorem segG_state_nil (tr : Trace) (pub : List F) (s : Bool) :
    part SegG.table tr pub 33 busState s = [] ∧ part MembG.table tr pub 34 busState s = [] ∧
      part MembH.table tr pub 35 busState s = [] := by
  refine ⟨part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_⟩ <;> cases s <;> decide +kernel

/-- **The STATE bus**: `wasmBaseSegAirMP`'s plus MEMG's rows (its `stateIn`/`stateOut`). -/
theorem segG_state (nloc ngl : Nat) (tr : Trace) (pub : List F) (s : Bool) :
    msgs (wasmBaseSegAirG nloc ngl) tr pub busState s =
      msgs (wasmBaseSegAirMP nloc ngl) tr pub busState s ++ part MemG.table tr pub 32 busState s := by
  obtain ⟨h1, h2, h3⟩ := segG_state_nil tr pub s
  rw [segG_msgs, h1, h2, h3]; simp

/-- The RCH (16) and NODE (17) buses: MEMG, MEMBG, MEMBH add nothing (SEGG is the lift root). -/
theorem segG_rch_node (nloc ngl : Nat) (tr : Trace) (pub : List F) (b : Nat) (hb : b = 16 ∨ b = 17) (s : Bool) :
    msgs (wasmBaseSegAirG nloc ngl) tr pub b s =
      msgs (wasmBaseSegAirMP nloc ngl) tr pub b s ++ part SegG.table tr pub 33 b s := by
  have h1 : part MemG.table tr pub 32 b s = [] := part_nil_of_filter (by rcases hb with rfl | rfl <;> cases s <;> decide +kernel)
  have h2 : part MembG.table tr pub 34 b s = [] := part_nil_of_filter (by rcases hb with rfl | rfl <;> cases s <;> decide +kernel)
  have h3 : part MembH.table tr pub 35 b s = [] := part_nil_of_filter (by rcases hb with rfl | rfl <;> cases s <;> decide +kernel)
  rw [segG_msgs, h1, h2, h3]; simp

/-- The leaf bus 15: MEMG and SEGG add nothing (MEMBG and MEMBH send leaves). -/
theorem segG_leaf (nloc ngl : Nat) (tr : Trace) (pub : List F) (s : Bool) :
    msgs (wasmBaseSegAirG nloc ngl) tr pub 15 s =
      msgs (wasmBaseSegAirMP nloc ngl) tr pub 15 s ++
        (part MembG.table tr pub 34 15 s ++ part MembH.table tr pub 35 15 s) := by
  have h1 : part MemG.table tr pub 32 15 s = [] := part_nil_of_filter (by cases s <;> decide +kernel)
  have h2 : part SegG.table tr pub 33 15 s = [] := part_nil_of_filter (by cases s <;> decide +kernel)
  rw [segG_msgs, h1, h2]; simp

/-! ## SEGG -/

/-- The cell `i` of row `r` of SEGG. -/
abbrev sgc (tr : Trace) (r i : Nat) : F := tr.cell 33 r i

theorem sg_ix : ix SegG.cols "pin" = 0 ∧ ix SegG.cols "pout" = 1 ∧ ix SegG.cols "tz" = 2 ∧
    ix SegG.cols "lift" = 3 ∧ ix SegG.cols "ndL" = 4 ∧ ix SegG.cols "ndR" = 5 ∧ ix SegG.cols "cidN" = 6 := by
  decide

theorem sg_ix_limbs : ∀ l, l < 18 → ix SegG.cols s!"oL{l}" = 7 + l ∧ ix SegG.cols s!"nL{l}" = 25 + l ∧
    ix SegG.cols s!"nR{l}" = 43 + l ∧ ix SegG.cols s!"pn{l}" = 61 + l := by
  decide

theorem sg_cx {pub : List F} {tr : Trace} (r i : Nat) : (Chips.v i).eval (tr.row pub 33 r) = sgc tr r i := rfl

/-- `Z_16`'s limbs (`SegG.zR`), as field elements. -/
def zRF : List F := (Grow.zrootW Grow.liftFrom).flatMap fun w => (wl w).map fun n => ((n : Nat) : F)

/-- The public values SEGG reads. -/
abbrev pNin (pub : List F) : F := pub.getD pubNblkIn 0
abbrev pNout (pub : List F) : F := pub.getD pubNblkOut 0
abbrev pDin (pub : List F) : F := pub.getD pubDepthIn 0

section rows
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

theorem segg_C {r : Nat} (hr : r < tr.height 33) :
    ∀ e ∈ SegG.constraints, e.eval (tr.row pub 33 r) = 0 := by
  intro e he
  exact H.constr 33 (segG_lt nloc ngl 33 (by decide)) r hr e (by rw [segG_t33']; exact he)

theorem segg_h0 : 4 ≤ tr.height 33 := H.heightPos 33 (segG_lt nloc ngl 33 (by decide))

/-- **SEGG's first row**: the size pins, the lift, its bits. -/
theorem segg_row0 :
    ((64 : Nat) : F) * sgc tr 0 0 = pNin pub ∧ ((64 : Nat) : F) * sgc tr 0 1 = pNout pub ∧
    sgc tr 0 3 = pD pub - pDin pub ∧ (sgc tr 0 3 = 0 ∨ sgc tr 0 3 = 1) ∧
    (sgc tr 0 3 = 1 → pDin pub = ((Grow.liftFrom : Nat) : F)) ∧
    (sgc tr 0 4 = 0 ∨ sgc tr 0 4 = 1) ∧ (sgc tr 0 5 = 0 ∨ sgc tr 0 5 = 1) ∧
    (sgc tr 0 3 = 0 → sgc tr 0 4 = 0 ∧ sgc tr 0 5 = 0) := by
  have C := segg_C H (r := 0) (by have := segg_h0 H; omega)
  obtain ⟨ipin, ipout, -, ilift, indL, indR, -⟩ := sg_ix
  have one : ((1 : Nat) : F) = 1 := rfl
  have fst : Expr.first.eval (tr.row pub 33 0) = 1 := by simp [Expr.eval, Trace.row]
  have pvx : ∀ k, (Chips.pv k).eval (tr.row pub 33 0) = pub.getD k 0 := by
    intro k; simp [Chips.pv, Expr.eval_pub, Trace.row]
  have c1 := C (.first * (64 * SegG.c "pin" - pv pubNblkIn)) (by simp [SegG.constraints])
  have c2 := C (.first * (64 * SegG.c "pout" - pv pubNblkOut)) (by simp [SegG.constraints])
  have c3 := C (.first * (SegG.c "lift" - pv pubDepth + pv pubDepthIn)) (by simp [SegG.constraints])
  have b3 := C (Chips.bool (SegG.c "lift")) (by simp [SegG.constraints])
  have c4 := C (SegG.c "lift" * (pv pubDepthIn - Expr.c Grow.liftFrom)) (by simp [SegG.constraints])
  have b4 := C (Chips.bool (SegG.c "ndL")) (by simp [SegG.constraints])
  have b5 := C (Chips.bool (SegG.c "ndR")) (by simp [SegG.constraints])
  have c5 := C (SegG.c "ndL" * (1 - SegG.c "lift")) (by simp [SegG.constraints])
  have c6 := C (SegG.c "ndR" * (1 - SegG.c "lift")) (by simp [SegG.constraints])
  simp only [SegG.c, Chips.bool, ipin, ipout, ilift, indL, indR, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
    sg_cx, Expr.eval_ofNat', one, fst, pvx, Expr.eval_c] at c1 c2 c3 b3 c4 b4 b5 c5 c6
  refine ⟨by grind, by grind, by grind, bool_cases b3, fun h => ?_, bool_cases b4, bool_cases b5, fun h => ?_⟩
  · rw [h] at c4; grind
  · rw [h] at c5 c6; exact ⟨by grind, by grind⟩

/-- **Only SEGG's first row can lift** (and touch children). -/
theorem segg_rows {r : Nat} (hr : r < tr.height 33) (h0 : r ≠ 0) :
    sgc tr r 3 = 0 ∧ sgc tr r 4 = 0 ∧ sgc tr r 5 = 0 := by
  have C := segg_C H hr
  obtain ⟨-, -, -, ilift, indL, indR, -⟩ := sg_ix
  have one : ((1 : Nat) : F) = 1 := rfl
  have fst : Expr.first.eval (tr.row pub 33 r) = 0 := by
    have : (r == 0) = false := by simpa using h0
    simp [Expr.eval, Trace.row, this]
  have c0 := C ((1 - Expr.first) * SegG.c "lift") (by simp [SegG.constraints])
  have c5 := C (SegG.c "ndL" * (1 - SegG.c "lift")) (by simp [SegG.constraints])
  have c6 := C (SegG.c "ndR" * (1 - SegG.c "lift")) (by simp [SegG.constraints])
  simp only [SegG.c, ilift, indL, indR, Expr.eval_mul', Expr.eval_sub', sg_cx, Expr.eval_ofNat', one, fst]
    at c0 c5 c6
  have hl : sgc tr r 3 = 0 := by grind
  rw [hl] at c5 c6
  exact ⟨hl, by grind, by grind⟩

/-- **SEGG's stubs on a lift**: an untouched left child is the in-root (`nL = oL`), an untouched
right child is `Z_16`. -/
theorem segg_stubs {r : Nat} (hr : r < tr.height 33) (hl : sgc tr r 3 = 1) :
    (sgc tr r 4 = 0 → ∀ l, l < 18 → sgc tr r (25 + l) = sgc tr r (7 + l)) ∧
    (sgc tr r 5 = 0 → ∀ l, l < 18 → sgc tr r (43 + l) = zRF.getD l 0) := by
  have C := segg_C H hr
  obtain ⟨-, -, -, ilift, indL, indR, -⟩ := sg_ix
  have one : ((1 : Nat) : F) = 1 := rfl
  have mem : ∀ l Z, l < 18 → Z ∈ [SegG.c "lift" * (1 - SegG.c "ndL") * (SegG.c s!"nL{l}" - SegG.c s!"oL{l}"),
      SegG.c "lift" * (1 - SegG.c "ndR") * (SegG.c s!"nR{l}" - SegG.zR.getD l 0)] → Z ∈ SegG.constraints := by
    intro l Z hl' hZ
    unfold SegG.constraints
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl', hZ⟩)
  have zr : ∀ l, l < 18 → (SegG.zR.getD l 0).eval (tr.row pub 33 r) = zRF.getD l 0 := by
    intro l hl'
    have hlen : (Grow.zrootW Grow.liftFrom).length = 6 := SegGrow.zrootW_length _
    have h18 : ((Grow.zrootW Grow.liftFrom).flatMap wl).length = 18 := by
      generalize Grow.zrootW Grow.liftFrom = ws at hlen
      match ws, hlen with
      | [_, _, _, _, _, _], _ => rfl
    have hl2 : l < ((Grow.zrootW Grow.liftFrom).flatMap wl).length := by rw [h18]; exact hl'
    have ez : zRF = ((Grow.zrootW Grow.liftFrom).flatMap wl).map fun n => ((n : Nat) : F) := by
      simp only [zRF, List.map_flatMap]
    rw [ez]
    simp only [SegG.zR, Grow.digC, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hl2, Option.map_some, Option.getD_some, Expr.eval_c]
  refine ⟨fun h4 l hl' => ?_, fun h5 l hl' => ?_⟩
  · obtain ⟨joL, jnL, -, -⟩ := sg_ix_limbs l hl'
    have e := C _ (mem l _ hl' (List.mem_cons_self))
    simp only [SegG.c, ilift, indL, joL, jnL, Expr.eval_mul', Expr.eval_sub', sg_cx, Expr.eval_ofNat', one,
      hl, h4] at e
    grind
  · obtain ⟨-, -, jnR, -⟩ := sg_ix_limbs l hl'
    have e := C _ (mem l _ hl' (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [SegG.c, ilift, indR, jnR, Expr.eval_mul', Expr.eval_sub', sg_cx, Expr.eval_ofNat', one,
      hl, h5, zr l hl'] at e
    grind

/-- **The lift in naturals**: with the public depths `D_in, D < 2^30`, SEGG's lift is
`D = D_in + 1` (then `D_in = 16`) or `D = D_in`. -/
theorem segg_lift_nat (hdin : (pDin pub).toNat < 2 ^ 30) (hd : (pD pub).toNat < 2 ^ 30) :
    (sgc tr 0 3 = 1 ∧ (pD pub).toNat = (pDin pub).toNat + 1 ∧ (pDin pub).toNat = Grow.liftFrom) ∨
      (sgc tr 0 3 = 0 ∧ (pD pub).toNat = (pDin pub).toNat) := by
  obtain ⟨-, -, hlift, hb, h16, -⟩ := segg_row0 H
  have hP := P_val
  rcases hb with h | h
  · right
    refine ⟨h, ?_⟩
    have e : pD pub = pDin pub := by rw [h] at hlift; grind
    rw [e]
  · left
    have e : pD pub = pDin pub + 1 := by rw [h] at hlift; grind
    have e16 := h16 h
    refine ⟨h, ?_, ?_⟩
    · rw [e, Fp.add_def, Fp.toNat_add, Fp.toNat_one, Nat.mod_eq_of_lt (by omega)]
    · rw [e16]; exact Fp.toNat_cast_of_lt (by rw [P_val]; decide)

end rows

/-! ## The size message (channel space 8) -/

/-- SEGG's CH production and consumption. -/
def segSzIn (tr : Trace) (pub : List F) : List F :=
  [((memSizeSpace : Nat) : F), 0, 0, sgc tr 0 0, 0, 0, 0, pub.getD pubTIn 0]
def segSzOut (tr : Trace) (pub : List F) : List F :=
  [((memSizeSpace : Nat) : F), 0, 0, sgc tr 0 1, 0, 0, 0, sgc tr 0 2]

/-- **The size message crosses the cut through SEGG's first row only**: SEGG produces exactly
`[8, 0, 0, pin, 0, 0, 0, t_in]` and consumes exactly `[8, 0, 0, pout, 0, 0, 0, tz]` on the channel
bus (with `64·pin = nblk_in`, `64·pout = nblk_out`, `segg_row0`). -/
theorem segg_size_parts (tr : Trace) (pub : List F) (h0 : 1 ≤ tr.height 33) :
    part SegG.table tr pub 33 busStk true = [segSzIn tr pub] ∧
      part SegG.table tr pub 33 busStk false = [segSzOut tr pub] := by
  constructor
  · rw [part_first (i0 := SegG.inters.getD 0 default) (by decide +kernel) rfl h0]
    simp [SegG.inters, segSzIn, chSend, SegG.c, Chips.v, Chips.pv, Expr.eval, Trace.row, sg_ix, memSizeSpace]
    rfl
  · rw [part_first (i0 := SegG.inters.getD 1 default) (by decide +kernel) rfl h0]
    simp [SegG.inters, segSzOut, chRecv, SegG.c, Chips.v, Expr.eval, Trace.row, sg_ix, memSizeSpace]
    rfl

/-! ## R16 lookups in the grow AIR -/

theorem segG_t15' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[15]'(segG_lt nloc ngl 15 (by decide)) = Range16.table := rfl
theorem segG_t27' (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[27]'(segG_lt nloc ngl 27 (by decide)) = Seg.RegCK.table := rfl

theorem segG_r16_send_only (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAirG nloc ngl).tables.length), t ≠ 15 →
      ∀ i ∈ ((wasmBaseSegAirG nloc ngl).tables[t]'ht).inters, i.bus = busR16 → i.send = true := by
  have e : (wasmBaseSegAirG nloc ngl).tables = (wasmBaseSegAirG 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAirG 0 0).tables.length), t ≠ 15 →
      ((wasmBaseSegAirG 0 0).tables[t]'ht).inters.all (fun i => i.bus != busR16 || i.send) = true := by
    decide
  intro t ht h15 i hi hb
  have h1 : ((wasmBaseSegAirG nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != busR16 || i.send) = true := by
    simp only [e] at ht ⊢; exact h0 t ht h15
  have := List.all_eq_true.mp h1 i hi
  simpa [hb] using this

/-- REG-C at index 27 of the grow AIR satisfies the walk's interface (RANGE16 answers). -/
theorem regAt_segG (nloc ngl : Nat) : RegAt (wasmBaseSegAirG nloc ngl) 27 where
  lt := segG_lt nloc ngl 27 (by decide)
  cons := fun e he => by
    rw [segG_t27']; exact List.mem_append_left _ (List.mem_append_left _ he)
  inters := fun i hi => by
    rw [segG_t27']; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi))
  r16only := by
    intro T hT hne i hi hb
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hT
    by_cases h15 : t = 15
    · subst h15; exact absurd (segG_t15' nloc ngl) hne
    · exact segG_r16_send_only nloc ngl t ht h15 i hi hb

/-- **Named obligation: the R16 send bound of `wasmBaseSegAirG`** (every RANGE16 query has count
`≤ 1`).  Honest traces satisfy it: every R16 count is a one-hot row flag or a product of bits (the
argument of `seg_hsend_r16`, plus MEMG `f_grow`/`act`, MEMBG `kD`/`p8`/`trans·p8·p0'`, MEMBH as MEMB). -/
def SegGSendR16 (nloc ngl : Nat) (pub : List F) (tr : Trace) : Prop :=
  ∀ o ∈ occs (wasmBaseSegAirG nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1

/-! ## MEMBG columns -/

abbrev mgN (tr : Trace) (r i : Nat) : Nat := rowNat tr 34 r i

theorem mg_ix : ix MembG.cols "act" = 0 ∧ ix MembG.cols "blk" = 10 ∧ ix MembG.cols "cidO" = 11 ∧
    ix MembG.cols "tg" = 12 ∧ ix MembG.cols "gold" = 13 ∧ ix MembG.cols "gnew" = 14 := by decide
theorem mg_ix_p : ∀ i, i < 9 → ix MembG.cols s!"p{i}" = 1 + i := by decide
set_option maxRecDepth 200000 in
theorem mg_ix_hoO : ∀ l, l < 18 → ix MembG.cols s!"hoO{l}" = 327 + l := by decide

section r16
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
  (hsend : SegGSendR16 nloc ngl pub tr)
include H hsend

/-- An R16 query (count 1) of table `t` of the grow AIR is `< 2^16`. -/
theorem segG_r16_lt {t : Nat} (ht : t < 36) {T : Table}
    (hT : (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht) = T)
    {r : Nat} (hr : r < tr.height t) {e c : Expr} (hi : r16 e c ∈ T.inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have hocc := occ_of_inter (segG_lt nloc ngl t ht) hr (by rw [hT]; exact hi) hc
  obtain ⟨x, hx, hxl⟩ := lookup_r16GX H hsend (regG_r16_recvX H (regAt_segG nloc ngl)) hocc rfl rfl rfl
  simp only [r16, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

theorem segG_col_lt {t : Nat} (ht : t < 36) {T : Table}
    (hT : (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht) = T)
    {r : Nat} (hr : r < tr.height t) {k : Nat} {c : Expr} (hi : r16 (v k) c ∈ T.inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) : rowNat tr t r k < 65536 := by
  have h := segG_r16_lt H hsend ht hT hr hi hc
  rwa [col_eval_nat, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at h

theorem segG_col32_lt {t : Nat} (ht : t < 36) {T : Table}
    (hT : (wasmBaseSegAirG nloc ngl).tables[t]'(segG_lt nloc ngl t ht) = T)
    {r : Nat} (hr : r < tr.height t) {k : Nat} {c : Expr} (hx : rowNat tr t r k < 65536)
    (hi : r16 (32 * v k) c ∈ T.inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) : rowNat tr t r k < 2048 := by
  have h := segG_r16_lt H hsend ht hT hr hi hc
  simp only [Expr.eval_mul', Expr.eval_ofNat', col_eval_nat] at h
  have hP := P_val
  rw [← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)] at h
  omega

/-! ## MEMG in the segment (table 32): M3's grow arithmetic -/

omit hsend in
theorem segG_memg_constr {r : Nat} (hr : r < tr.height 32) {e : Expr} (he : e ∈ MemG.table.constraints) :
    e.eval (tr.row pub 32 r) = 0 :=
  H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr e (by rw [segG_t32']; exact he)

omit hsend in
theorem segG_memg_act_cnt {r : Nat} (hr : r < tr.height 32) (hg : rowNat tr 32 r MemG.fGrow = 1) :
    (MemG.act.eval (tr.row pub 32 r)).toNat = 1 := by
  have hb := segG_memg_constr H hr (e := bool MemG.act) (by simp [MemG.table, MemG.constraints])
  have hs := segG_memg_constr H hr (e := bool (v MemG.fSize)) (by simp [MemG.table, MemG.constraints])
  simp only [Chips.bool, MemG.act, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat',
    col_eval_nat, hg] at hb hs ⊢
  rcases bool_nat (rowNat_lt tr 32 r MemG.fSize) hs with h0 | h1
  · rw [h0]; decide
  · rw [h1] at hb; exact absurd hb (by decide)

/-- **A successful `memory.grow` inside a segment: `old + n + d = 2048`** (`m3_grow_ok` on table 32). -/
theorem segG_grow_ok {r : Nat} (hr : r < tr.height 32)
    (hg : rowNat tr 32 r MemG.fGrow = 1) (hok : rowNat tr 32 r MemG.ok = 1) :
    rowNat tr 32 r MemG.old + (rowNat tr 32 r MemG.n0 + 65536 * rowNat tr 32 r MemG.n1) +
      rowNat tr 32 r MemG.d = maxPagesM3 := by
  have hT := segG_t32' nloc ngl
  have hc : ((v MemG.fGrow).eval (tr.row pub 32 r)).toNat = 1 := by rw [col_eval_nat, hg]; decide
  have ha := segG_memg_act_cnt H hr hg
  have hn0 := segG_col_lt H hsend (by decide) hT hr (k := MemG.n0) (by simp [MemG.table, MemG.inters]) hc
  have hn1' := segG_col_lt H hsend (by decide) hT hr (k := MemG.n1) (by simp [MemG.table, MemG.inters]) hc
  have hn1 := segG_col32_lt H hsend (by decide) hT hr (k := MemG.n1) hn1' (by simp [MemG.table, MemG.inters]) hc
  have hold := segG_col_lt H hsend (by decide) hT hr (k := MemG.old) (by simp [MemG.table, MemG.inters]) ha
  have hd := segG_col_lt H hsend (by decide) hT hr (k := MemG.d) (by simp [MemG.table, MemG.inters]) ha
  have h := segG_memg_constr H hr (e := MemG.cOk) (by simp [MemG.table, MemG.constraints])
  simp only [MemG.cOk, MemG.nE, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat',
    Expr.eval_c, col_eval_nat, hok, cast_one] at h
  have hP := P_val
  refine natEq ?_ (by omega) (by simp [maxPagesM3]; omega)
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  grind

/-- **A failed `memory.grow` inside a segment: `old + n = 2049 + e`.** -/
theorem segG_grow_fail {r : Nat} (hr : r < tr.height 32)
    (hg : rowNat tr 32 r MemG.fGrow = 1) (hok : rowNat tr 32 r MemG.ok = 0) :
    rowNat tr 32 r MemG.old + (rowNat tr 32 r MemG.n0 + 65536 * rowNat tr 32 r MemG.n1) =
      maxPagesM3 + 1 + (rowNat tr 32 r MemG.e0 + 65536 * rowNat tr 32 r MemG.e1) := by
  have hT := segG_t32' nloc ngl
  have hc : ((v MemG.fGrow).eval (tr.row pub 32 r)).toNat = 1 := by rw [col_eval_nat, hg]; decide
  have ha := segG_memg_act_cnt H hr hg
  have hn0 := segG_col_lt H hsend (by decide) hT hr (k := MemG.n0) (by simp [MemG.table, MemG.inters]) hc
  have hn1' := segG_col_lt H hsend (by decide) hT hr (k := MemG.n1) (by simp [MemG.table, MemG.inters]) hc
  have hn1 := segG_col32_lt H hsend (by decide) hT hr (k := MemG.n1) hn1' (by simp [MemG.table, MemG.inters]) hc
  have hold := segG_col_lt H hsend (by decide) hT hr (k := MemG.old) (by simp [MemG.table, MemG.inters]) ha
  have he0 := segG_col_lt H hsend (by decide) hT hr (k := MemG.e0) (by simp [MemG.table, MemG.inters]) ha
  have he1' := segG_col_lt H hsend (by decide) hT hr (k := MemG.e1) (by simp [MemG.table, MemG.inters]) ha
  have he1 := segG_col32_lt H hsend (by decide) hT hr (k := MemG.e1) he1' (by simp [MemG.table, MemG.inters]) ha
  have h := segG_memg_constr H hr (e := MemG.cFail) (by simp [MemG.table, MemG.constraints])
  simp only [MemG.cFail, MemG.nE, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat',
    Expr.eval_c, col_eval_nat, hok, hg, cast_one] at h
  have hP := P_val
  refine natEq ?_ (by omega) (by simp [maxPagesM3]; omega)
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, cast_one]
  grind

omit hsend in
/-- **Only a successful grow offers its range to MEMBG** (`gm·(1 − ok) = 0`). -/
theorem segG_grow_gm {r : Nat} (hr : r < tr.height 32) (hok : rowNat tr 32 r MemG.ok = 0) :
    rowNat tr 32 r MemG.gm = 0 := by
  have h := segG_memg_constr H hr (e := v MemG.gm * (1 - v MemG.ok)) (by simp [MemG.table, MemG.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', col_eval_nat, hok, cast_one] at h
  exact cast_zero_nat (rowNat_lt _ _ _ _) (by grind)

/-! ## MEMBG (table 34): a grown block lies in its grow's range, above `nblk_in` -/


omit hsend in
theorem membg_constr {r : Nat} (hr : r < tr.height 34) {e : Expr} (he : e ∈ MembG.constraints) :
    e.eval (tr.row pub 34 r) = 0 :=
  H.constr 34 (segG_lt nloc ngl 34 (by decide)) r hr e (by rw [segG_t34']; exact he)

/-- **A MEMBG padding row's block lies in its grow's range and above `nblk_in`**:
`64·gold ≤ blk < 64·gnew` and `nblk_in ≤ blk` (for `gold, gnew ≤ 2048`, `gnew ≥ 1` and `nblk_in ≤ 2^17`, which a
successful MEMG row (`segG_grow_ok`) and NEAR's 2048-page limit give). -/
theorem membg_range {r : Nat} (hr : r < tr.height 34) (hp8 : mgN tr r 9 = 1)
    (hold : mgN tr r 13 ≤ 2048) (hnew : mgN tr r 14 ≤ 2048) (hnew1 : 1 ≤ mgN tr r 14)
    (hnin : (pNin pub).toNat ≤ 2 ^ 17) :
    64 * mgN tr r 13 ≤ mgN tr r 10 ∧ mgN tr r 10 < 64 * mgN tr r 14 ∧ (pNin pub).toNat ≤ mgN tr r 10 := by
  simp only [mgN] at hold hnew hnew1 ⊢
  have hT := segG_t34' nloc ngl
  obtain ⟨-, ib, -, -, igo, ign⟩ := mg_ix
  have hc : ((MembG.p 8).eval (tr.row pub 34 r)).toNat = 1 := by
    rw [MembG.p, MembG.c, mg_ix_p 8 (by decide), col_eval_nat]
    have h9 : rowNat tr 34 r 9 = 1 := hp8
    rw [h9]; decide
  have hP := P_val
  have q1 := segG_r16_lt H hsend (by decide) hT hr (e := MembG.c "blk" - 64 * MembG.c "gold")
    (by simp [MembG.table, MembG.inters]) hc
  have q2 := segG_r16_lt H hsend (by decide) hT hr (e := 64 * MembG.c "gnew" - 1 - MembG.c "blk")
    (by simp [MembG.table, MembG.inters]) hc
  have q3 := segG_r16_lt H hsend (by decide) hT hr (e := MembG.c "blk" - pv pubNblkIn)
    (by simp [MembG.table, MembG.inters]) hc
  simp only [MembG.c, ib, igo, ign, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', col_eval_nat] at q1 q2 q3
  have pvx : (pv pubNblkIn).eval (tr.row pub 34 r) = pNin pub := by simp [Chips.pv, Expr.eval_pub, Trace.row]
  rw [pvx] at q3
  have hb := rowNat_lt tr 34 r 10
  -- each check: `x − y = k` in the field with `k < 2^16` and small `x, y`
  have sub_nat : ∀ x y : Nat, x < P → y < P → ((x : F) - (y : F)).toNat < 65536 → y ≤ x ∧ x - y < 65536 ∨
      x < y ∧ P - (y - x) < 65536 := by
    intro x y hx hy h
    rw [Fp.sub_def, Fp.toNat_sub, Fp.toNat_cast_of_lt hx, Fp.toNat_cast_of_lt hy] at h
    by_cases hxy : y ≤ x
    · left; refine ⟨hxy, ?_⟩
      rw [show x + (P - y) = (x - y) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h; exact h
    · right; refine ⟨by omega, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  have e64o : ((64 : Nat) : F) * ((rowNat tr 34 r 13 : Nat) : F) = ((64 * rowNat tr 34 r 13 : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_mul]
  have e64n : ((64 : Nat) : F) * ((rowNat tr 34 r 14 : Nat) : F) - ((1 : Nat) : F) =
      ((64 * rowNat tr 34 r 14 - 1 : Nat) : F) := by
    obtain ⟨k, hk⟩ : ∃ k, 64 * rowNat tr 34 r 14 = k + 1 := ⟨64 * rowNat tr 34 r 14 - 1, by
      have : 1 ≤ rowNat tr 34 r 14 := hnew1
      omega⟩
    rw [← Lean.Grind.Semiring.natCast_mul, hk, show k + 1 - 1 = k by omega, Lean.Grind.Semiring.natCast_add]
    grind
  rw [e64o] at q1
  rw [e64n] at q2
  have hnn : pNin pub = (((pNin pub).toNat : Nat) : F) := (Fp.ofNat_toNat _).symm
  rw [hnn] at q3
  rcases sub_nat _ _ hb (by omega) q1 with h1 | h1 <;>
  rcases sub_nat _ _ (by omega) hb q2 with h2 | h2 <;>
  rcases sub_nat _ _ hb (by omega) q3 with h3 | h3 <;>
  first
  | (refine ⟨by omega, ?_, by omega⟩
     have : 1 ≤ mgN tr r 14 := by omega
     omega)
  | omega

end r16

/-! ## MEMBG's leaf message: the old leaf of a grown block is `zleaf` -/

/-- `zleaf`'s limbs (`Grow.digC Grow.zleafW`), as field elements. -/
def zleafF : List F := (Grow.zleafW.flatMap wl).map fun n => ((n : Nat) : F)

/-- **Every leaf MEMBG sends on bus 15 is `[blk, 0] ++ limbs(zleaf) ++ out`**: a grown block's old
leaf digest is the constant `zleafW`, whose bytes are the spec's `zleaf` (`zleafW_bytes`). -/
theorem membg_leaf_parts (tr : Trace) (pub : List F) :
    ∀ m ∈ part MembG.table tr pub 34 15 true, ∃ r, r < tr.height 34 ∧
      m = [tr.cell 34 r 10, 0] ++ zleafF ++ (List.range 18).map (fun l => tr.cell 34 r (327 + l)) := by
  intro m hm
  unfold part at hm
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hm
  refine ⟨r, List.mem_range.mp hr, ?_⟩
  have hf : MembG.table.inters.filter (fun i => i.bus = 15 ∧ i.send = true) =
      [⟨busLeaf, true, MembG.p 8, [MembG.c "blk", 0] ++ Grow.digC Grow.zleafW ++ (names "hoO" 18).map MembG.c⟩] := by
    decide +kernel
  rw [rowMsgs_single _ _ _ _ _ _ _ _ hf] at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    have h1 : [MembG.c "blk", (0 : Expr)].map (fun x => Expr.eval (tr.row pub 34 r) x) = [tr.cell 34 r 10, 0] := by
      simp [MembG.c, Chips.v, Expr.eval, Trace.row, mg_ix.2.1]; rfl
    have h2 : (Grow.digC Grow.zleafW).map (fun x => Expr.eval (tr.row pub 34 r) x) = zleafF := by
      simp only [Grow.digC, zleafF, List.map_map]
      apply List.map_congr_left
      intro n _
      simp [Expr.eval]
    have h3 : ((names "hoO" 18).map MembG.c).map (fun x => Expr.eval (tr.row pub 34 r) x) =
        (List.range 18).map (fun l => tr.cell 34 r (327 + l)) := by
      simp only [names, List.map_map]
      apply List.map_congr_left
      intro l hl
      simp only [Function.comp, MembG.c, Chips.v, Expr.eval, Trace.row, mg_ix_hoO l (List.mem_range.mp hl)]
    show List.map (fun x => Expr.eval (tr.row pub 34 r) x)
      ([MembG.c "blk", 0] ++ Grow.digC Grow.zleafW ++ List.map MembG.c (names "hoO" 18)) = _
    rw [List.map_append, List.map_append, h1, h2, h3]
  · simp at hm

end WasmBase

#print axioms WasmBase.segG_msgs
#print axioms WasmBase.segG_state
#print axioms WasmBase.segG_rch_node
#print axioms WasmBase.segG_leaf
#print axioms WasmBase.segg_row0
#print axioms WasmBase.segg_rows
#print axioms WasmBase.segg_stubs
#print axioms WasmBase.segg_lift_nat
#print axioms WasmBase.segg_size_parts
#print axioms WasmBase.regAt_segG
#print axioms WasmBase.segG_grow_ok
#print axioms WasmBase.segG_grow_fail
#print axioms WasmBase.segG_grow_gm
#print axioms WasmBase.membg_range
#print axioms WasmBase.membg_leaf_parts
