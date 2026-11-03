import WasmBase.Main.SegCuto
import WasmBase.Main.SegS.SegSend
/-!
# WasmBase.Main.SegS.SegCuto — `SegCuto`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegCuto.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem cuto_constrS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r < tr.height 31) {e : Expr} (he : e ∈ Cut.Out.constraints) :
    e.eval (tr.row pub 31 r) = 0 :=
  H.constr 31 (by simp [seg_air_len]) r hr e (by rw [seg_t31]; exact he)

/-- The stream bits of a CUTO row (`act j kD kP kX`) and `kD + kP + kX = 1`, `act → kD`. -/
theorem cuto_bitsS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r < tr.height 31) :
    rowNat tr 31 r 0 ≤ 1 ∧ rowNat tr 31 r 1 ≤ 1 ∧ rowNat tr 31 r 2 ≤ 1 ∧ rowNat tr 31 r 3 ≤ 1 ∧ rowNat tr 31 r 4 ≤ 1 ∧
      rowNat tr 31 r 2 + rowNat tr 31 r 3 + rowNat tr 31 r 4 = 1 ∧ (rowNat tr 31 r 0 = 1 → rowNat tr 31 r 2 = 1) ∧
      (rowNat tr 31 r 2 = 1 → rowNat tr 31 r 0 = 0 → rowNat tr 31 r 1 = 1) := by
  obtain ⟨i0, i1, i2, i3, i4, -⟩ := cuto_ix
  have hC := fun e he => cuto_constrS H hr (e := e) (cuto_stream_mem he)
  have hP := rowNat_lt tr 31 r
  have b : ∀ s i, ix Cut.Out.cols s = i → bool (Cut.c Cut.Out.cols s) ∈ Cut.streamConstraints Cut.Out.cols pubCtxOut →
      rowNat tr 31 r i = 0 ∨ rowNat tr 31 r i = 1 := by
    intro s i hi hm
    have e := hC _ hm
    simp only [Chips.bool, Cut.c, hi, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      row_cur] at e
    exact bool_nat (hP i) e
  have ba := b "act" 0 i0 (by simp [Cut.streamConstraints])
  have bj := b "j" 1 i1 (by simp [Cut.streamConstraints])
  have bD := b "kD" 2 i2 (by simp [Cut.streamConstraints])
  have bP := b "kP" 3 i3 (by simp [Cut.streamConstraints])
  have bX := b "kX" 4 i4 (by simp [Cut.streamConstraints])
  have e1 := hC (Cut.c Cut.Out.cols "kD" + Cut.c Cut.Out.cols "kP" + Cut.c Cut.Out.cols "kX" - 1)
    (by simp [Cut.streamConstraints])
  have e2 := hC ((1 - Cut.c Cut.Out.cols "kD") * Cut.c Cut.Out.cols "act") (by simp [Cut.streamConstraints])
  have e3 := hC (Cut.c Cut.Out.cols "kD" * (1 - Cut.c Cut.Out.cols "act") * (1 - Cut.c Cut.Out.cols "j"))
    (by simp [Cut.streamConstraints])
  simp only [Cut.c, i0, i1, i2, i3, i4, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col,
    Expr.eval_ofNat', row_cur] at e1 e2 e3
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rcases bD with hD | hD <;> rcases bP with hP' | hP' <;> rcases bX with hX | hX <;>
      rw [hD, hP', hX] at e1 <;> first | omega | (exfalso; revert e1; decide)
  · intro ha; rcases bD with hD | hD
    · rw [hD, ha] at e2; exfalso; revert e2; decide
    · exact hD
  · intro hD ha; rcases bj with hj | hj
    · rw [hD, ha, hj] at e3; exfalso; revert e3; decide
    · exact hj

/-- **Active CUTO rows form a prefix**: an active row's predecessor is active.  (An inactive data row
has `j = 1` and is followed by the padding group; padding is followed by dead rows; dead rows by dead
rows: none of them can precede a data row.) -/
theorem cuto_prefixS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r + 1 < tr.height 31) (ha : rowNat tr 31 (r + 1) 0 = 1) : rowNat tr 31 r 0 = 1 := by
  obtain ⟨i0, i1, i2, i3, i4, -⟩ := cuto_ix
  obtain ⟨a0, aj, aD, aP, aX, asum, aact, aj1⟩ := cuto_bitsS H (r := r) (by omega)
  obtain ⟨-, -, -, -, -, bsum, bact, -⟩ := cuto_bitsS H hr
  have bD := bact ha
  have bP : rowNat tr 31 (r + 1) 3 = 0 := by omega
  have bX : rowNat tr 31 (r + 1) 4 = 0 := by omega
  refine Classical.byContradiction fun hne => ?_
  have h0 : rowNat tr 31 r 0 = 0 := by omega
  have hC := fun e he => cuto_constrS H (r := r) (by omega) (e := e) (cuto_stream_mem he)
  have c5 := hC (Expr.trans * (1 - Cut.c Cut.Out.cols "kX") * (1 - Cut.c Cut.Out.cols "j") *
    (Cut.n Cut.Out.cols "kP" - Cut.c Cut.Out.cols "kP")) (by simp [Cut.streamConstraints])
  have c6 := hC (Expr.trans * Cut.c Cut.Out.cols "j" * Cut.c Cut.Out.cols "kP" * (1 - Cut.n Cut.Out.cols "kX"))
    (by simp [Cut.streamConstraints])
  have c7 := hC (Expr.trans * Cut.c Cut.Out.cols "kX" * (1 - Cut.n Cut.Out.cols "kX"))
    (by simp [Cut.streamConstraints])
  have c8 := hC (Expr.trans * Cut.c Cut.Out.cols "kD" * (1 - Cut.c Cut.Out.cols "act") *
    (1 - Cut.n Cut.Out.cols "kP")) (by simp [Cut.streamConstraints])
  simp only [Cut.c, Cut.n, i0, i1, i2, i3, i4, v, nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', row_cur, row_nxt tr pub hr, row_trans tr pub hr, bP, bX, h0] at c5 c6 c7 c8
  have hD3 : rowNat tr 31 r 2 = 1 ∨ rowNat tr 31 r 3 = 1 ∨ rowNat tr 31 r 4 = 1 := by omega
  rcases hD3 with hD | hP | hX
  · have hj := aj1 hD h0
    rw [hD] at c8; revert c8; decide
  · have hD0 : rowNat tr 31 r 2 = 0 := by omega
    have hX0 : rowNat tr 31 r 4 = 0 := by omega
    rcases (by omega : rowNat tr 31 r 1 = 0 ∨ rowNat tr 31 r 1 = 1) with hj | hj
    · rw [hX0, hj, hP] at c5; revert c5; decide
    · rw [hj, hP] at c6; revert c6; decide
  · rw [hX] at c7; revert c7; decide

theorem cuto_interS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r < tr.height 31) {e c : Expr} (hi : r16 e c ∈ Cut.Out.inters)
    (hc : (c.eval (tr.row pub 31 r)).toNat = 1) : (e.eval (tr.row pub 31 r)).toNat < 65536 :=
  seg_r16_ltS H (seg_hsend_r16S H) (t := 31) (by simp [seg_air_len]) hr (by rw [seg_t31]; exact hi) hc

/-- The halves of an active CUTO row: `lo_k < 2^16`, `hi_k < 2^14`, so field `k` is `< 2^30`. -/
theorem cuto_halvesS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) {k : Nat} (hk : k < 7) :
    rowNat tr 31 r (5 + k) < 2 ^ 16 ∧ rowNat tr 31 r (12 + k) < 2 ^ 14 := by
  obtain ⟨i0, -⟩ := cuto_ix
  have hc : ((Cut.c Cut.Out.cols "act").eval (tr.row pub 31 r)).toNat = 1 := by
    simp only [Cut.c, i0, v, Expr.eval_col, row_cur, ha]; rfl
  have m1 : r16 (Cut.c Cut.Out.cols s!"lo{k}") (Cut.c Cut.Out.cols "act") ∈ Cut.Out.inters := by
    simp only [Cut.Out.inters, Cut.Out.c, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨k, hk, by simp⟩))
  have m2 : r16 (4 * Cut.c Cut.Out.cols s!"hi{k}") (Cut.c Cut.Out.cols "act") ∈ Cut.Out.inters := by
    simp only [Cut.Out.inters, Cut.Out.c, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨k, hk, by simp⟩))
  have l1 := cuto_interS H hr m1 hc
  have l2 := cuto_interS H hr m2 hc
  simp only [Cut.c, cuto_ix_lo k hk, cuto_ix_hi k hk, v, Expr.eval_col, Expr.eval_mul', Expr.eval_ofNat',
    row_cur, Fp.toNat_cast_of_lt (rowNat_lt tr 31 r _)] at l1 l2
  exact ⟨l1, cut_hi (hl r hr ha k hk) l2⟩

theorem cutoF_ltS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) {k : Nat} (hk : k < 7) :
    cutoF tr r k < 2 ^ 30 := by
  obtain ⟨a, b⟩ := cuto_halvesS H hl hr ha hk
  unfold cutoF; omega

/-- **CUTO's order on consecutive active rows** (`cut_order` on the trace). -/
theorem cuto_order_stepS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hl : CutoHiLimbs tr) {r : Nat} (hr : r + 1 < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (hb : rowNat tr 31 (r + 1) 0 = 1) : keyLt (cutoRow tr r) (cutoRow tr (r + 1)) := by
  obtain ⟨i0, -, -, -, -, i61, i62, i63⟩ := cuto_ix
  have hr' : r < tr.height 31 := by omega
  have F0 := cutoF_ltS H hl hr' ha (k := 0) (by omega)
  have F1 := cutoF_ltS H hl hr' ha (k := 1) (by omega)
  have G0 := cutoF_ltS H hl hr hb (k := 0) (by omega)
  have G1 := cutoF_ltS H hl hr hb (k := 1) (by omega)
  have hC := fun e he => cuto_constrS H hr' (e := e) he
  -- `same` is a bit
  have bs := hC (bool (Cut.Out.c "same")) (by simp [Cut.Out.constraints])
  simp only [Chips.bool, Cut.Out.c, Cut.c, i61, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', row_cur] at bs
  have hsm := bool_nat (rowNat_lt tr 31 r 61) bs
  -- the two order constraints
  have e1 := hC (Cut.Out.c "act" * Cut.Out.n "act" * Cut.Out.c "same" * (Cut.Out.Fn 0 - Cut.Out.F 0))
    (by simp [Cut.Out.constraints])
  have e2 := hC (Cut.Out.c "act" * Cut.Out.n "act" * (Cut.Out.c "same" * (Cut.Out.Fn 1 - Cut.Out.F 1 - 1) +
    (1 - Cut.Out.c "same") * (Cut.Out.Fn 0 - Cut.Out.F 0 - 1) - Cut.Out.c "dlo" - 65536 * Cut.Out.c "dhi"))
    (by simp [Cut.Out.constraints])
  simp only [Cut.Out.c, Cut.Out.n, Cut.Out.F, Cut.Out.Fn, Cut.F, Cut.Fn, Cut.c, Cut.n, i0, i61, i62, i63,
    cuto_ix_lo 0 (by omega), cuto_ix_lo 1 (by omega), cuto_ix_hi 0 (by omega), cuto_ix_hi 1 (by omega),
    v, nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col, Expr.eval_nxt, Expr.eval_ofNat',
    row_cur, row_nxt tr pub hr, ha, hb, fcast] at e1 e2
  -- the R16 checks on `dlo`, `8·dhi` (count `act · act'` = 1)
  have hc : ((Cut.Out.c "act" * Cut.Out.n "act").eval (tr.row pub 31 r)).toNat = 1 := by
    simp only [Cut.Out.c, Cut.Out.n, Cut.c, Cut.n, i0, v, nv, Expr.eval_mul', Expr.eval_col, Expr.eval_nxt,
      row_cur, row_nxt tr pub hr, ha, hb]; rfl
  have m1 : r16 (Cut.Out.c "dlo") (Cut.Out.c "act" * Cut.Out.n "act") ∈ Cut.Out.inters := by
    simp [Cut.Out.inters]
  have m2 : r16 (8 * Cut.Out.c "dhi") (Cut.Out.c "act" * Cut.Out.n "act") ∈ Cut.Out.inters := by
    simp [Cut.Out.inters]
  have l1 := cuto_interS H hr' m1 hc
  have l2 := cuto_interS H hr' m2 hc
  simp only [Cut.Out.c, Cut.c, i62, i63, v, Expr.eval_col, Expr.eval_mul', Expr.eval_ofNat', row_cur,
    Fp.toNat_cast_of_lt (rowNat_lt tr 31 r _)] at l1 l2
  have one1 : ((1 : Nat) : F) * ((1 : Nat) : F) = 1 := by decide
  rw [one1] at e1 e2
  have e1' : ((rowNat tr 31 r 61 : Nat) : F) * (((cutoF tr (r + 1) 0 : Nat) : F) - ((cutoF tr r 0 : Nat) : F)) = 0 := by
    unfold cutoF; grind
  have e2' : ((rowNat tr 31 r 61 : Nat) : F) * (((cutoF tr (r + 1) 1 : Nat) : F) - ((cutoF tr r 1 : Nat) : F) - 1) +
      (1 - ((rowNat tr 31 r 61 : Nat) : F)) * (((cutoF tr (r + 1) 0 : Nat) : F) - ((cutoF tr r 0 : Nat) : F) - 1) -
      ((rowNat tr 31 r 62 : Nat) : F) - ((65536 : Nat) : F) * ((rowNat tr 31 r 63 : Nat) : F) = 0 := by
    unfold cutoF; grind
  have o := cut_order F0 F1 G0 G1 (by omega) l1 l2 e1' e2'
  simp only [keyLt, cutoRow, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : 0 < 7),
    List.getElem?_range (by omega : 1 < 7), Option.map_some, Option.getD_some]
  omega

/-- Order between any two active rows `r < r'` (all rows in between are active, `cuto_prefixS`). -/
theorem cuto_orderS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hl : CutoHiLimbs tr) : ∀ d r, r + d + 1 < tr.height 31 → rowNat tr 31 (r + d + 1) 0 = 1 →
      keyLt (cutoRow tr r) (cutoRow tr (r + d + 1))
  | 0, r, hr, hb => cuto_order_stepS H hl hr (cuto_prefixS H hr hb) hb
  | d + 1, r, hr, hb => by
    have hm : rowNat tr 31 (r + d + 1) 0 = 1 := by
      have := cuto_prefixS H (r := r + d + 1) (by omega) (by simpa [Nat.add_assoc] using hb); exact this
    have h1 := cuto_orderS H hl d r (by omega) hm
    have h2 := cuto_order_stepS H hl (r := r + d + 1) (by omega) hm (by simpa [Nat.add_assoc] using hb)
    have e : r + (d + 1) + 1 = r + d + 1 + 1 := by omega
    rw [e]; exact keyLt_trans h1 h2

/-- **CUTO's hashed list is strictly increasing in `(space, slot)`** on any satisfying segment trace
(given the chip's limb bound). -/
theorem cuto_sortedS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hl : CutoHiLimbs tr) : (cutoList tr).Pairwise keyLt := by
  unfold cutoList
  rw [List.pairwise_map, List.pairwise_filter, List.pairwise_iff_getElem]
  intro i j hi hj hij _ hb
  simp only [List.length_range] at hi hj
  simp only [List.getElem_range] at hb ⊢
  have := cuto_orderS H hl (j - i - 1) i (by omega) (by rw [show i + (j - i - 1) + 1 = j by omega]; simpa using hb)
  rwa [show i + (j - i - 1) + 1 = j by omega] at this

/-- **Every hashed CUTO message is `MsgWF`** (7 fields, each `< 2^30`). -/
theorem cuto_wfS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hl : CutoHiLimbs tr) : ∀ y ∈ cutoList tr, MsgWF y := by
  intro y hy
  simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
  obtain ⟨r, ⟨hr, ha⟩, rfl⟩ := hy
  refine ⟨by simp [cutoRow], fun f hf => ?_⟩
  simp only [cutoRow, List.mem_map, List.mem_range] at hf
  obtain ⟨k, hk, rfl⟩ := hf
  exact cutoF_ltS H hl hr ha hk

end WasmBase
