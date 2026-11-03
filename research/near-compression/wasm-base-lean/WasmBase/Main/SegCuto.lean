import WasmBase.Main.SegSend
import WasmBase.Main.SegView

/-!
# WasmBase.Main.SegCuto — CUTO's hashed list on the trace is sorted and well formed (E2E M4b, S1)

CUTO (table 31) hashes the final live non-memory messages as 7-field vectors.  This file reads that
list off a satisfying `wasmBaseSegAir` trace and proves what `ctx_out_eq` needs from it:

* `cuto_bits`, **`cuto_prefix`**: the active CUTO rows form a prefix of the table (from the stream
  constraints: an inactive data row has `j = 1` and is followed by padding, padding by dead rows,
  dead rows by dead rows);
* `cuto_halves`, `cutoF_lt`: on an active row `lo_k < 2^16` (R16, `seg_r16_lt`/`seg_hsend_r16`),
  `hi_k < 2^14` (R16 on `4·hi_k` plus the chip's limb bound, `cut_hi`), so every field is `< 2^30`;
* `cuto_order_step` (`cut_order` on two consecutive active rows, with the R16 checks on `dlo`,
  `8·dhi`), `cuto_order`, **`cuto_sorted`**: `cutoList tr` is strictly increasing in
  `(space, slot)`; **`cuto_wf`**: every entry is `MsgWF`;
* **`seg_sound_cut_holds`**: `seg_sound_cut` with `H := cutoList tr`.

Named hypothesis: **`CutoHiLimbs tr`** — the SHA-512 chip's interface limbs are canonical (`< 2^21`),
in particular CUTO's `hi_k` on active rows (the chip contract, sub-lane S2 / lane B).  Still open:
the CUTO link (the members of `cutoList tr` are the kept depth-relabelled live messages), see
`Main/SegView.lean`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem cuto_ix : ix Cut.Out.cols "act" = 0 ∧ ix Cut.Out.cols "j" = 1 ∧ ix Cut.Out.cols "kD" = 2 ∧
    ix Cut.Out.cols "kP" = 3 ∧ ix Cut.Out.cols "kX" = 4 ∧ ix Cut.Out.cols "same" = 61 ∧
    ix Cut.Out.cols "dlo" = 62 ∧ ix Cut.Out.cols "dhi" = 63 := by decide

theorem cuto_ix_lo : ∀ k, k < 7 → ix Cut.Out.cols s!"lo{k}" = 5 + k := by decide
theorem cuto_ix_hi : ∀ k, k < 7 → ix Cut.Out.cols s!"hi{k}" = 12 + k := by decide

theorem row_cur (tr : Trace) (pub : List F) (t r i : Nat) :
    (tr.row pub t r).cur i = ((rowNat tr t r i : Nat) : F) := by
  simp only [Trace.row, rowNat, Fp.cast_toNat]

theorem row_nxt (tr : Trace) (pub : List F) {t r : Nat} (h : r + 1 < tr.height t) (i : Nat) :
    (tr.row pub t r).nxt i = ((rowNat tr t (r + 1) i : Nat) : F) := by
  simp only [Trace.row, Nat.mod_eq_of_lt h, rowNat, Fp.cast_toNat]

theorem row_trans (tr : Trace) (pub : List F) {t r : Nat} (h : r + 1 < tr.height t) :
    Expr.trans.eval (tr.row pub t r) = 1 := by
  have : (r + 1 == tr.height t) = false := by simp; omega
  simp only [Expr.eval, Trace.row, this]; rfl

theorem cuto_constr {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 31) {e : Expr} (he : e ∈ Cut.Out.constraints) :
    e.eval (tr.row pub 31 r) = 0 :=
  H.constr 31 (by simp [seg_air_len]) r hr e (by rw [seg_t31]; exact he)

theorem cuto_stream_mem {e : Expr} (h : e ∈ Cut.streamConstraints Cut.Out.cols pubCtxOut) :
    e ∈ Cut.Out.constraints := List.mem_append_left _ (List.mem_append_left _ h)


theorem one_F : ((1 : Nat) : F) = 1 := rfl
theorem zero_F : ((0 : Nat) : F) = 0 := rfl

/-- The stream bits of a CUTO row (`act j kD kP kX`) and `kD + kP + kX = 1`, `act → kD`. -/
theorem cuto_bits {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 31) :
    rowNat tr 31 r 0 ≤ 1 ∧ rowNat tr 31 r 1 ≤ 1 ∧ rowNat tr 31 r 2 ≤ 1 ∧ rowNat tr 31 r 3 ≤ 1 ∧ rowNat tr 31 r 4 ≤ 1 ∧
      rowNat tr 31 r 2 + rowNat tr 31 r 3 + rowNat tr 31 r 4 = 1 ∧ (rowNat tr 31 r 0 = 1 → rowNat tr 31 r 2 = 1) ∧
      (rowNat tr 31 r 2 = 1 → rowNat tr 31 r 0 = 0 → rowNat tr 31 r 1 = 1) := by
  obtain ⟨i0, i1, i2, i3, i4, -⟩ := cuto_ix
  have hC := fun e he => cuto_constr H hr (e := e) (cuto_stream_mem he)
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
theorem cuto_prefix {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r + 1 < tr.height 31) (ha : rowNat tr 31 (r + 1) 0 = 1) : rowNat tr 31 r 0 = 1 := by
  obtain ⟨i0, i1, i2, i3, i4, -⟩ := cuto_ix
  obtain ⟨a0, aj, aD, aP, aX, asum, aact, aj1⟩ := cuto_bits H (r := r) (by omega)
  obtain ⟨-, -, -, -, -, bsum, bact, -⟩ := cuto_bits H hr
  have bD := bact ha
  have bP : rowNat tr 31 (r + 1) 3 = 0 := by omega
  have bX : rowNat tr 31 (r + 1) 4 = 0 := by omega
  refine Classical.byContradiction fun hne => ?_
  have h0 : rowNat tr 31 r 0 = 0 := by omega
  have hC := fun e he => cuto_constr H (r := r) (by omega) (e := e) (cuto_stream_mem he)
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

/-! ## Field bounds and the order on the trace -/

/-- Field `k` of CUTO row `r` (`lo_k + 2^16·hi_k`), as a natural. -/
def cutoF (tr : Trace) (r k : Nat) : Nat := rowNat tr 31 r (5 + k) + 65536 * rowNat tr 31 r (12 + k)

/-- The 7 hashed fields of CUTO row `r`. -/
def cutoRow (tr : Trace) (r : Nat) : List Nat := (List.range 7).map (cutoF tr r)

/-- **CUTO's hashed list**: the fields of the active rows, in row order. -/
def cutoList (tr : Trace) : List (List Nat) :=
  ((List.range (tr.height 31)).filter (fun r => rowNat tr 31 r 0 = 1)).map (cutoRow tr)

/-- **The SHA chip's limb bound on CUTO's `hi` halves** (named hypothesis: the chip's canonical
interface limbs are `< 2^21`; `hi_k` is one of them on every active row — the chip contract of
sub-lane S2 / lane B). -/
def CutoHiLimbs (tr : Trace) : Prop :=
  ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → ∀ k, k < 7 → rowNat tr 31 r (12 + k) < 2 ^ 21

theorem cuto_inter {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 31) {e c : Expr} (hi : r16 e c ∈ Cut.Out.inters)
    (hc : (c.eval (tr.row pub 31 r)).toNat = 1) : (e.eval (tr.row pub 31 r)).toNat < 65536 :=
  seg_r16_lt H (seg_hsend_r16 H) (t := 31) (by simp [seg_air_len]) hr (by rw [seg_t31]; exact hi) hc

/-- The halves of an active CUTO row: `lo_k < 2^16`, `hi_k < 2^14`, so field `k` is `< 2^30`. -/
theorem cuto_halves {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
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
  have l1 := cuto_inter H hr m1 hc
  have l2 := cuto_inter H hr m2 hc
  simp only [Cut.c, cuto_ix_lo k hk, cuto_ix_hi k hk, v, Expr.eval_col, Expr.eval_mul', Expr.eval_ofNat',
    row_cur, Fp.toNat_cast_of_lt (rowNat_lt tr 31 r _)] at l1 l2
  exact ⟨l1, cut_hi (hl r hr ha k hk) l2⟩

theorem cutoF_lt {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1) {k : Nat} (hk : k < 7) :
    cutoF tr r k < 2 ^ 30 := by
  obtain ⟨a, b⟩ := cuto_halves H hl hr ha hk
  unfold cutoF; omega

theorem fcast (lo hi : Nat) :
    ((lo : Nat) : F) + ((65536 : Nat) : F) * ((hi : Nat) : F) = ((lo + 65536 * hi : Nat) : F) := by
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

/-- **CUTO's order on consecutive active rows** (`cut_order` on the trace). -/
theorem cuto_order_step {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hl : CutoHiLimbs tr) {r : Nat} (hr : r + 1 < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (hb : rowNat tr 31 (r + 1) 0 = 1) : keyLt (cutoRow tr r) (cutoRow tr (r + 1)) := by
  obtain ⟨i0, -, -, -, -, i61, i62, i63⟩ := cuto_ix
  have hr' : r < tr.height 31 := by omega
  have F0 := cutoF_lt H hl hr' ha (k := 0) (by omega)
  have F1 := cutoF_lt H hl hr' ha (k := 1) (by omega)
  have G0 := cutoF_lt H hl hr hb (k := 0) (by omega)
  have G1 := cutoF_lt H hl hr hb (k := 1) (by omega)
  have hC := fun e he => cuto_constr H hr' (e := e) he
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
  have l1 := cuto_inter H hr' m1 hc
  have l2 := cuto_inter H hr' m2 hc
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

theorem keyLt_trans {a b c : List Nat} (h1 : keyLt a b) (h2 : keyLt b c) : keyLt a c := by
  unfold keyLt at *; omega

/-- Order between any two active rows `r < r'` (all rows in between are active, `cuto_prefix`). -/
theorem cuto_order {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hl : CutoHiLimbs tr) : ∀ d r, r + d + 1 < tr.height 31 → rowNat tr 31 (r + d + 1) 0 = 1 →
      keyLt (cutoRow tr r) (cutoRow tr (r + d + 1))
  | 0, r, hr, hb => cuto_order_step H hl hr (cuto_prefix H hr hb) hb
  | d + 1, r, hr, hb => by
    have hm : rowNat tr 31 (r + d + 1) 0 = 1 := by
      have := cuto_prefix H (r := r + d + 1) (by omega) (by simpa [Nat.add_assoc] using hb); exact this
    have h1 := cuto_order H hl d r (by omega) hm
    have h2 := cuto_order_step H hl (r := r + d + 1) (by omega) hm (by simpa [Nat.add_assoc] using hb)
    have e : r + (d + 1) + 1 = r + d + 1 + 1 := by omega
    rw [e]; exact keyLt_trans h1 h2

/-- **CUTO's hashed list is strictly increasing in `(space, slot)`** on any satisfying segment trace
(given the chip's limb bound). -/
theorem cuto_sorted {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hl : CutoHiLimbs tr) : (cutoList tr).Pairwise keyLt := by
  unfold cutoList
  rw [List.pairwise_map, List.pairwise_filter, List.pairwise_iff_getElem]
  intro i j hi hj hij _ hb
  simp only [List.length_range] at hi hj
  simp only [List.getElem_range] at hb ⊢
  have := cuto_order H hl (j - i - 1) i (by omega) (by rw [show i + (j - i - 1) + 1 = j by omega]; simpa using hb)
  rwa [show i + (j - i - 1) + 1 = j by omega] at this

/-- **Every hashed CUTO message is `MsgWF`** (7 fields, each `< 2^30`). -/
theorem cuto_wf {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hl : CutoHiLimbs tr) : ∀ y ∈ cutoList tr, MsgWF y := by
  intro y hy
  simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
  obtain ⟨r, ⟨hr, ha⟩, rfl⟩ := hy
  refine ⟨by simp [cutoRow], fun f hf => ?_⟩
  simp only [cutoRow, List.mem_map, List.mem_range] at hf
  obtain ⟨k, hk, rfl⟩ := hf
  exact cutoF_lt H hl hr ha hk

#print axioms cuto_prefix
#print axioms cuto_order_step
#print axioms cuto_sorted
#print axioms cuto_wf

/-! ## Segment soundness with CUTO's list from the trace -/

/-- **`seg_sound_cut` with CUTO's hashed list read off the trace.**  As `seg_sound_cut`, with
`H := cutoList tr` of a satisfying `wasmBaseSegAir` trace: its order is `cuto_sorted` and its
`MsgWF` is `cuto_wf` (both from `Holds` and the chip limb bound), so, given the CUTO link `hcuto`,
`ctx_out = cutDigest (cutView X sN)` and every message of the view is `MsgWF`. -/
theorem seg_sound_cut_holds (X : Ctx) (hnd : X.M.fns.Nodup) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (Hh : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hl : CutoHiLimbs tr)
    {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ]
    (c : CutSeg X sg ρ) (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    (hreg : ∀ r ∈ c.act, RowQ X (fun s live => RegC live s) (c.inS r) (c.cons r) (c.prod r))
    (hsp : ∀ r ∈ c.act, RowQ X (fun _ live => SpC live) (c.inS r) (c.cons r) (c.prod r))
    (hwf : ∀ r ∈ c.act, RowQ X (fun s _ => RegWF s) (c.inS r) (c.cons r) (c.prod r))
    {s0 : St} (h0 : BndC X sg s0 c.t0 c.S0 c.m0 c.init) (hw0 : RegWF s0)
    (MemOut : St → Prop) (hmem : ∀ sN, Bnd X sg sN c.stop.t c.stop.S c.stop.m c.fin → MemOut sN)
    (ctxOut : ArenaCore.Bytes) (hsha : ctxOut = cutDigest (cutoList tr)) :
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p c.len s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (c.len + m) s0 = run X.cfg X.p m sN) ∧
      BndC X sg sN c.stop.t c.stop.S c.stop.m c.fin ∧ MemOut sN ∧
      ∃ (σ : Nat → Nat) (A : List Nat),
        BndC X sg sN c.stop.t c.stop.S (c.stop.m.set 5 ((sN.frames.length - 1 : Nat) : F))
          ((c.fin.filter (fun x => decide (keepA A x))).map (rlMsg σ)) ∧
        ((∀ y, y ∈ cutoList tr ↔ ∃ x ∈ (c.fin.filter (fun x => decide (keepA A x))).map (rlMsg σ),
            x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y) →
          cutoList tr = cutView X sN ∧ ctxOut = cutDigest (cutView X sN) ∧ ∀ y ∈ cutView X sN, MsgWF y) := by
  obtain ⟨sN, h1, h2, h3, h4, σ, A, h5, h6⟩ := seg_sound_cut X hnd c hc hstepgas hg64 hreg hsp hwf h0 hw0
    MemOut hmem (cutoList tr) (cuto_sorted Hh hl) ctxOut hsha
  refine ⟨sN, h1, h2, h3, h4, σ, A, h5, fun hcuto => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h6 hcuto
  exact ⟨e1, e2, e3 (cuto_wf Hh hl)⟩

#print axioms seg_sound_cut_holds

end WasmBase
