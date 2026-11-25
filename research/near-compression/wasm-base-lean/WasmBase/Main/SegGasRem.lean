import WasmBase.Main.SegCallSigma

/-!
# WasmBase.Main.SegGasRem — the out-boundary's gas register and stack budget as public values (E2E A-T5)

A-T5 adds nine public values to the segment AIR (`SegAir.lean`: `pubRemLo`, `pubRemHi`,
`pubGOut … +3`, `pubRop … +2`) and two gadgets.  This file proves what they bind, from the
relation `HoldsXS` (so for both segment AIRs).

* **`segb_gas_sound`** — `SEGB`'s gas gadget: with the wrapper's range checks on the publics
  (`g`-limbs and `segb`-limbs `< 2^16`, `R`-bytes `< 2^8`) and `S_seg,out ≤ S_out`,
  `gOutN pub + ropN pub · (S_out − S_seg,out) = gbOutN pub` over the naturals.  So the public
  `g_out` is the spec's gas register `segb − R·(S − S_seg)` at the out-cut (`RelW.gas`).
* **`cuto_rem_sound`** — `CUTO`'s budget rows: if CUTO's hashed list is the view `cutView X s`,
  the two public halves are the halves of `s.stackRem` (the view has exactly one space-5 message,
  `budMsg s.stackRem`, and `k5 · (F₃ − rem_lo) = k5 · (F₄ − rem_hi) = 0` on its row).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## Public decodings -/

/-- The `n`-limb little-endian value of the publics at `b` in base `2^w`. -/
def pubLimbs (pub : List F) (b w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pubLimbs pub b w n + 2 ^ (w * n) * (pub.getD (b + n) 0).toNat

/-- The public `g_out` (four 16-bit limbs). -/
def gOutN (pub : List F) : Nat := pubLimbs pub pubGOut 16 4
/-- The public out-boundary segment budget `segb_out` (four 16-bit limbs). -/
def gbOutN (pub : List F) : Nat := pubLimbs pub pubGbOut 16 4
/-- The public `R` (three bytes). -/
def ropN (pub : List F) : Nat := pubLimbs pub pubRop 8 3
/-- The public out-boundary stack budget. -/
def remN (pub : List F) : Nat := (pub.getD pubRemLo 0).toNat + 65536 * (pub.getD pubRemHi 0).toNat

/-- **The wrapper's range checks on the gas publics** (circuit checks on public values). -/
structure GasPubOK (pub : List F) : Prop where
  g : ∀ k, k < 4 → (pub.getD (pubGOut + k) 0).toNat < 2 ^ 16
  b : ∀ k, k < 4 → (pub.getD (pubGbOut + k) 0).toNat < 2 ^ 16
  r : ∀ i, i < 3 → (pub.getD (pubRop + i) 0).toNat < 2 ^ 8

/-! ## Bit sums -/

/-- `Σ_{j<n} 2^j · b j`. -/
def bsum (b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum b n + 2 ^ n * b n

theorem bsum_lt (b : Nat → Nat) : ∀ n, (∀ j, j < n → b j ≤ 1) → bsum b n < 2 ^ n
  | 0, _ => by simp [bsum]
  | n + 1, h => by
    have ih := bsum_lt b n (fun j hj => h j (by omega))
    have := h n (by omega)
    have : 2 ^ n * b n ≤ 2 ^ n := by
      calc 2 ^ n * b n ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ this
        _ = 2 ^ n := Nat.mul_one _
    simp only [bsum, Nat.pow_succ]; omega

theorem foldl_add_eval (rw : Row) : ∀ (l : List Expr) (a : Expr),
    (l.foldl (· + ·) a).eval rw = a.eval rw + (l.foldl (· + ·) (0 : Expr)).eval rw
  | [], a => by simp only [List.foldl_nil]; show _ = _ + ((0 : Nat) : F); grind
  | x :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_add_eval rw l (a + x), foldl_add_eval rw l (0 + x)]
    simp only [Expr.eval_add']
    show _ = _ + (((0 : Nat) : F) + _ + _)
    grind

/-- The evaluation of a bit-sum expression `Σ_{j<n} 2^j · col (f j)`. -/
theorem eval_bitsum (rw : Row) (f : Nat → Nat) : ∀ n,
    (sumE ((List.range n).map fun j => Expr.c (2 ^ j) * v (f j))).eval rw =
      ((bsum (fun j => (rw.cur (f j)).toNat) n : Nat) : F)
  | 0 => rfl
  | n + 1 => by
    have ih := eval_bitsum rw f n
    unfold sumE at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, Expr.eval_add', ih]
    simp only [bsum, Expr.eval_mul', v, Expr.eval]
    rw [← Fp.cast_toNat (rw.cur (f n))]
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt
      (Fp.toNat_lt _)]

/-! ## SEGB's gas gadget -/

namespace SegbG

theorem ix_gd : ∀ j, j < Segb.gdN → ix Segb.cols s!"gd{j}" = 4 + j := by decide
theorem ix_gc : ∀ j, j < Segb.gcN → ix Segb.cols s!"gc{j}" = 34 + j := by decide

theorem bitsAt_eq (p : String) (off len : Nat) (base : Nat)
    (hix : ∀ j, j < len → ix Segb.cols s!"{p}{off + j}" = base + off + j) :
    Segb.bitsAt p off len = sumE ((List.range len).map fun j => Expr.c (2 ^ j) * v (base + off + j)) := by
  unfold Segb.bitsAt
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  simp only [Segb.c, hix j hj]

end SegbG

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

theorem segb_constr {r : Nat} (hr : r < tr.height 0) {e : Expr} (he : e ∈ Segb.constraints) :
    e.eval (tr.row pub 0 r) = 0 :=
  H.constr 0 (by simp [seg_air_len]) r hr e (by rw [seg_t0]; exact he)

/-- A gadget bit of `SEGB` is 0 or 1. -/
theorem segb_bit {r : Nat} (hr : r < tr.height 0) {s : String} (hs : s ∈ names "gd" Segb.gdN ++ names "gc" Segb.gcN)
    {i : Nat} (hi : ix Segb.cols s = i) : rowNat tr 0 r i ≤ 1 := by
  have e := segb_constr H hr (e := bool (Segb.c s))
    (List.mem_append_left _ (List.mem_map_of_mem (f := fun s => bool (Segb.c s)) hs))
  simp only [Chips.bool, Segb.c, hi, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', row_cur] at e
  rcases bool_nat (rowNat_lt tr 0 r i) e with h | h <;> omega

theorem gd_bit {r : Nat} (hr : r < tr.height 0) {j : Nat} (hj : j < 30) : rowNat tr 0 r (4 + j) ≤ 1 :=
  segb_bit H hr (s := s!"gd{j}")
    (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) (SegbG.ix_gd j hj)

theorem gc_bit {r : Nat} (hr : r < tr.height 0) {j : Nat} (hj : j < 33) : rowNat tr 0 r (34 + j) ≤ 1 :=
  segb_bit H hr (s := s!"gc{j}")
    (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) (SegbG.ix_gc j hj)

end

/-- The bytes `δ_m` of `d`, the carries `c_k`, as naturals of a `SEGB` row. -/
def gdByte (tr : Trace) (r m : Nat) : Nat :=
  if m < 3 then bsum (fun j => rowNat tr 0 r (4 + 8 * m + j)) 8 else bsum (fun j => rowNat tr 0 r (4 + 24 + j)) 6
def gcK (tr : Trace) (r k : Nat) : Nat := bsum (fun j => rowNat tr 0 r (34 + 11 * k + j)) 11

theorem eval_dB (tr : Trace) (pub : List F) (r m : Nat) (hm : m < 4) :
    (Segb.dB m).eval (tr.row pub 0 r) = ((gdByte tr r m : Nat) : F) := by
  unfold Segb.dB gdByte
  by_cases h3 : m < 3
  · simp only [h3, ↓reduceIte]
    rw [SegbG.bitsAt_eq "gd" (8 * m) 8 4 (fun j hj => by rw [SegbG.ix_gd _ (by unfold Segb.gdN; omega)]; try omega)]
    rw [eval_bitsum]; rfl
  · simp only [h3, ↓reduceIte]
    rw [SegbG.bitsAt_eq "gd" 24 6 4 (fun j hj => by rw [SegbG.ix_gd _ (by unfold Segb.gdN; omega)]; try omega)]
    rw [eval_bitsum]; rfl

theorem eval_cK (tr : Trace) (pub : List F) (r k : Nat) (hk : k < 3) :
    (Segb.cK k).eval (tr.row pub 0 r) = ((gcK tr r k : Nat) : F) := by
  unfold Segb.cK gcK
  rw [SegbG.bitsAt_eq "gc" (11 * k) 11 34 (fun j hj => by rw [SegbG.ix_gc _ (by unfold Segb.gcN; omega)]; try omega)]
  rw [eval_bitsum]; rfl

theorem eval_pv (rw : Row) (i : Nat) : (pv i).eval rw = rw.pub i := rfl

theorem pub_cast (tr : Trace) (pub : List F) (i : Nat) :
    (pv i).eval (Trace.row tr pub 0 0) = (((pub.getD i 0).toNat : Nat) : F) := by
  simp only [eval_pv, Trace.row, Fp.cast_toNat]

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

theorem gdByte_lt {r : Nat} (hr : r < tr.height 0) {m : Nat} (hm : m < 4) : gdByte tr r m < 256 := by
  unfold gdByte
  split
  · have := bsum_lt (fun j => rowNat tr 0 r (4 + 8 * m + j)) 8
      (fun j hj => by have := gd_bit H hr (j := 8 * m + j) (by omega); rwa [← Nat.add_assoc] at this)
    exact this
  · have := bsum_lt (fun j => rowNat tr 0 r (4 + 24 + j)) 6
      (fun j hj => by have := gd_bit H hr (j := 24 + j) (by omega); rwa [← Nat.add_assoc] at this)
    exact Nat.lt_of_lt_of_le this (by decide)

theorem gdByte3_lt {r : Nat} (hr : r < tr.height 0) : gdByte tr r 3 < 64 := by
  unfold gdByte
  simp only [show ¬ (3 < 3) from by omega, ↓reduceIte]
  exact bsum_lt (fun j => rowNat tr 0 r (4 + 24 + j)) 6
    (fun j hj => by have := gd_bit H hr (j := 24 + j) (by omega); rwa [← Nat.add_assoc] at this)

theorem gcK_lt {r : Nat} (hr : r < tr.height 0) {k : Nat} (hk : k < 3) : gcK tr r k < 2048 := by
  unfold gcK
  exact bsum_lt _ 11 (fun j hj => by
    have := gc_bit H hr (j := 11 * k + j) (by omega); rwa [← Nat.add_assoc] at this)

/-- **The gas gadget, as naturals**: `g_out + R·(S_out − S_seg,out) = segb_out`. -/
theorem segb_gas_sound (hok : GasPubOK pub)
    (hle : (pub.getD pubSsegOut 0).toNat ≤ (pub.getD pubSOut 0).toNat) :
    gOutN pub + ropN pub * ((pub.getD pubSOut 0).toNat - (pub.getD pubSsegOut 0).toNat) = gbOutN pub := by
  have hP := P_val
  have h0 : 0 < tr.height 0 := by have := H.heightPos 0 (by simp [seg_air_len]); omega
  have C := fun e he => segb_constr H h0 (e := e) he
  -- the atoms
  let d0 := gdByte tr 0 0; let d1 := gdByte tr 0 1; let d2 := gdByte tr 0 2; let d3 := gdByte tr 0 3
  let c0 := gcK tr 0 0; let c1 := gcK tr 0 1; let c2 := gcK tr 0 2
  let q := fun i => (pub.getD (pubRop + i) 0).toNat
  let g := fun k => (pub.getD (pubGOut + k) 0).toNat
  let b := fun k => (pub.getD (pubGbOut + k) 0).toNat
  have bd0 : d0 < 256 := gdByte_lt H h0 (by omega)
  have bd1 : d1 < 256 := gdByte_lt H h0 (by omega)
  have bd2 : d2 < 256 := gdByte_lt H h0 (by omega)
  have bd3 : d3 < 64 := gdByte3_lt H h0
  have bc0 : c0 < 2048 := gcK_lt H h0 (by omega)
  have bc1 : c1 < 2048 := gcK_lt H h0 (by omega)
  have bc2 : c2 < 2048 := gcK_lt H h0 (by omega)
  have bq0 : q 0 < 256 := hok.r 0 (by omega)
  have bq1 : q 1 < 256 := hok.r 1 (by omega)
  have bq2 : q 2 < 256 := hok.r 2 (by omega)
  have bg : ∀ k, k < 4 → g k < 65536 := hok.g
  have bb : ∀ k, k < 4 → b k < 65536 := hok.b
  have ed := fun m (hm : m < 4) => eval_dB tr pub 0 m hm
  have ec := fun k (hk : k < 3) => eval_cK tr pub 0 k hk
  have ep := fun i => pub_cast tr pub i
  -- the products are below 2^16
  have pm : ∀ x y, x < 256 → y < 256 → x * y < 65536 := fun x y hx hy => by
    have : x * y ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have p00 := pm _ _ bq0 bd0; have p01 := pm _ _ bq0 bd1; have p02 := pm _ _ bq0 bd2
  have p03 := pm _ _ bq0 (by omega : d3 < 256)
  have p10 := pm _ _ bq1 bd0; have p11 := pm _ _ bq1 bd1; have p12 := pm _ _ bq1 bd2
  have p13 := pm _ _ bq1 (by omega : d3 < 256)
  have p20 := pm _ _ bq2 bd0; have p21 := pm _ _ bq2 bd1; have p22 := pm _ _ bq2 bd2
  have p23 := pm _ _ bq2 (by omega : d3 < 256)
  have g0 := bg 0 (by omega); have g1 := bg 1 (by omega); have g2 := bg 2 (by omega); have g3 := bg 3 (by omega)
  have b0 := bb 0 (by omega); have b1 := bb 1 (by omega); have b2 := bb 2 (by omega); have b3 := bb 3 (by omega)
  -- (1) d
  have eD := C Segb.gasD (by simp [Segb.constraints])
  simp only [Segb.gasD, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', ed 0 (by omega),
    ed 1 (by omega), ed 2 (by omega), ed 3 (by omega), ep] at eD
  have hD : d0 + 256 * d1 + 65536 * d2 + 16777216 * d3 =
      (pub.getD pubSOut 0).toNat - (pub.getD pubSsegOut 0).toNat := by
    have hSl := (pub.getD pubSOut 0).toNat_lt
    have e : ((d0 + 256 * d1 + 65536 * d2 + 16777216 * d3 : Nat) : F) =
        (((pub.getD pubSOut 0).toNat - (pub.getD pubSsegOut 0).toNat : Nat) : F) := by
      have hc : (((pub.getD pubSOut 0).toNat : Nat) : F) =
          (((pub.getD pubSOut 0).toNat - (pub.getD pubSsegOut 0).toNat : Nat) : F) +
            (((pub.getD pubSsegOut 0).toNat : Nat) : F) := by
        rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel hle]
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at eD ⊢
      grind
    exact natEq e (by omega) (by omega)
  -- (2) the four limb equations
  have L0 := C Segb.gas0 (by simp [Segb.constraints])
  have L1 := C Segb.gas1 (by simp [Segb.constraints])
  have L2 := C Segb.gas2 (by simp [Segb.constraints])
  have L3 := C Segb.gas3 (by simp [Segb.constraints])
  simp only [Segb.gas0, Segb.gas1, Segb.gas2, Segb.gas3, Segb.U0, Segb.U1, Segb.U2, Segb.gL, Segb.bL,
    Segb.rho, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', ed 0 (by omega),
    ed 1 (by omega), ed 2 (by omega), ed 3 (by omega), ec 0 (by omega), ec 1 (by omega), ec 2 (by omega),
    ep] at L0 L1 L2 L3
  have n0 : g 0 + (q 0 * d0 + 256 * (q 0 * d1 + q 1 * d0)) = b 0 + 65536 * c0 := by
    refine natEq ?_ (by omega) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at L0 ⊢
    grind
  have n1 : g 1 + (q 0 * d2 + q 1 * d1 + q 2 * d0 + 256 * (q 0 * d3 + q 1 * d2 + q 2 * d1)) + c0 =
      b 1 + 65536 * c1 := by
    refine natEq ?_ (by omega) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at L1 ⊢
    grind
  have n2 : g 2 + (q 1 * d3 + q 2 * d2 + 256 * (q 2 * d3)) + c1 = b 2 + 65536 * c2 := by
    refine natEq ?_ (by omega) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at L2 ⊢
    grind
  have n3 : g 3 + c2 = b 3 := by
    refine natEq ?_ (by omega) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at L3 ⊢
    grind
  -- (3) assemble
  rw [← hD]
  have eg : gOutN pub = g 0 + 65536 * g 1 + 4294967296 * g 2 + 281474976710656 * g 3 := by
    simp only [gOutN, pubLimbs, g]; omega
  have eb : gbOutN pub = b 0 + 65536 * b 1 + 4294967296 * b 2 + 281474976710656 * b 3 := by
    simp only [gbOutN, pubLimbs, b]; omega
  have er : ropN pub = q 0 + 256 * q 1 + 65536 * q 2 := by
    simp only [ropN, pubLimbs, q]; omega
  rw [eg, eb, er]
  grind

end

/-! ## CUTO's budget row -/

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- An active CUTO row whose hashed space field is 5 has `k5 = 1`. -/
theorem cuto_k5_of_five (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (h5 : cutoF tr r 0 = 5) : rowNat tr 31 r 54 = 1 := by
  obtain ⟨-, b52, b53, b54, b55, b56, hsum⟩ := cuto_kindsS H hr
  have ff := cuto_fieldfactsS H hl hr ha
  by_cases hL : rowNat tr 31 r 56 = 1
  · exfalso
    obtain ⟨-, -, h⟩ := cuto_kL_lookupS H hl hr ha hL
    rcases h with ⟨-, h⟩ | ⟨r', -, -, -, -, h⟩ <;> omega
  · have hL0 : rowNat tr 31 r 56 = 0 := by omega
    obtain ⟨e1, e2⟩ := ff.1 hL0
    omega

/-- **The public stack budget is the out-state's** (`remN pub = s.stackRem`), when CUTO's hashed list
is the view of `s`. -/
theorem cuto_rem_sound (hl : CutoHiLimbs tr) {X : Ctx} {s : St} (hv : cutoList tr = cutView X s) :
    remN pub = s.stackRem := by
  have hP := P_val
  have hm : fieldsOf (budMsg s.stackRem 0) ∈ cutoList tr := by
    rw [hv]
    exact mem_cutView.mpr ⟨budMsg s.stackRem 0, by simp [cutMsgs], rfl⟩
  simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
  obtain ⟨r, ⟨hr, ha⟩, hrow⟩ := hm
  rw [cutoRow_eq] at hrow
  simp only [fieldsOf, budMsg, List.cons.injEq, and_true] at hrow
  obtain ⟨h0, -, -, h3, h4, -⟩ := hrow
  have hk5 := cuto_k5_of_five H hl hr ha h0
  have i54 : ix Cut.Out.cols "k5" = 54 := by decide
  have eLo := cuto_constrS H hr (e := Cut.Out.c "k5" * (Cut.Out.F 3 - pv pubRemLo))
    (by simp [Cut.Out.constraints])
  have eHi := cuto_constrS H hr (e := Cut.Out.c "k5" * (Cut.Out.F 4 - pv pubRemHi))
    (by simp [Cut.Out.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', cuto_evalc tr pub r i54, hk5,
    cuto_evalF tr pub r (show 3 < 7 by omega), cuto_evalF tr pub r (show 4 < 7 by omega), eval_pv] at eLo eHi
  have hpb : ∀ i, (tr.row pub 31 r).pub i = pub.getD i 0 := fun _ => rfl
  simp only [hpb] at eLo eHi
  have f3 := cutoF_ltS H hl hr ha (k := 3) (by omega)
  have f4 := cutoF_ltS H hl hr ha (k := 4) (by omega)
  have lo : (pub.getD pubRemLo 0).toNat = cutoF tr r 3 := by
    have : pub.getD pubRemLo 0 = ((cutoF tr r 3 : Nat) : F) := by
      have e1 : ((1 : Nat) : F) = 1 := rfl
      try simp only [e1] at eLo
      grind
    rw [this, Fp.toNat_cast_of_lt (by omega)]
  have hi : (pub.getD pubRemHi 0).toNat = cutoF tr r 4 := by
    have : pub.getD pubRemHi 0 = ((cutoF tr r 4 : Nat) : F) := by
      have e1 : ((1 : Nat) : F) = 1 := rfl
      try simp only [e1] at eHi
      grind
    rw [this, Fp.toNat_cast_of_lt (by omega)]
  unfold remN
  rw [lo, hi, h3, h4]
  omega

end

/-! ## On a cut segment of the merged chain -/

namespace Cuti

/-- **CUTO hashes the view of the successor state** of a cut segment (`seg_sound_cσS`'s
`cutoList = cutView`, for the state `seg n s = .cont sN`). -/
theorem seg_cutoView_AMP (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St}
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64) {d : SegD} (hp : SegPremAMP X nloc ngl sg σ d) {s sN : St}
    (hin : InSA X sg σ d s) (hseg : NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont sN) :
    cutoList d.tr = cutView X.toCtx sN := by
  have hP := P_val
  obtain ⟨⟨⟨h0, hw, hinit, -⟩, -, -, -⟩, hσ0⟩ := hin
  obtain ⟨HM, hCM, hl, hcode, hfunc, hkeep, hsk, hhold, hrely, hst0, hlen, htin, hfeeN, -, -⟩ := hp
  have H := HM.toSMP
  have hC := SegSha.ChipIf.toSMP HM hCM
  obtain ⟨hlenEq, sN', h1, -, -, h4, -⟩ :=
    seg_sound_cσS X H hC hl hcode hfunc (seg_hostBLinkedL H) (seg_regCLinked H) hkeep hsk hhold hrely hst0
      hlen htin hfeeN hstepgas hg64 hinit h0 hw hσ0
  have en : d.n = (actListM2 d.tr d.pub).length := rfl
  rw [en, h1] at hseg
  cases hseg
  exact h4

end Cuti

#print axioms bsum_lt
#print axioms eval_bitsum
#print axioms segb_gas_sound
#print axioms cuto_k5_of_five
#print axioms cuto_rem_sound

end WasmBase
