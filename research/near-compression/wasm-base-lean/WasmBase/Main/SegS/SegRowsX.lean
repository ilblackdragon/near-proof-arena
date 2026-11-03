import WasmBase.Main.SegRowsX
import WasmBase.Main.SegS.SegBus
/-!
# WasmBase.Main.SegS.SegRowsX — `SegRowsX`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegRowsX.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- A segment trace satisfies the base AIR's constraints on `segBase tr`, for any `nloc'`, `ngl'`
and any public values (the kept tables mention none). -/
theorem seg_base_holdsCS' (nloc' ngl' : Nat) (pub' : List F) :
    HoldsC (wasmBaseAir nloc' ngl') pub' (segBase tr) := by
  refine ⟨fun t ht r hr e he => ?_⟩
  have h22 : t < 22 := by rwa [air_len] at ht
  by_cases hg : baseGone t
  · simp [segBase, hg] at hr
  · have h0 : t ≠ 0 := by unfold baseGone at hg; omega
    rw [segBase_height hg] at hr
    rw [segBase_row hg]
    have hnp := base_noPub nloc' ngl' t h22 hg
    rw [← Expr.eval_noPub tr pub pub' t r e (noPub_cons hnp e he)]
    rw [base_table_indep nloc' ngl' nloc ngl t h22 h0, seg_base_constraints nloc ngl t h22 hg] at he
    have : SegT t := ⟨by unfold baseGone at hg; omega⟩
    exact H.constr t _ r hr e he

/-- **The FETCH/FUNC send bounds of `wasmBaseSegAir`.** -/
theorem seg_hsend_ffS {b : Nat} (hb : b = busFetch ∨ b = busFunc) :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hbo hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hbo hs ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have : SegT t := ⟨by omega⟩
    have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqXS H ht (chipT t) hT hr
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
      table_constr_eqXS H ht RetT.table (seg_t14' nloc ngl) hr
    rw [seg_t14'] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ret_counts_of hcon i hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; rcases hb with rfl | rfl <;> exact absurd hbo (by decide)
  · have hok := seg_sendsOkFF nloc ngl t ht (by omega)
    by_cases h20 : t = 20
    · subst h20; rcases hb with rfl | rfl <;> exact absurd hbo (seg_t20_noBus nloc ngl (by decide) hi)
    have : SegT t := ⟨h20⟩
    rcases hb with rfl | rfl
    · exact SegSha.le_of_sendsOkBS H ht hok.1 hr hi hbo hs
    · exact SegSha.le_of_sendsOkBS H ht hok.2 hr hi hbo hs

/-- **FETCH lookup soundness on the segment AIR.** -/
theorem seg_fetchS (X : Ctx) (hcode : CodeOK X tr) {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub)
    (hb : o.1 = busFetch) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRec X j := by
  refine lookup_soundXS H busFetch (by decide) (fun m => ∃ j, j < X.M.codeSize ∧ m = codeRec X j) ?_
    (seg_hsend_ffS H (Or.inl rfl)) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h17 : t = 17
  · subst h17
    rw [seg_t17] at hi
    simp only [Code.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    obtain ⟨j, hj, he⟩ := hcode r hr
    refine ⟨j, hj, ?_⟩
    rw [← he]
    simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row, Boundary.recWidth]
  · exact absurd (seg_recv_fetch nloc ngl t ht h17 i hi hb') (by simp [hs'])

/-- **FUNC lookup soundness on the segment AIR.** -/
theorem seg_funcS (X : Ctx) (hfunc : FuncOK X tr) {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub)
    (hb : o.1 = busFunc) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ k, k < X.nf ∧ o.2.2.1 = funcRec X k := by
  refine lookup_soundXS H busFunc (by decide) (fun m => ∃ k, k < X.nf ∧ m = funcRec X k) ?_
    (seg_hsend_ffS H (Or.inr rfl)) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h21 : t = 21
  · subst h21
    rw [seg_t21] at hi
    simp only [Func.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    obtain ⟨k, hk, he⟩ := hfunc r hr
    refine ⟨k, hk, ?_⟩
    rw [← he]
    simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row]
  · exact absurd (seg_recv_func nloc ngl t ht h21 i hi hb') (by simp [hs'])

/-- **R16 lookup soundness on the segment AIR.** -/
theorem seg_r16S {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) : ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_r16GXS H (seg_hsend_r16S H) (regG_r16_recvXS H (regAt_seg nloc ngl)) ho hb hs hc

/-- The BYTE table rows of a segment trace answer exactly `byteF`. -/
theorem seg_byte_row_msgsS {r : Nat} (hr : r < tr.height 16) :
    ∀ i ∈ Byte.inters, ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      i.msg.map (·.eval (tr.row pub 16 r)) =
        [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)] := by
  have hb := SegSha.byte_bitsXS H hr
  have hx := bits8_lt (fun i => rowNat tr 16 r i) (fun i hi => hb i (by omega))
  have hy := bits8_lt (fun i => rowNat tr 16 r (8 + i)) (fun i hi => hb (8 + i) (by omega))
  have eX : Byte.X.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = ((bits8 fun i => rowNat tr 16 r i : Nat) : F) := by
    simp only [Byte.X, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
      Expr.eval_c, Expr.eval_col, natRow, v, Byte.xb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    exact cast_bits8 _
  have eY : Byte.Y.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = ((bits8 fun i => rowNat tr 16 r (8 + i) : Nat) : F) := by
    simp only [Byte.Y, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
      Expr.eval_c, Expr.eval_col, natRow, v, Byte.yb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    exact cast_bits8 (fun i => rowNat tr 16 r (8 + i))
  have hop : ∀ (op : Nat → Nat → Nat) (fb : Bool → Bool → Bool),
      (∀ x y i, (op x y).testBit i = fb (x.testBit i) (y.testBit i)) → (∀ a b, a ≤ 1 → b ≤ 1 → op a b ≤ 1) →
      bits8 (fun i => op (rowNat tr 16 r i) (rowNat tr 16 r (8 + i))) =
        op (bits8 fun i => rowNat tr 16 r i) (bits8 fun i => rowNat tr 16 r (8 + i)) := fun op fb h1 h2 =>
    (bits8_op fb op h1 h2 _ _ (fun i hi => hb i (by omega)) (fun i hi => hb (8 + i) (by omega))).symm
  have eAnd : Byte.andE.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) =
      (((bits8 fun i => rowNat tr 16 r i) &&& (bits8 fun i => rowNat tr 16 r (8 + i)) : Nat) : F) := by
    rw [← hop (· &&& ·) (· && ·) (fun x y i => Nat.testBit_and x y i)
      (fun a b ha hb => by rw [and_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.andE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_and_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_and_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_and_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_and_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_and_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_and_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_and_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_and_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr 16 r i &&& rowNat tr 16 r (8 + i))
  have eOr : Byte.orE.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) =
      (((bits8 fun i => rowNat tr 16 r i) ||| (bits8 fun i => rowNat tr 16 r (8 + i)) : Nat) : F) := by
    rw [← hop (· ||| ·) (· || ·) (fun x y i => Nat.testBit_or x y i)
      (fun a b ha hb => by rw [or_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.orE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_or_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_or_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_or_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_or_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_or_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_or_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_or_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_or_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr 16 r i ||| rowNat tr 16 r (8 + i))
  have eXor : Byte.xorE.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) =
      (((bits8 fun i => rowNat tr 16 r i) ^^^ (bits8 fun i => rowNat tr 16 r (8 + i)) : Nat) : F) := by
    rw [← hop (· ^^^ ·) (fun a b => a ^^ b) (fun x y i => Nat.testBit_xor x y i)
      (fun a b ha hb => by rw [xor_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.xorE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_xor_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_xor_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_xor_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_xor_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_xor_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_xor_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_xor_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_xor_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr 16 r i ^^^ rowNat tr 16 r (8 + i))
  intro i hi
  rw [row_eq_natRow]
  simp only [Byte.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · refine ⟨0, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, Expr.eval_ofNat', byteF]; rfl
  · refine ⟨1, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, eAnd, Expr.eval_ofNat', byteF]; rfl
  · refine ⟨2, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, eOr, Expr.eval_ofNat', byteF]; rfl
  · refine ⟨3, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, eXor, Expr.eval_ofNat', byteF]; rfl

/-- **BYTE lookup soundness on the segment AIR** (the full answer `byteF`). -/
theorem seg_byteS {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busByte)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      o.2.2.1 = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)] := by
  refine lookup_soundXS H busByte (by decide) (fun m => ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      m = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)]) ?_
    (SegSha.seg_hsend_byteS H) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h16 : t = 16
  · subst h16
    rw [SegSha.seg_t16] at hi
    exact seg_byte_row_msgsS H hr i hi
  · exact absurd (SegSha.seg_byte_recv_tables nloc ngl t ht h16 i hi hb') (by simp [hs'])

/-- **The base `Looks` facts on the base view of a segment trace**, for any `nloc'`, `ngl'`, publics. -/
theorem seg_looksS (X : Ctx) (hcode : CodeOK X tr) (hfunc : FuncOK X tr) (nloc' ngl' : Nat) (pub' : List F) :
    Looks X nloc' ngl' pub' (segBase tr) :=
  ⟨fun _o ho hb hs hc => seg_fetchS H X hcode (base_occ_seg ho) hb hs hc,
   fun _o ho hb hs hc => seg_r16S H (base_occ_seg ho) hb hs hc,
   fun _o ho hb hs hc => seg_byteS H (base_occ_seg ho) hb hs hc,
   fun _o ho hb hs hc => seg_funcS H X hfunc (base_occ_seg ho) hb hs hc⟩

end

/-- **`RowFacts2` of an active base instruction row (tables 1–14) of a segment trace.** -/
theorem seg_base_rowfactsS (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    {t r : Nat} (h1 : 1 ≤ t) (h14 : t ≤ 14) (hr : r < tr.height t) (ha : rowAct (chipT t) tr pub t r) :
    RowFacts2 X (rowIn (chipT t) tr pub t r) (rowOut (chipT t) tr pub t r)
      (rowCons (chipT t) tr pub t r) (rowProd (chipT t) tr pub t r) := by
  have hg : ¬ baseGone t := by unfold baseGone; omega
  have hnp := chipT_noPub t h1 h14
  have HC := seg_base_holdsCS' H X.pf.locals.size 0 (pubOf X)
  have L := seg_looksS H X hcode hfunc X.pf.locals.size 0 (pubOf X)
  have h := (chipFactsC X HC).rows L (pubOK_of X) t h1 h14 r (by rw [segBase_height hg]; exact hr)
    (by rw [segBase_rowAct hg, rowAct_noPub hnp tr (pubOf X) pub]; exact ha)
  have eI : rowIn (chipT t) (segBase tr) (pubOf X) t r = rowIn (chipT t) tr pub t r := by
    unfold rowIn; rw [segBase_row hg]; exact rowIn_noPub hnp tr (pubOf X) pub t r
  have eO : rowOut (chipT t) (segBase tr) (pubOf X) t r = rowOut (chipT t) tr pub t r := by
    unfold rowOut; rw [segBase_row hg]; exact rowOut_noPub hnp tr (pubOf X) pub t r
  have eC : rowCons (chipT t) (segBase tr) (pubOf X) t r = rowCons (chipT t) tr pub t r := by
    unfold rowCons; rw [segBase_rowMsgs hg, rowMsgs_noPub hnp tr (pubOf X) pub t r]
  have eP : rowProd (chipT t) (segBase tr) (pubOf X) t r = rowProd (chipT t) tr pub t r := by
    unfold rowProd; rw [segBase_rowMsgs hg, rowMsgs_noPub hnp tr (pubOf X) pub t r]
  rwa [eI, eO, eC, eP] at h

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- FETCH lookup soundness with the M2 records. -/
theorem seg_fetchM2S (X : M2Ctx) (hcode : CodeOKM2 X tr) {o : Occ}
    (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busFetch) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRecM2 X j :=
  seg_fetchS H X.toCtx hcode ho hb hs hc

/-- **Time check on the segment AIR.** -/
theorem seg_time_chkS {ts tp hi : F}
    (h1 : (busR16, true, [ts - tp - ((1 : Nat) : F) - ((65536 : Nat) : F) * hi], 1) ∈
      occs (wasmBaseSegAir nloc ngl) tr pub)
    (h2 : (busR16, true, [((4 : Nat) : F) * hi], 1) ∈ occs (wasmBaseSegAir nloc ngl) tr pub) :
    ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((tp.toNat + 1 + n : Nat) : F) = ts := by
  obtain ⟨x, hx, hxl⟩ := seg_r16S H h1 rfl rfl rfl
  obtain ⟨y, hy, hyl⟩ := seg_r16S H h2 rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx hy
  refine ⟨x.toNat + 16384 * y.toNat, by omega, ?_⟩
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat]
  rw [← hx, ← hy]
  have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_mul]
  rw [this]; grind

end

theorem seg_fetch_convS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOKM2 X tr)
    {pcN opN hN feeN : Nat} (hpcP : pcN < P) (hhP : hN < P) (hfP : feeN < P)
    (hop : isConvOp opN = true)
    (ho : (busFetch, true, [((pcN : Nat) : F), ((opN : Nat) : F), ((hN : Nat) : F), ((feeN : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈
        occs (wasmBaseSegAir nloc ngl) tr pub) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = pcN ∧
      (X.pfOf k).code[pc]? = some (.num opN) ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      feeN = fee ∧ hN = (X.ckOf k).heights[pc]?.getD 0 ∧ fee ≤ X.maxFee := by
  have hP' := P_val
  obtain ⟨j, hj, hm⟩ := seg_fetchM2S H X hcode ho rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨a, op, b, c, d, e, f, g, hsh⟩ := X.recShape hj
  have hopl := X.recOp_lt hj
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  obtain ⟨-, e1, -, -⟩ := cast8_inj hm
  have hconv := isConvOp_cases hop
  have hopEq : opN = op := natEq e1 (by omega) (by omega)
  subst hopEq
  have hop2 : isConvOp ((X.M.records[j]?.getD []).getD 1 0) = true := by rw [hsh]; exact hop
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hrec⟩ := X.recG_conv hj hop2
  rw [hsh] at hrec hins
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hrec hins
  rw [hrec] at hm
  obtain ⟨e0, -, e2, e3⟩ := cast8_inj hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hpcEq : pcN = j := natEq e0 hpcP (by omega)
  have hhb := (X.factsOf hk).hBound pc hpc
  have hfl := feeUnits_lt hfee
  refine ⟨k, pc, fee, hk, hpc, by omega, hins, hfee, natEq e3 hfP (by omega), natEq e2 hhP (by omega), ?_⟩
  have := X.recFee_le hj
  rw [hsh] at this
  simp only [List.cons.injEq] at hrec
  simp only [List.getD_cons_succ, List.getD_cons_zero] at this
  omega

/-- **The FETCH pin of an `unreachable` row.** -/
theorem seg_fetch_unreachS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOKM2 X tr)
    {pcN hN feeN : Nat} (hpcP : pcN < P) (hhP : hN < P) (hfP : feeN < P)
    (ho : (busFetch, true, [((pcN : Nat) : F), ((opUnreach : Nat) : F), ((hN : Nat) : F), ((feeN : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈
        occs (wasmBaseSegAir nloc ngl) tr pub) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = pcN ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      feeN = fee ∧ hN = (X.ckOf k).heights[pc]?.getD 0 ∧ fee ≤ X.maxFee := by
  have hP' := P_val
  obtain ⟨j, hj, hm⟩ := seg_fetchM2S H X hcode ho rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨a, op, b, c, d, e, f, g, hsh⟩ := X.recShape hj
  have hopl := X.recOp_lt hj
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  obtain ⟨-, e1, -, -⟩ := cast8_inj hm
  have hopEq : opUnreach = op := natEq e1 (by simp [opUnreach]; omega) (by omega)
  have hop2 : (X.M.records[j]?.getD []).getD 1 0 = opUnreach := by rw [hsh]; exact hopEq.symm
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hrec⟩ := X.recG_unreach hj hop2
  rw [hsh] at hrec
  rw [hrec] at hm
  obtain ⟨e0, -, e2, e3⟩ := cast8_inj hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound pc hpc
  have hfl := feeUnits_lt hfee
  refine ⟨k, pc, fee, hk, hpc, by have := natEq e0 hpcP (by omega); omega, hins, hfee,
    natEq e3 hfP (by omega), natEq e2 hhP (by omega), ?_⟩
  have := X.recFee_le hj
  rw [hsh] at this
  simp only [List.cons.injEq] at hrec
  simp only [List.getD_cons_succ, List.getD_cons_zero] at this
  omega

/-- **An active CONV row of a `HoldsX (wasmBaseSegAir …)` trace.**  Its FETCH answer pins a checked
function `k` and local pc whose instruction is the conversion `.num (convOpN tr r)`, with the row's
fee and height the pc's (all from `checkModuleM2`); its CH effect is `convVal` of the consumed value
(`conv_row_spec`, with the R16 bound of `2·rl` from the lookup); and the six non-spec `RowFacts2`
fields hold. -/
theorem conv_row_segS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 28) (hact : (Conv.act.eval (tr.row pub 28 r)).toNat = 1) :
    (∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = cn tr 28 r cPc ∧
      (X.pfOf k).code[pc]? = some (.num (convOpN tr r)) ∧ isConvOp (convOpN tr r) = true ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧ fee ≤ X.maxFee ∧ cn tr 28 r cFee = fee ∧
      cn tr 28 r cH = (X.ckOf k).heights[pc]?.getD 0) ∧
    (∀ {i tp : Nat} {x : Val}, isNum x →
      decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r),
        ((cn tr 28 r Conv.fWrap : Nat) : F), ((cn tr 28 r Conv.a : Nat) : F),
        ((cn tr 28 r (Conv.a + 1) : Nat) : F), ((cn tr 28 r (Conv.a + 2) : Nat) : F),
        ((cn tr 28 r (Conv.a + 3) : Nat) : F), ((cn tr 28 r Conv.ta : Nat) : F)] = enc 0 i x tp →
      rowCons Conv.table tr pub 28 r = [enc 0 i x tp] ∧
      rowProd Conv.table tr pub 28 r = [enc 0 i (convVal (convOpN tr r) x) (cn tr 28 r cTs)]) ∧
    (rowIn Conv.table tr pub 28 r).getD 3 0 = 0 ∧
    lvl (rowOut Conv.table tr pub 28 r) = lvl (rowIn Conv.table tr pub 28 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧
      gasF (rowOut Conv.table tr pub 28 r) = gasF (rowIn Conv.table tr pub 28 r) + (fee : F)) ∧
    (∀ x ∈ rowCons Conv.table tr pub 28 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn Conv.table tr pub 28 r)) ∧
    (∀ x ∈ rowProd Conv.table tr pub 28 r, x.tp < P ∧
      ((x.tp : Nat) : F) = lvl (rowIn Conv.table tr pub 28 r)) ∧
    (rowProd Conv.table tr pub 28 r).Nodup := by
  have hP' := P_val
  have ht : 28 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hT := seg_t28 nloc ngl
  have hc := table_constr_eqXS H ht Conv.table hT hr
  have hPr := rowNat_lt tr 28 r
  obtain ⟨hfl, -, -, -⟩ := conv_row_facts hc hact
  have hop : isConvOp (convOpN tr r) = true := by
    simp only [convOpN, isConvOp, Bool.or_eq_true, beq_iff_eq]
    rcases hfl with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rw [a, b, c] <;> simp
  have hopP : convOpN tr r < P := by
    have := isConvOp_cases hop; omega
  -- interactions of the row, as occurrences
  have occ : ∀ i ∈ Conv.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 28 r)),
      (i.count.eval (tr.row pub 28 r)).toNat) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
    intro i hi
    refine row_occ ht hr ?_
    rw [hT]; exact hi
  -- the FETCH pin
  have hfo := occ (fetch (v cPc) Conv.op (v cH) (v cFee) zeros4 Conv.act) (by simp [Conv.inters, stdState])
  have hopE : Conv.op.eval (tr.row pub 28 r) = ((convOpN tr r : Nat) : F) := by
    simp only [Conv.op, convOpN, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval,
      Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  simp only [fetch, zeros4, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hact, hopE,
    Expr.eval_ofNat', conv_col_eval] at hfo
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfeq, hheq, hfle⟩ :=
    seg_fetch_convS X H hcode (hPr _) (hPr _) (hPr _) hop hfo
  refine ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hop, hfee, hfle, hfeq, hheq⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the CH effect
    intro i tp x hx hin
    refine conv_row_spec hc hact (fun h1 => ?_) hx hin
    have hro := occ (r16 (2 * v Conv.rl) (v Conv.fExtS)) (by simp [Conv.inters])
    simp only [r16, List.map_cons, List.map_nil, Expr.eval_mul', Expr.eval_ofNat', conv_col_eval] at hro
    have hcnt : (((cn tr 28 r Conv.fExtS : Nat) : F)).toNat = 1 := by
      rw [Fp.toNat_cast_of_lt (hPr _)]; exact h1
    rw [hcnt] at hro
    obtain ⟨y, hy, hyl⟩ := seg_r16S H hro rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hy
    rw [← Lean.Grind.Semiring.natCast_mul] at hy
    rw [← hy, Fp.toNat_cast] at hyl
    exact hyl
  · rw [conv_rowIn]; rfl
  · rw [conv_rowIn, conv_rowOut]; simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, one_cast]
  · refine ⟨fee, hfle, ?_⟩
    rw [conv_rowIn, conv_rowOut]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero]
    rw [cell_cast tr 28 r 4]
    have : rowNat tr 28 r 4 = fee := hfeq
    rw [this]
  · -- consT from the time check
    intro x hx
    rw [conv_row_cons hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    have h1 := occ ((timeChk (v cTs) (v Conv.ta) (v Conv.ha) Conv.act)[0]'(by simp [timeChk]))
      (by simp [Conv.inters, timeChk])
    have h2 := occ ((timeChk (v cTs) (v Conv.ta) (v Conv.ha) Conv.act)[1]'(by simp [timeChk]))
      (by simp [Conv.inters, timeChk])
    simp only [timeChk, r16, B16, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval, hact] at h1 h2
    obtain ⟨n, hn, he⟩ := seg_time_chkS H h1 h2
    refine ⟨n, hn, ?_⟩
    rw [conv_rowIn]
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero, lvl]
    rw [Fp.toNat_cast_of_lt (hPr _)] at he ⊢
    rw [he, cell_cast tr 28 r 1]; rfl
  · intro x hx
    rw [conv_row_prod hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero]
    rw [Fp.toNat_cast_of_lt (hPr _), conv_rowIn]
    refine ⟨hPr _, ?_⟩
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rw [cell_cast tr 28 r 1]; rfl
  · rw [conv_row_prod hact]; simp

/-- **An active UNREACH row of a `HoldsX (wasmBaseSegAir …)` trace.**  Its FETCH answer pins a checked
function `k` and local pc whose instruction is `unreachable` (with the row's fee and height the pc's);
it consumes and produces nothing; its STATE output carries `halted = 2`; and the `RowFacts2` fields
`halt0`, `tsOut`, `gasOut` hold (`consT`, `prodT`, `prodNd` are trivial: no CH traffic). -/
theorem unreach_row_segS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 29) (hact : ((v Unreach.act).eval (tr.row pub 29 r)).toNat = 1) :
    (∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = cn tr 29 r cPc ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧ fee ≤ X.maxFee ∧ cn tr 29 r cFee = fee ∧
      cn tr 29 r cH = (X.ckOf k).heights[pc]?.getD 0) ∧
    rowCons Unreach.table tr pub 29 r = [] ∧ rowProd Unreach.table tr pub 29 r = [] ∧
    (rowOut Unreach.table tr pub 29 r).getD 3 0 = ((2 : Nat) : F) ∧
    (rowIn Unreach.table tr pub 29 r).getD 3 0 = 0 ∧
    lvl (rowOut Unreach.table tr pub 29 r) = lvl (rowIn Unreach.table tr pub 29 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧
      gasF (rowOut Unreach.table tr pub 29 r) = gasF (rowIn Unreach.table tr pub 29 r) + (fee : F)) := by
  have ht : 29 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hT := seg_t29 nloc ngl
  have hPr := rowNat_lt tr 29 r
  have hfo := row_occ (pub := pub) ht hr
    (i := fetch (v cPc) (Expr.c opUnreach) (v cH) (v cFee) zeros4 (v Unreach.act))
    (by rw [hT]; simp [Unreach.table, Unreach.inters])
  have hact' : (((cn tr 29 r Unreach.act : Nat) : F)).toNat = 1 := by rw [← conv_col_eval]; exact hact
  simp only [fetch, zeros4, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Expr.eval_ofNat', Expr.eval_c, conv_col_eval, hact'] at hfo
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfeq, hheq, hfle⟩ :=
    seg_fetch_unreachS X H hcode (hPr _) (hPr _) (hPr _) hfo
  obtain ⟨hcons, hprod, hout⟩ := unreach_row hact
  refine ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfle, hfeq, hheq⟩, hcons, hprod, ?_, ?_, ?_, ?_⟩
  · rw [hout]; rfl
  · rw [unreach_rowIn]; rfl
  · rw [unreach_rowIn, hout]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, one_cast, cell_cast]; rfl
  · refine ⟨fee, hfle, ?_⟩
    rw [unreach_rowIn, hout]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, cell_cast]
    have e : cn tr 29 r cFee = fee := hfeq
    rw [e]; rfl

/-- **`RowFacts2` of an active CONV row** of a `HoldsX (wasmBaseSegAir …)` trace, for the M2
context. -/
theorem conv_rowfacts_segS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 28) (hact : (Conv.act.eval (tr.row pub 28 r)).toNat = 1) :
    RowFacts2 X.toCtx (rowIn Conv.table tr pub 28 r) (rowOut Conv.table tr pub 28 r)
      (rowCons Conv.table tr pub 28 r) (rowProd Conv.table tr pub 28 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 28 r
  obtain ⟨⟨k0, pc0, fee, hk0, hpc0, hoff0, hins0, hop, hfee0, hfle, hfeq, hheq⟩, hspec, h0, hts, hgas, hct,
    hpt, hnd⟩ := conv_row_segS X H hcode hr hact
  refine ⟨?_, h0, hts, hgas, hct, hpt, hnd⟩
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [conv_rowIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.toCtx.off_bound R.kLt
  have htot := X.toCtx.mf.total
  simp only [toCtx_offOf, toCtx_pfOf, toCtx_M] at hoffb hpcl
  have p0 : rowNat tr 28 r 0 = X.offOf E.k + pc := natEq (by rw [cell_cast] at i0; exact i0) (hcP _) (by
    simp only [toCtx_M] at htot; omega)
  have p1 : rowNat tr 28 r 1 = t := natEq (by rw [cell_cast] at i1; exact i1) (hcP _) (by omega)
  have psb : rowNat tr 28 r Conv.kSb = E.sb :=
    natEq (by rw [cell_cast] at i4; exact i4) (hcP _) (by have := R.sbLt; omega)
  have hsbR := R.sbLe
  obtain ⟨hk, hl⟩ := X.loc_unique hk0 hpc0 R.kLt hpcl (by rw [hoff0]; exact p0)
  subst k0
  subst pc0
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hH := R.height
  simp only [toCtx_ckOf] at hL0 hH
  obtain ⟨h1, hnext, hL1, hH1⟩ := X.conv_succ R.kLt hins0 hop hL0 hH
  have p3 : rowNat tr 28 r cH = s.stack.size - E.sb := by
    show cn tr 28 r cH = _; rw [hheq, hH]; rfl
  have hHb := (X.factsOf R.kLt).hBound pc hpcl
  rw [hH] at hHb; simp only [Option.getD_some] at hHb
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  -- the consumed message is the stack top
  have hcons := conv_row_cons (pub := pub) hact
  obtain ⟨mc, hmc_def⟩ : ∃ mc, mc = decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r),
        ((cn tr 28 r Conv.fWrap : Nat) : F), ((cn tr 28 r Conv.a : Nat) : F),
        ((cn tr 28 r (Conv.a + 1) : Nat) : F), ((cn tr 28 r (Conv.a + 2) : Nat) : F),
        ((cn tr 28 r (Conv.a + 3) : Nat) : F), ((cn tr 28 r Conv.ta : Nat) : F)] := ⟨_, rfl⟩
  rw [← hmc_def] at hcons
  have hmc : live mc := hlive mc (by rw [hcons]; simp)
  have hsl : (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r) =
      ((rowNat tr 28 r Conv.kSb : Nat) : F) + ((rowNat tr 28 r cH : Nat) : F) - ((1 : Nat) : F) := by
    simp only [v, Expr.eval_add', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast]
  have ms : mc.space = 0 := by
    simp only [hmc_def, decMsg, List.getD_cons_zero]; rw [Fp.toNat_cast_of_lt (by omega)]
  have msl : mc.slot = s.stack.size - 1 := by
    simp only [hmc_def, decMsg, List.getD_cons_succ, List.getD_cons_zero]
    rw [hsl, slot_toNat psb p3 hsbR (by omega) hszP]
  obtain ⟨ea, -, -, vt⟩ := R.stack_dec hmc ms msl (by omega)
  have hnum := R.numS (s.stack.size - 1) (by omega)
  obtain ⟨-, hprod⟩ := hspec hnum (by rw [← hmc_def]; exact ea)
  have hins' : (X.toCtx.pfOf E.k).code[pc]? = some (.num (convOpN tr r)) := hins0
  have hfee' : feeUnits X.toCtx.cfg (X.toCtx.pfOf E.k).gas[pc]? = some fee := hfee0
  have hout : rowOut Conv.table tr pub 28 r =
      stMsg (X.toCtx.offOf E.k + (pc + 1)) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [conv_rowOut]
    rw [cell_cast] at i0 i1 i2 i4 i5
    rw [cell_cast tr 28 r 0, cell_cast tr 28 r 1, cell_cast tr 28 r 2, cell_cast tr 28 r 4,
      cell_cast tr 28 r Conv.kSb, cell_cast tr 28 r Conv.kCid, i0, i1, i2, i4, i5,
      show rowNat tr 28 r 4 = fee from hfeq]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add, toCtx_offOf, one_cast, List.cons.injEq, and_true]
    grind
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfle, by omega, hout, fun hg => ⟨fun _ => ?_,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩
  obtain ⟨s', hst, hrel⟩ := step_conv X.toCtx R hins' hop hfee' hg hg64 (by omega) hnext
    ⟨ls0, hL1, hfl0⟩ hH1 mc (enc 0 (s.stack.size - 1) (convVal (convOpN tr r) mc.toVal) t) hmc
    ⟨ms, msl⟩ rfl
  refine ⟨s', hst, ?_⟩
  rw [vt] at hrel
  rw [hcons, hprod, show cn tr 28 r cTs = t from p1]
  exact hrel

/-- **`RowFacts2` of an active UNREACH row**: the spec step aborts (`halted = 2`). -/
theorem unreach_rowfacts_segS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 29) (hact : ((v Unreach.act).eval (tr.row pub 29 r)).toNat = 1) :
    RowFacts2 X.toCtx (rowIn Unreach.table tr pub 29 r) (rowOut Unreach.table tr pub 29 r)
      (rowCons Unreach.table tr pub 29 r) (rowProd Unreach.table tr pub 29 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 29 r
  obtain ⟨⟨k0, pc0, fee, hk0, hpc0, hoff0, hins0, hfee0, hfle, hfeq, -⟩, hc, hp, hh2, h0, hts, hgas⟩ :=
    unreach_row_segS X H hcode hr hact
  refine ⟨?_, h0, hts, hgas, by rw [hc]; simp, by rw [hp]; simp, by rw [hp]; simp⟩
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [unreach_rowIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.toCtx.off_bound R.kLt
  have htot := X.toCtx.mf.total
  simp only [toCtx_offOf, toCtx_pfOf, toCtx_M] at hoffb hpcl
  have p0 : rowNat tr 29 r 0 = X.offOf E.k + pc := natEq (by rw [cell_cast] at i0; exact i0) (hcP _) (by
    simp only [toCtx_M] at htot; omega)
  obtain ⟨hk, hl⟩ := X.loc_unique hk0 hpc0 R.kLt hpcl (by rw [hoff0]; exact p0)
  subst k0
  subst pc0
  have hins' : (X.toCtx.pfOf E.k).code[pc]? = some .unreachable := hins0
  have hfee' : feeUnits X.toCtx.cfg (X.toCtx.pfOf E.k).gas[pc]? = some fee := hfee0
  obtain ⟨-, -, hout0⟩ := unreach_row (pub := pub) (t := 29) (r := r) hact
  have hout : rowOut Unreach.table tr pub 29 r =
      stMsg (X.toCtx.offOf E.k + (pc + 1)) (t + 1) (S + fee) 2 E.sb E.cid := by
    rw [hout0]
    rw [cell_cast] at i0 i1 i2 i4 i5
    simp only [cn, cPc, cTs, cS, cFee] at hfeq ⊢
    rw [i0, i1, i2, i4, i5, hfeq]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add, toCtx_offOf, one_cast, List.cons.injEq, and_true]
    grind
  refine ⟨E.k, pc + 1, fee, 2, E.sb, E.cid, hfle, by omega, hout, fun hg =>
    ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩⟩
  refine ⟨{ s with gas := { s.gas with g := s.gas.g - X.toCtx.R * fee } }, trapStr "Unreachable", ?_,
    R.step_gas hg rfl⟩
  rw [step_eq_exec X.toCtx R hins' hfee' hg hg64]
  simp [exec]

/-- **`RowFacts` of an active IF row** of a `HoldsX (wasmBaseSegAir …)` trace, for the M2 context. -/
theorem if_rowfacts_segS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hcode : CodeOK X.toCtx tr)
    {r : Nat} (hr : r < tr.height 26) (hact : rowAct IfC.table tr pub 26 r) :
    RowFacts X.toCtx (rowIn IfC.table tr pub 26 r) (rowOut IfC.table tr pub 26 r)
      (rowCons IfC.table tr pub 26 r) (rowProd IfC.table tr pub 26 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 26 r
  have ht : 26 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hT := seg_t26 nloc ngl
  have hcon : ∀ e ∈ IfC.constraints, e.eval (natRow (rowNat tr 26 r) (tr.row pub 26 r)) = 0 :=
    table_constr_eqXS H ht IfC.table hT hr
  have hact' : (((rowNat tr 26 r IfC.fIf : Nat) : F)).toNat = 1 := by
    rw [Fp.toNat_cast_of_lt (hcP _)]; exact hact
  have occ : ∀ i ∈ IfC.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 26 r)),
      (i.count.eval (tr.row pub 26 r)).toNat) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
    intro i hi
    refine row_occ ht hr ?_
    rw [hT]; exact hi
  -- the FETCH pin
  have hfo := occ (fetch (v cPc) (Expr.c IfC.opIf) (v cH) (v cFee) [v IfC.tgt, 0, 0, 0] IfC.act)
    (by simp [IfC.inters])
  simp only [fetch, List.cons_append, List.nil_append, List.map_cons, List.map_nil, IfC.act,
    Expr.eval_ofNat', Expr.eval_c, conv_col_eval, hact'] at hfo
  obtain ⟨j, hj, hm⟩ := seg_fetchM2S H X hcode hfo rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  have hopl := X.recOp_lt hj
  rw [hrj, Option.getD_some, Array.getElem?_eq_getElem hsz, Option.getD_some] at hm hopl
  obtain ⟨a, op, b, c, d, e5, f, g, hsh⟩ := recordAtM2_shape hrec
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  have hm2 := hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm2
  obtain ⟨-, e1, -, -, -, -, -, -⟩ := hm2
  have hopEq : op = IfC.opIf := (natEq e1 (by simp [IfC.opIf]; omega) (by omega)).symm
  obtain ⟨bt, e, el, fee, hins, hend, hels, hfee, hrr⟩ :=
    recordAtM2_if_op (hrec.trans (congrArg some hsh)) (by rw [hopEq]; rfl)
  rw [hrr] at hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
  obtain ⟨m0, -, m3, m4, m6⟩ := hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound l hl
  have hfl := feeUnits_lt hfee
  have hoffb := X.off_bound hk
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have p0 : rowNat tr 26 r cPc = X.offOf k + l := natEq m0 (hcP _) (by omega)
  have p3 : rowNat tr 26 r cH = (X.ckOf k).heights[l]?.getD 0 := natEq m3 (hcP _) (by omega)
  have p4 : rowNat tr 26 r cFee = fee := natEq m4 (hcP _) (by omega)
  have helt : el + 1 < (X.pfOf k).code.size := by
    obtain ⟨ls, h, hls, hh⟩ := (X.factsOf hk).lh hl
    obtain ⟨lsT, hT', ftgt, lsF, hF, hs, -, -, -, h5, -, -⟩ := X.if_succ hk hins hls hh
    have := ifStepM2_spec hend hels hs
    rw [← this.2.2.2.1]; exact h5
  have p6 : rowNat tr 26 r IfC.tgt = el + 1 + X.offOf k := natEq m6 (hcP _) (by omega)
  have hfeeMax : fee ≤ X.toCtx.maxFee := by
    have := X.recFee_le hj
    rw [hrj, Option.getD_some, Array.getElem?_eq_getElem hsz, Option.getD_some, hsh, hrr] at this
    simpa using this
  -- the checker data
  have hd : IfRowData 26 X.toCtx tr r fee :=
    { k := k, pc := l, bt := bt, e := e, el := el, kLt := hk, pcLt := hl, gpc := p0.symm,
      ins := hins, endE := hend, elseE := hels, feeEq := hfee, tgt := p6, hEq := p3,
      hLt := by rw [p3]; exact hhb,
      succ := by
        intro ls h hls hh
        obtain ⟨lsT, hT', ftgt, lsF, hF, hs, h1, h2, h3, h4, h5, h6⟩ := X.if_succ hk hins hls hh
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := ifStepM2_spec hend hels hs
        subst q2 q3 q4 q5 q6
        exact ⟨h - 1, q1, rfl, h1, h2, h3, h4, h5, h6⟩ }
  -- the condition's producer time
  have hconsT : ∀ x ∈ rowCons IfC.table tr pub 26 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn IfC.table tr pub 26 r) := by
    intro x hx
    rw [if_rowCons hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    have h1 := occ ((timeChk (v cTs) (v IfC.tc) (v IfC.hc) IfC.act)[0]'(by simp [timeChk]))
      (by simp [IfC.inters, timeChk])
    have h2 := occ ((timeChk (v cTs) (v IfC.tc) (v IfC.hc) IfC.act)[1]'(by simp [timeChk]))
      (by simp [IfC.inters, timeChk])
    simp only [timeChk, r16, B16, IfC.act, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval, hact'] at h1 h2
    obtain ⟨n, hn, he⟩ := seg_time_chkS H h1 h2
    refine ⟨n, hn, ?_⟩
    rw [if_rowIn]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rw [Fp.toNat_cast_of_lt (hcP _)] at he
    rw [he, cell_cast tr 26 r 1]; rfl
  exact if_rowfacts hcon hact hfeeMax p4 hd hconsT

/-- **The per-row dispatch of `wasmBaseSegAir`** (the segment analogue of `m2_rowfacts`): every active
instruction row (tables 1–14, IF 26, CONV 28, UNREACH 29) of a `HoldsX (wasmBaseSegAir …)` trace has
`RowFacts2` for the M2 context.  Premises: the CODE/FUNC commitment bindings only. -/
theorem seg_rowfactsS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) (ha : rowAct (chipM2 t) tr pub t r) :
    RowFacts2 X.toCtx (rowIn (chipM2 t) tr pub t r) (rowOut (chipM2 t) tr pub t r)
      (rowCons (chipM2 t) tr pub t r) (rowProd (chipM2 t) tr pub t r) := by
  rcases htI with ⟨h1, h14⟩ | rfl | rfl | rfl
  · have hne : chipM2 t = chipT t := by
      simp only [chipM2]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hne] at ha ⊢
    exact seg_base_rowfactsS X.toCtx H hcode hfunc h1 h14 hr ha
  · exact (if_rowfacts_segS X H hcode hr ha).two
  · exact conv_rowfacts_segS X H hcode hr
      (by simpa [rowAct, chipM2, Conv.table, Conv.inters, stdState, stateIn] using ha)
  · exact unreach_rowfacts_segS X H hcode hr
      (by simpa [rowAct, chipM2, Unreach.table, Unreach.inters, stateIn] using ha)

end WasmBase
