import WasmBase.Main.Rows
import WasmBase.StepOps
import WasmBase.StepOps2
import WasmBase.Local.Bit
/-!
# Row lemma: BIT (`i32/i64.and`, `or`, `xor`)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- Flags of a BIT row: bits, mutually exclusive.  (Constraint-only form; `bit_flags` is the wrapper.) -/
theorem bit_flags_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Bit.table.constraints, e.eval (natRow (rowNat tr 2 r) (tr.row pub 2 r)) = 0) :
    (rowNat tr 2 r 5 = 0 ∨ rowNat tr 2 r 5 = 1) ∧ (rowNat tr 2 r 6 = 0 ∨ rowNat tr 2 r 6 = 1) ∧
      (rowNat tr 2 r 7 = 0 ∨ rowNat tr 2 r 7 = 1) ∧ (rowNat tr 2 r 8 = 0 ∨ rowNat tr 2 r 8 = 1) ∧
      rowNat tr 2 r 5 + rowNat tr 2 r 6 + rowNat tr 2 r 7 ≤ 1 := by
  simp only [Bit.table, Bit.constraints, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil,
    and_true] at hcon
  obtain ⟨⟨bA, bO, bX, b64, hAO, hAX, hOX, -⟩, -⟩ := hcon
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Bit.fAnd, Bit.fOr, Bit.fXor, Bit.is64] at bA bO bX b64 hAO hAX hOX
  have h5 := bool_nat (rowNat_lt _ _ _ _) bA
  have h6 := bool_nat (rowNat_lt _ _ _ _) bO
  have h7 := bool_nat (rowNat_lt _ _ _ _) bX
  have := zero_of_mul_nat (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _) hAO
  have := zero_of_mul_nat (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _) hAX
  have := zero_of_mul_nat (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _) hOX
  exact ⟨h5, h6, h7, bool_nat (rowNat_lt _ _ _ _) b64, by omega⟩

theorem bit_flags {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 2) :
    (rowNat tr 2 r 5 = 0 ∨ rowNat tr 2 r 5 = 1) ∧ (rowNat tr 2 r 6 = 0 ∨ rowNat tr 2 r 6 = 1) ∧
      (rowNat tr 2 r 7 = 0 ∨ rowNat tr 2 r 7 = 1) ∧ (rowNat tr 2 r 8 = 0 ∨ rowNat tr 2 r 8 = 1) ∧
      rowNat tr 2 r 5 + rowNat tr 2 r 6 + rowNat tr 2 r 7 ≤ 1 :=
  bit_flags_of (table_constr H (by simp [air_len]) hr)

theorem bit_count_eq {i : Inter} (hi : i ∈ Bit.inters) : i.count = Bit.act :=
  of_decide_eq_true (List.all_eq_true.mp
    (show Bit.inters.all (fun i => decide (i.count = Bit.act)) = true by decide) i hi)

theorem bit_act_eval (tr : Trace) (pub : List F) (r : Nat) :
    (Bit.act.eval (tr.row pub 2 r)).toNat = (rowNat tr 2 r 5 + rowNat tr 2 r 6 + rowNat tr 2 r 7) % P := by
  simp only [Bit.act, v, Expr.eval_add', Expr.eval_col, Trace.row, Bit.fAnd, Bit.fOr, Bit.fXor]
  rw [cell_cast, cell_cast, cell_cast, ← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add,
    Fp.toNat_cast]

theorem bit_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Bit.table.constraints, e.eval (natRow (rowNat tr 2 r) (tr.row pub 2 r)) = 0) :
    ∀ i ∈ Bit.inters, (i.count.eval (tr.row pub 2 r)).toNat ≤ 1 := by
  have hP' := P_val
  obtain ⟨-, -, -, -, hs⟩ := bit_flags_of hcon
  intro i hi
  rw [bit_count_eq hi, bit_act_eval, Nat.mod_eq_of_lt (by omega)]; exact hs

theorem bit_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 2) :
    ∀ i ∈ Bit.inters, (i.count.eval (tr.row pub 2 r)).toNat ≤ 1 :=
  bit_counts_of (table_constr H (by simp [air_len]) hr)

theorem bit_inactive {pub : List F} {tr : Trace} {r : Nat}
    (hna : ¬ rowAct Bit.table tr pub 2 r) :
    ∀ i ∈ Bit.inters, (i.count.eval (tr.row pub 2 r)).toNat ≠ 1 := by
  intro i hi
  rw [bit_count_eq hi]
  simpa [rowAct, Bit.table, Bit.inters, stdState, stateIn] using hna

theorem bit_rnToNat (tr : Trace) (t r i : Nat) : (((rowNat tr t r i : Nat) : F)).toNat = rowNat tr t r i :=
  Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)

theorem bit_zeroToNat : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by rw [P_val]; omega)

theorem bit_limbToNat {a b : Nat} (ha : a < 256) (hb : b < 256) :
    (((a : Nat) : F) + ((256 : Nat) : F) * ((b : Nat) : F)).toNat = a + 256 * b := by
  rw [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt]
  rw [P_val]; omega

theorem bit_byteF_lt {K x y : Nat} (hx : x < 256) (hy : y < 256) : byteF K x y < 256 := by
  have h8 : (256 : Nat) = 2 ^ 8 := rfl
  unfold byteF
  split
  · exact h8 ▸ and_byte (h8 ▸ hx)
  · split
    · exact h8 ▸ or_byte (h8 ▸ hx) (h8 ▸ hy)
    · split
      · exact h8 ▸ xor_byte (h8 ▸ hx) (h8 ▸ hy)
      · omega

theorem bit_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 2) (hact : rowAct Bit.table tr pub 2 r) :
    RowFacts X (rowIn Bit.table tr pub 2 r) (rowOut Bit.table tr pub 2 r)
      (rowCons Bit.table tr pub 2 r) (rowProd Bit.table tr pub 2 r) := by
  have hP' := P_val
  have ht : 2 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 2 r i < P := rowNat_lt tr 2 r
  have hcon : ∀ e ∈ Bit.constraints, e.eval (natRow (rowNat tr 2 r) (tr.row pub 2 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨f5, f6, f7, f8, f567⟩ := bit_flags H hr
  have cnt : (Bit.act.eval (tr.row pub 2 r)).toNat = 1 := by
    simpa only [rowAct, Bit.table, Bit.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero] using hact
  have a567 : rowNat tr 2 r 5 + rowNat tr 2 r 6 + rowNat tr 2 r 7 = 1 := by
    rw [bit_act_eval, Nat.mod_eq_of_lt (by omega)] at cnt; exact cnt
  have hocc : ∀ i ∈ Bit.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 2 r)),
      (i.count.eval (tr.row pub 2 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Bit.table.inters from hi)
  -- the BYTE lookups
  have hbyte : ∀ k, k < 8 → rowNat tr 2 r (9 + k) < 256 ∧ rowNat tr 2 r (19 + k) < 256 ∧
      rowNat tr 2 r (29 + k) = byteF (rowNat tr 2 r 5 + 2 * rowNat tr 2 r 6 + 3 * rowNat tr 2 r 7)
        (rowNat tr 2 r (9 + k)) (rowNat tr 2 r (19 + k)) := by
    intro k hk
    have h := hocc _ (show byteQ Bit.kind (v (Bit.ab + k)) (v (Bit.bb + k)) (v (Bit.rb + k)) Bit.act ∈ Bit.inters by
      unfold Bit.inters; exact List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    simp only [byteQ, cnt] at h
    simp only [List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat',
      cell_cast, Trace.row, Bit.kSb, Bit.kCid, Bit.kind, Bit.ab, Bit.bb, Bit.rb, Bit.fAnd, Bit.fOr, Bit.fXor] at h
    obtain ⟨K, x, y, hK, hx, hy, hm⟩ := L.byte _ h rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hm
    obtain ⟨eK, ex, ey, ez⟩ := hm
    have ex' := natEq ex (hcP _) (by omega)
    have ey' := natEq ey (hcP _) (by omega)
    have ez' := natEq ez (hcP _) (by have := bit_byteF_lt (K := K) hx hy; omega)
    simp only [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_mul] at eK
    have eK' := natEq eK (by omega) (by omega)
    rw [ez', ex', ey', eK']
    exact ⟨hx, hy, rfl⟩
  have ab : ∀ k, k < 8 → rowNat tr 2 r (9 + k) < 256 := fun k hk => (hbyte k hk).1
  have bb : ∀ k, k < 8 → rowNat tr 2 r (19 + k) < 256 := fun k hk => (hbyte k hk).2.1
  have rb : ∀ k, k < 8 → rowNat tr 2 r (29 + k) < 256 := fun k hk => by
    rw [(hbyte k hk).2.2]; exact bit_byteF_lt (ab k hk) (bb k hk)
  have a0 := ab 0 (by omega); have a1 := ab 1 (by omega); have a2 := ab 2 (by omega); have a3 := ab 3 (by omega)
  have a4 := ab 4 (by omega); have a5 := ab 5 (by omega); have a6 := ab 6 (by omega); have a7 := ab 7 (by omega)
  have b0 := bb 0 (by omega); have b1 := bb 1 (by omega); have b2 := bb 2 (by omega); have b3 := bb 3 (by omega)
  have b4 := bb 4 (by omega); have b5 := bb 5 (by omega); have b6 := bb 6 (by omega); have b7 := bb 7 (by omega)
  have r0 := rb 0 (by omega); have r1 := rb 1 (by omega); have r2 := rb 2 (by omega); have r3 := rb 3 (by omega)
  have r4 := rb 4 (by omega); have r5 := rb 5 (by omega); have r6 := rb 6 (by omega); have r7 := rb 7 (by omega)
  simp only [Nat.reduceAdd] at a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1 r2 r3 r4 r5 r6 r7
  -- messages
  have hIn : rowIn Bit.table tr pub 2 r =
      [((rowNat tr 2 r 0 : Nat) : F), ((rowNat tr 2 r 1 : Nat) : F), ((rowNat tr 2 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 2 r 37 : Nat) : F), ((rowNat tr 2 r 38 : Nat) : F)] := by
    simp only [rowIn, Bit.table, Bit.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Bit.kSb, Bit.kCid, cPc, cTs, cS]
  have hOut : rowOut Bit.table tr pub 2 r =
      [((rowNat tr 2 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 2 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 2 r 2 : Nat) : F) + ((rowNat tr 2 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 2 r 37 : Nat) : F), ((rowNat tr 2 r 38 : Nat) : F)] := by
    simp only [rowOut, Bit.table, Bit.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Bit.kSb, Bit.kCid, cPc, cTs, cS, cFee]
  have hCons : rowCons Bit.table tr pub 2 r =
      [⟨0, (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 2 r 8,
          rowNat tr 2 r 9 + 256 * rowNat tr 2 r 10, rowNat tr 2 r 11 + 256 * rowNat tr 2 r 12,
          rowNat tr 2 r 13 + 256 * rowNat tr 2 r 14, rowNat tr 2 r 15 + 256 * rowNat tr 2 r 16, rowNat tr 2 r 17⟩,
        ⟨0, (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 2 r 8,
          rowNat tr 2 r 19 + 256 * rowNat tr 2 r 20, rowNat tr 2 r 21 + 256 * rowNat tr 2 r 22,
          rowNat tr 2 r 23 + 256 * rowNat tr 2 r 24, rowNat tr 2 r 25 + 256 * rowNat tr 2 r 26, rowNat tr 2 r 27⟩] := by
    rw [rowCons, rowMsgs_eq, show Bit.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
      [stkRecv (v Bit.kSb + v cH - 2) (v Bit.is64) (limbsB Bit.ab) (v Bit.ta) Bit.act,
       stkRecv (v Bit.kSb + v cH - 1) (v Bit.is64) (limbsB Bit.bb) (v Bit.tb) Bit.act] by decide]
    simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, cnt, ite_true]
    simp only [List.map_cons, List.map_nil, limbsB, limbB, List.range, List.range.loop, List.cons_append,
      List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      cell_cast, Trace.row, Bit.kSb, Bit.kCid, cH, Bit.is64, Bit.ab, Bit.ta, Bit.bb, Bit.tb, Nat.reduceAdd, Nat.reduceMul, decMsg,
      List.getD_cons_zero, List.getD_cons_succ, bit_rnToNat, bit_zeroToNat,
      bit_limbToNat a0 a1, bit_limbToNat a2 a3, bit_limbToNat a4 a5, bit_limbToNat a6 a7,
      bit_limbToNat b0 b1, bit_limbToNat b2 b3, bit_limbToNat b4 b5, bit_limbToNat b6 b7]
  have hProd : rowProd Bit.table tr pub 2 r =
      [⟨0, (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 2 r 8,
          rowNat tr 2 r 29 + 256 * rowNat tr 2 r 30, rowNat tr 2 r 31 + 256 * rowNat tr 2 r 32,
          rowNat tr 2 r 33 + 256 * rowNat tr 2 r 34, rowNat tr 2 r 35 + 256 * rowNat tr 2 r 36, rowNat tr 2 r 1⟩] := by
    rw [rowProd, rowMsgs_eq, show Bit.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
      [stkSend (v Bit.kSb + v cH - 2) (v Bit.is64) (limbsB Bit.rb) (v cTs) Bit.act] by decide]
    simp only [List.filterMap_cons, List.filterMap_nil, stkSend, chSend, cnt, ite_true]
    simp only [List.map_cons, List.map_nil, limbsB, limbB, List.range, List.range.loop, List.cons_append,
      List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      cell_cast, Trace.row, Bit.kSb, Bit.kCid, cH, cTs, Bit.is64, Bit.rb, Nat.reduceAdd, Nat.reduceMul, decMsg,
      List.getD_cons_zero, List.getD_cons_succ, bit_rnToNat, bit_zeroToNat,
      bit_limbToNat r0 r1, bit_limbToNat r2 r3, bit_limbToNat r4 r5, bit_limbToNat r6 r7]
  -- time checks of the consumed values
  have tA := hocc _ (show r16 (v cTs - v Bit.ta - 1 - B16 * v Bit.ha) Bit.act ∈ Bit.inters by simp [Bit.inters, timeChk])
  have tA' := hocc _ (show r16 (4 * v Bit.ha) Bit.act ∈ Bit.inters by simp [Bit.inters, timeChk])
  have tB := hocc _ (show r16 (v cTs - v Bit.tb - 1 - B16 * v Bit.hb) Bit.act ∈ Bit.inters by simp [Bit.inters, timeChk])
  have tB' := hocc _ (show r16 (4 * v Bit.hb) Bit.act ∈ Bit.inters by simp [Bit.inters, timeChk])
  simp only [r16, cnt] at tA tA' tB tB'
  simp only [List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_mul',
    Expr.eval_ofNat', B16, cell_cast, Trace.row, Bit.kSb, Bit.kCid, cTs, Bit.ta, Bit.ha, Bit.tb, Bit.hb] at tA tA' tB tB'
  obtain ⟨nA, hnA, eA⟩ := time_chk L tA tA'
  obtain ⟨nB, hnB, eB⟩ := time_chk L tB tB'
  rw [bit_rnToNat] at eA eB
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Bit.op (v cH) (v cFee) zeros4 Bit.act) (by simp [Bit.inters, stdState])
  simp only [fetch, cnt] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hlt := recordOf_op_lt hrc
  rw [hre] at hm hlt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hlt
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, zeros4, v, Expr.eval_col,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cell_cast, Trace.row, Bit.kSb, Bit.kCid, cPc, cH, cFee, Bit.op, Bit.is64,
    Bit.fOr, Bit.fXor, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 2 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = 0x71 + 18 * rowNat tr 2 r 8 + rowNat tr 2 r 6 + 2 * rowNat tr 2 r 7 := by
    simp only [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_mul] at eop
    exact (natEq eop (by omega) (by omega)).symm
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl,
    ⟨fee, hfl, by rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']⟩,
    ?_, ?_, by rw [hProd]; simp⟩
  rotate_left
  · rw [hCons, hIn]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, lvl,
      List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨⟨nA, by omega, eA⟩, ⟨nB, by omega, eB⟩⟩
  · rw [hProd, hIn]; simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, lvl,
      List.getD_cons_succ, List.getD_cons_zero]; exact ⟨hcP _, trivial⟩
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have p0 : rowNat tr 2 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 2 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 2 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 2 r 37 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 2 r 38 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
  have hsbR := R.sbLe
  have hpc : pc0 = X.offOf E.k + pc := natEq (e0.symm.trans i0) (by omega) (by omega)
  subst hpc
  obtain ⟨hqk, hlpc⟩ := X.loc_unique hq hl R.kLt hpcl hoff
  subst q
  subst l
  have hH := R.height
  have hHb := CF.hBound pc hpcl
  rw [hH] at eh hHb
  simp only [Option.getD_some] at eh hHb
  have p3 : rowNat tr 2 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  have hout : rowOut Bit.table tr pub 2 r = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hCons, hProd] at *
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  have hins' : ins = .num op := by
    rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
    all_goals first
      | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
      | (exfalso; omega)
      | exact h
      | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
      | (exfalso; simp only [opCall] at h; omega)
  subst hins'
  have hcases : (rowNat tr 2 r 6 = 0 ∧ rowNat tr 2 r 7 = 0) ∨ (rowNat tr 2 r 6 = 1 ∧ rowNat tr 2 r 7 = 0) ∨
      (rowNat tr 2 r 6 = 0 ∧ rowNat tr 2 r 7 = 1) := by omega
  have hbin : isBinop op := by
    rw [hop]; rcases hcases with ⟨g6, g7⟩ | ⟨g6, g7⟩ | ⟨g6, g7⟩ <;> rcases f8 with g8 | g8 <;>
      rw [g6, g7, g8] <;> simp [isBinop, binops]
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hbin
  have hk : kindOf ls0 (.num op) = some (.straight 2 1) := by simp [kindOf, hfam, hpops]
  obtain ⟨h2, -⟩ := verify_straight X R.kLt hpcl hins hL0 R.height hk (by intro bt; simp) (by simp)
    (by simp) (by simp) (by intro l; simp) (by intro l; simp)
  have sl2 : (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat = s.stack.size - 2 := by
    exact slot_toNat psb p3 hsbR h2 hszP
  have sl1 : (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat = s.stack.size - 1 := by
    exact slot_toNat psb p3 hsbR (by omega) hszP
  have hwk : opW op = 32 + 32 * rowNat tr 2 r 8 ∧ opK op = 7 + rowNat tr 2 r 6 + 2 * rowNat tr 2 r 7 := by
    rw [hop]; rcases hcases with ⟨g6, g7⟩ | ⟨g6, g7⟩ | ⟨g6, g7⟩ <;> rcases f8 with g8 | g8 <;>
      rw [g6, g7, g8] <;> simp [opW, opK]
  have eA8 := val4_bytes (fun k => rowNat tr 2 r (9 + k))
  have eB8 := val4_bytes (fun k => rowNat tr 2 r (19 + k))
  have eR8 := val4_bytes (fun k => rowNat tr 2 r (29 + k))
  simp only [Nat.reduceAdd] at eA8 eB8 eR8
  obtain ⟨s', hs', hrel⟩ := step_binop X R hins hbin hfee hg hg64
    ⟨0, (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 2 r 8,
          rowNat tr 2 r 9 + 256 * rowNat tr 2 r 10, rowNat tr 2 r 11 + 256 * rowNat tr 2 r 12,
          rowNat tr 2 r 13 + 256 * rowNat tr 2 r 14, rowNat tr 2 r 15 + 256 * rowNat tr 2 r 16, rowNat tr 2 r 17⟩
    ⟨0, (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 2 r 8,
          rowNat tr 2 r 19 + 256 * rowNat tr 2 r 20, rowNat tr 2 r 21 + 256 * rowNat tr 2 r 22,
          rowNat tr 2 r 23 + 256 * rowNat tr 2 r 24, rowNat tr 2 r 25 + 256 * rowNat tr 2 r 26, rowNat tr 2 r 27⟩
    ⟨0, (((rowNat tr 2 r 37 : Nat) : F) + ((rowNat tr 2 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 2 r 8,
          rowNat tr 2 r 29 + 256 * rowNat tr 2 r 30, rowNat tr 2 r 31 + 256 * rowNat tr 2 r 32,
          rowNat tr 2 r 33 + 256 * rowNat tr 2 r 34, rowNat tr 2 r 35 + 256 * rowNat tr 2 r 36, rowNat tr 2 r 1⟩
    (hlive _ (by simp)) (hlive _ (by simp)) ⟨rfl, sl2⟩ ⟨rfl, sl1⟩
    ⟨rfl, sl2, p1, by rw [hwk.1]; rcases f8 with g8 | g8 <;> rw [g8] <;> rfl⟩
    (by
      intro _ _
      have hlk : ∀ k, k < 8 → rowNat tr 2 r (Bit.ab + k) < 256 ∧ rowNat tr 2 r (Bit.bb + k) < 256 ∧
          rowNat tr 2 r (Bit.rb + k) = byteF (rowNat tr 2 r Bit.fAnd + 2 * rowNat tr 2 r Bit.fOr +
            3 * rowNat tr 2 r Bit.fXor) (rowNat tr 2 r (Bit.ab + k)) (rowNat tr 2 r (Bit.bb + k)) := hbyte
      obtain ⟨-, hup, hsem⟩ := bit_sound (rowNat tr 2 r) (tr.row pub 2 r) hcP hcon a567 hlk
      simp only [Bit.ab, Bit.bb, Bit.rb, Bit.is64, Bit.fOr, Bit.fXor] at hup hsem
      refine ⟨?_, ?_⟩
      · simp only [Msg.ok]
        refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        rcases f8 with g8 | g8
        · have z4 := hup g8 4 (by omega) (by omega); have z5 := hup g8 5 (by omega) (by omega)
          have z6 := hup g8 6 (by omega) (by omega); have z7 := hup g8 7 (by omega) (by omega)
          simp only [Nat.reduceAdd] at z4 z5 z6 z7
          exact Or.inl ⟨g8, by omega, by omega⟩
        · exact Or.inr g8
      · simp only [Msg.val]; rw [hwk.1, hwk.2, eA8, eB8, eR8]; exact hsem)
  exact ⟨s', hs', hrel⟩

end WasmBase
