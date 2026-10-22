import WasmBase.Main.Rows
import WasmBase.StepCall
import WasmBase.Main.RowCtrl
import WasmBase.Main.MemInit
/-!
# Row lemma: RET (return from a callee)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

theorem ret_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Ret.constraints, e.eval (natRow c rw) = 0) :
    (c Ret.fRet = 0 ∨ c Ret.fRet = 1) ∧ (c Ret.fRif = 0 ∨ c Ret.fRif = 1) ∧ c Ret.fRet + c Ret.fRif ≤ 1 ∧
    (c Ret.c + c (Ret.c + 1) < P → Ret.nz.eval (natRow c rw) = ((if c Ret.c + c (Ret.c + 1) = 0 then 0 else 1 : Nat) : F)) ∧
    (c Ret.fRet + c Ret.fRif = 1 → c Ret.kCid ≠ 0) ∧
    (Ret.tk * (v Ret.n0 + B16 * v Ret.n1 - v Ret.r0 - B16 * v Ret.r1 - v Ret.charge)).eval (natRow c rw) = 0 ∧
    (Ret.nz.eval (natRow c rw) = 0 ∨ Ret.nz.eval (natRow c rw) = 1) := by
  have hP' := P_val
  have hb := hc
  simp only [Ret.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨bR, bI, bAct, hnz, hcid, hbud⟩ := hb
  simp only [Chips.bool, v, Ret.act, Ret.nz, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at bR bI bAct hnz hcid
  have r := bool_nat (hP _) bR; have i := bool_nat (hP _) bI
  refine ⟨r, i, ?_, fun hz => ?_, fun h1 h0 => ?_, hbud, ?_⟩
  · have hs : c Ret.fRet + c Ret.fRif < P := by omega
    have := bool_nat hs (by simpa only [Lean.Grind.Semiring.natCast_add] using bAct)
    omega
  · have hn := nz_val (inv := c Ret.inv) hz (by
      simpa only [Lean.Grind.Semiring.natCast_add] using hnz)
    simp only [Ret.nz, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, natRow]
    rw [show ((c Ret.c : F) + (c (Ret.c + 1) : F)) = ((c Ret.c + c (Ret.c + 1) : Nat) : F) by
      simp only [Lean.Grind.Semiring.natCast_add]]
    exact hn
  · rw [h0] at hcid
    have e : ((c Ret.fRet : Nat) : F) + ((c Ret.fRif : Nat) : F) = ((1 : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_add, h1]
    rw [e] at hcid
    have : ((1 : Nat) : F) * (((0 : Nat) : F) * ((c Ret.invc : Nat) : F) - ((1 : Nat) : F)) = -1 := by grind
    rw [this] at hcid
    exact absurd hcid (by decide)
  · simp only [Ret.nz, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, natRow]
    rcases mul_eq_zero' hnz with h | h
    · left; rw [h]; grind
    · right; grind

theorem ret_count_cases : ∀ i ∈ Ret.inters, i.count = Ret.act ∨ i.count = v Ret.fRif ∨ i.count = Ret.tk := by
  intro i hi
  have := List.all_eq_true.mp (show Ret.inters.all (fun i => decide (i.count = Ret.act ∨ i.count = v Ret.fRif ∨
    i.count = Ret.tk)) = true by decide) i hi
  exact of_decide_eq_true this

/-- RET counts as naturals. -/
theorem ret_count_vals_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Ret.table.constraints, e.eval (natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0) :
    rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif ≤ 1 ∧
    (Ret.act.eval (tr.row pub 14 r)).toNat = rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif ∧
    ((v Ret.fRif).eval (tr.row pub 14 r)).toNat = rowNat tr 14 r Ret.fRif ∧
    (Ret.tk.eval (tr.row pub 14 r)).toNat ≤ rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif := by
  have hP' := P_val
  obtain ⟨r1, r2, hs, -, -, -, hnzb⟩ := ret_sound (rowNat tr 14 r) (tr.row pub 14 r) (rowNat_lt tr 14 r) hcon
  rw [← row_eq_natRow] at hnzb
  have hcP := rowNat_lt tr 14 r
  refine ⟨hs, ?_, ?_, ?_⟩
  · show (tr.cell 14 r Ret.fRet + tr.cell 14 r Ret.fRif).toNat = _
    rw [cell_cast, cell_cast, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]
  · show (tr.cell 14 r Ret.fRif).toNat = _; rfl
  · show (tr.cell 14 r Ret.fRet + tr.cell 14 r Ret.fRif * Ret.nz.eval (tr.row pub 14 r)).toNat ≤ _
    rw [cell_cast, cell_cast]
    rcases hnzb with h | h <;> rw [h]
    · rw [show ((rowNat tr 14 r Ret.fRet : Nat) : F) + ((rowNat tr 14 r Ret.fRif : Nat) : F) * 0 =
        ((rowNat tr 14 r Ret.fRet : Nat) : F) by grind, Fp.toNat_cast_of_lt (hcP _)]; omega
    · rw [show ((rowNat tr 14 r Ret.fRet : Nat) : F) + ((rowNat tr 14 r Ret.fRif : Nat) : F) * 1 =
        ((rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif : Nat) : F) by
          rw [Lean.Grind.Semiring.natCast_add]; grind, Fp.toNat_cast_of_lt (by have := P_val; omega)]
      exact Nat.le_refl _

theorem ret_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Ret.table.constraints, e.eval (natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0) :
    ∀ i ∈ Ret.inters, (i.count.eval (tr.row pub 14 r)).toNat ≤ 1 := by
  obtain ⟨hs, ha, hf, ht⟩ := ret_count_vals_of hcon
  intro i hi
  rcases ret_count_cases i hi with h | h | h <;> rw [h] <;> omega

theorem ret_count_vals {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 14) :
    rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif ≤ 1 ∧
    (Ret.act.eval (tr.row pub 14 r)).toNat = rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif ∧
    ((v Ret.fRif).eval (tr.row pub 14 r)).toNat = rowNat tr 14 r Ret.fRif ∧
    (Ret.tk.eval (tr.row pub 14 r)).toNat ≤ rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif :=
  ret_count_vals_of (table_constr H (by simp [air_len]) hr)

theorem ret_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 14) :
    ∀ i ∈ Ret.inters, (i.count.eval (tr.row pub 14 r)).toNat ≤ 1 :=
  ret_counts_of (table_constr H (by simp [air_len]) hr)

theorem ret_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 14)
    (hna : ¬ rowAct Ret.table tr pub 14 r) :
    ∀ i ∈ Ret.inters, (i.count.eval (tr.row pub 14 r)).toNat ≠ 1 := by
  obtain ⟨hs, ha, hf, ht⟩ := ret_count_vals H hr
  have h0 : rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif = 0 := by
    have : (Ret.act.eval (tr.row pub 14 r)).toNat ≠ 1 := hna
    omega
  intro i hi
  rcases ret_count_cases i hi with h | h | h <;> rw [h] <;> omega

theorem ret_filterC :
    Ret.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)) =
      [stkRecv (v Ret.kSb + v cH - 1) 0 [v Ret.c, v (Ret.c + 1), 0, 0] (v Ret.tc) (v Ret.fRif),
       chRecv 4 (v Ret.kCid) 0 [v Ret.retpc, v Ret.sbc, v Ret.cidc, v Ret.charge] (v Ret.tpr) Ret.tk,
       chRecv 5 0 0 [v Ret.r0, v Ret.r1, 0, 0] (v Ret.tpb) Ret.tk] := by decide

theorem ret_filterP :
    Ret.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) =
      [chSend 5 0 0 [v Ret.n0, v Ret.n1, 0, 0] (v cTs) Ret.tk] := by decide

set_option maxHeartbeats 4000000 in
theorem ret_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 14) (hact : rowAct Ret.table tr pub 14 r) :
    RowFacts X (rowIn Ret.table tr pub 14 r) (rowOut Ret.table tr pub 14 r)
      (rowCons Ret.table tr pub 14 r) (rowProd Ret.table tr pub 14 r) := by
  have hP' := P_val
  have ht : 14 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 14 r i < P := rowNat_lt tr 14 r
  have hcon : ∀ e ∈ Ret.table.constraints, e.eval (natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨gR, gI, gS, gnzv, gcid, gbud, gnz⟩ := ret_sound (rowNat tr 14 r) (tr.row pub 14 r) hcP hcon
  rw [← row_eq_natRow] at gbud gnz gnzv
  obtain ⟨-, ha, hf, -⟩ := ret_count_vals H hr
  have a1 : rowNat tr 14 r Ret.fRet + rowNat tr 14 r Ret.fRif = 1 := ha.symm.trans hact
  have hocc : ∀ i ∈ Ret.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 14 r)),
      (i.count.eval (tr.row pub 14 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Ret.table.inters from hi)
  let cc : Nat → F := fun i => ((rowNat tr 14 r i : Nat) : F)
  let N := Ret.nz.eval (tr.row pub 14 r)
  have hTK : Ret.tk.eval (tr.row pub 14 r) = cc Ret.fRet + cc Ret.fRif * N := by
    show tr.cell 14 r Ret.fRet + tr.cell 14 r Ret.fRif * N = _
    rw [cell_cast, cell_cast]
  -- the three cases: plain return; taken br_if return; untaken br_if
  have hcases : (rowNat tr 14 r Ret.fRet = 1 ∧ rowNat tr 14 r Ret.fRif = 0) ∨ (rowNat tr 14 r Ret.fRet = 0 ∧ rowNat tr 14 r Ret.fRif = 1 ∧ N = 1) ∨
      (rowNat tr 14 r Ret.fRet = 0 ∧ rowNat tr 14 r Ret.fRif = 1 ∧ N = 0) := by
    rcases gR with h | h <;> rcases gnz with hn | hn
    · right; right; exact ⟨h, by omega, hn⟩
    · right; left; exact ⟨h, by omega, hn⟩
    · left; exact ⟨h, by omega⟩
    · left; exact ⟨h, by omega⟩
  have tkV : (Ret.tk.eval (tr.row pub 14 r)).toNat = if rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 then 1 else 0 := by
    rw [hTK]
    rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · simp only [cc, show rowNat tr 14 r Ret.fRet = 1 from e1, show rowNat tr 14 r Ret.fRif = 0 from e2]
      rw [if_pos (Or.inl trivial)]
      rw [show ((1 : Nat) : F) + ((0 : Nat) : F) * N = ((1 : Nat) : F) by grind]; rfl
    · simp only [cc, show rowNat tr 14 r Ret.fRet = 0 from e1, show rowNat tr 14 r Ret.fRif = 1 from e2, e3]
      rw [if_pos (Or.inr trivial)]
      rw [show ((0 : Nat) : F) + ((1 : Nat) : F) * 1 = ((1 : Nat) : F) by grind]; rfl
    · simp only [cc, show rowNat tr 14 r Ret.fRet = 0 from e1, show rowNat tr 14 r Ret.fRif = 1 from e2, e3]
      rw [if_neg (fun h => by
        rcases h with h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide))]
      rw [show ((0 : Nat) : F) + ((1 : Nat) : F) * 0 = ((0 : Nat) : F) by grind]; rfl
  have hIn : rowIn Ret.table tr pub 14 r = [cc 0, cc 1, cc 2, ((0 : Nat) : F), cc Ret.kSb, cc Ret.kCid] := by
    simp only [rowIn, Ret.table, Ret.inters, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cTs, cS, cc]
  have hOut : rowOut Ret.table tr pub 14 r =
      [(cc Ret.fRet + cc Ret.fRif * N) * cc Ret.retpc + (1 - (cc Ret.fRet + cc Ret.fRif * N)) * (cc 0 + 1),
        cc 1 + ((1 : Nat) : F), cc 2 + cc 4, ((0 : Nat) : F),
        (cc Ret.fRet + cc Ret.fRif * N) * cc Ret.sbc + (1 - (cc Ret.fRet + cc Ret.fRif * N)) * cc Ret.kSb,
        (cc Ret.fRet + cc Ret.fRif * N) * cc Ret.cidc + (1 - (cc Ret.fRet + cc Ret.fRif * N)) * cc Ret.kCid] := by
    simp only [rowOut, Ret.table, Ret.inters, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
      Expr.eval_ofNat', hTK]
    simp only [v, Expr.eval_col, cell_cast, Trace.row, cPc, cTs, cS, cFee, cc, cast_one]
  have cntR : ((v Ret.fRif).eval (tr.row pub 14 r)).toNat = rowNat tr 14 r Ret.fRif := hf
  -- the consumed and produced messages
  let mC : Msg := ⟨0, (cc Ret.kSb + cc 3 - ((1 : Nat) : F)).toNat, 0, rowNat tr 14 r Ret.c,
    rowNat tr 14 r (Ret.c + 1), 0, 0, rowNat tr 14 r Ret.tc⟩
  let mR : Msg := ⟨4, rowNat tr 14 r Ret.kCid, 0, rowNat tr 14 r Ret.retpc, rowNat tr 14 r Ret.sbc,
    rowNat tr 14 r Ret.cidc, rowNat tr 14 r Ret.charge, rowNat tr 14 r Ret.tpr⟩
  let mB : Msg := ⟨5, 0, 0, rowNat tr 14 r Ret.r0, rowNat tr 14 r Ret.r1, 0, 0, rowNat tr 14 r Ret.tpb⟩
  let mB' : Msg := ⟨5, 0, 0, rowNat tr 14 r Ret.n0, rowNat tr 14 r Ret.n1, 0, 0, rowNat tr 14 r 1⟩
  have z5 : (((5 : Nat) : F)).toNat = 5 := Fp.toNat_cast_of_lt (by omega)
  have z4 : (((4 : Nat) : F)).toNat = 4 := Fp.toNat_cast_of_lt (by omega)
  have z0 : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by omega)
  have hCons : rowCons Ret.table tr pub 14 r =
      (if rowNat tr 14 r Ret.fRif = 1 then [mC] else []) ++
        (if rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 then [mR, mB] else []) := by
    rw [rowCons, rowMsgs_eq]
    show (List.filterMap _ (Ret.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)))).map decMsg = _
    rw [ret_filterC]
    simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, cntR, tkV]
    by_cases hw : rowNat tr 14 r Ret.fRif = 1 <;> by_cases ht : rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 <;>
      simp only [hw, ht, ite_true, ite_false, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.append_nil, Nat.zero_ne_one, List.filterMap_cons, List.filterMap_nil] <;>
      simp only [v, Expr.eval_col, Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', cell_cast, Trace.row, cH,
        Ret.kSb, Ret.kCid, Ret.c, Ret.tc, Ret.retpc, Ret.sbc, Ret.cidc, Ret.charge, Ret.tpr, Ret.r0, Ret.r1, Ret.tpb,
        decMsg, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _), z0, z4, z5,
        List.cons.injEq, and_true, mC, mR, mB, cc] <;> rfl
  have hProd : rowProd Ret.table tr pub 14 r = if rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 then [mB'] else [] := by
    rw [rowProd, rowMsgs_eq]
    show (List.filterMap _ (Ret.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)))).map decMsg = _
    rw [ret_filterP]
    simp only [List.filterMap_cons, List.filterMap_nil, chSend, tkV]
    by_cases ht : rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 <;>
      simp only [ht, ite_true, ite_false, List.map_cons, List.map_nil, Nat.zero_ne_one] <;>
      simp only [v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cTs, Ret.n0, Ret.n1, decMsg,
        List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _), z0, z5, List.cons.injEq, and_true,
        mB'] <;> rfl
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Ret.op (v cH) (v cFee) zeros4 Ret.act) (by simp [Ret.inters])
  have cntA : (Ret.act.eval (tr.row pub 14 r)).toNat = 1 := hact
  simp only [fetch, cntA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  rw [hre] at hm
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add',
    Expr.eval_mul', Expr.eval_c, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cH, cFee, Ret.op, Ret.fRet, Ret.fRif,
    zeros4, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 14 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = Ctrl.opHalt * rowNat tr 14 r Ret.fRet + Ctrl.opHif * rowNat tr 14 r Ret.fRif := by
    simp only [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add] at eop
    have hoplt := recordOf_op_lt hrc
    rw [hre] at hoplt; simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
    refine (natEq eop ?_ (by omega)).symm
    simp only [Ctrl.opHalt, Ctrl.opHif, Ret.fRet, Ret.fRif] at *; omega
  -- channel time checks
  have tchk : ∀ (cnt : Expr) (tpc hic : Nat), (cnt.eval (tr.row pub 14 r)).toNat = 1 →
      r16 (v cTs - v tpc - 1 - B16 * v hic) cnt ∈ Ret.inters → r16 (4 * v hic) cnt ∈ Ret.inters →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 14 r tpc + 1 + n : Nat) : F) = ((rowNat tr 14 r 1 : Nat) : F) := by
    intro cnt tpc hic hc m1 m2
    have h1 := hocc _ m1
    have h2 := hocc _ m2
    simp only [r16, hc] at h1 h2
    simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat',
      B16, cTs, Trace.row] at h1 h2
    obtain ⟨n, hn, e⟩ := time_chk L h1 h2
    exact ⟨n, hn, e.trans (cell_cast tr 14 r 1)⟩
  -- budget limbs of the produced register
  have hn0 : (rowNat tr 14 r Ret.fRet = 1 ∨ N = 1) → rowNat tr 14 r Ret.n0 < 65536 ∧ rowNat tr 14 r Ret.n1 < 16384 := by
    intro htk
    have hc : (Ret.tk.eval (tr.row pub 14 r)).toNat = 1 := by rw [tkV, if_pos htk]
    have b0 := row_r16 L ht hr (v Ret.n0) Ret.tk
      (show r16 (v Ret.n0) Ret.tk ∈ Ret.table.inters by simp [Ret.table, Ret.inters]) hc
    have b1 := row_r16 L ht hr (v Ret.n1) Ret.tk
      (show r16 (v Ret.n1) Ret.tk ∈ Ret.table.inters by simp [Ret.table, Ret.inters]) hc
    have b2 := row_r16 L ht hr (4 * v Ret.n1) Ret.tk
      (show r16 (4 * v Ret.n1) Ret.tk ∈ Ret.table.inters by simp [Ret.table, Ret.inters]) hc
    simp only [v, Expr.eval_col, Expr.eval_mul', Expr.eval_ofNat', Trace.row] at b0 b1 b2
    rw [cell_cast] at b0 b1 b2
    rw [Fp.toNat_cast_of_lt (hcP _)] at b0 b1
    rw [← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)] at b2
    exact ⟨b0, by omega⟩
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee, hfl, ?_⟩, ?_, ?_, ?_⟩
  rotate_left
  · rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee', cc]
  · rw [hCons, hIn]
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · rename_i hw
        simp only [List.mem_singleton] at hx; subst hx
        exact tchk (v Ret.fRif) Ret.tc Ret.hc (by rw [cntR]; exact hw) (by simp [Ret.inters, timeChk])
          (by simp [Ret.inters, timeChk])
      · simp at hx
    · split at hx
      · rename_i htk
        have hc : (Ret.tk.eval (tr.row pub 14 r)).toNat = 1 := by rw [tkV, if_pos htk]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact tchk Ret.tk Ret.tpr Ret.hr hc (by simp [Ret.inters, timeChk]) (by simp [Ret.inters, timeChk])
        · exact tchk Ret.tk Ret.tpb Ret.hb hc (by simp [Ret.inters, timeChk]) (by simp [Ret.inters, timeChk])
      · simp at hx
  · rw [hProd, hIn]
    intro x hx
    split at hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨hcP _, rfl⟩
    · simp at hx
  · rw [hProd]; split <;> simp
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : rowNat tr 14 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 14 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 14 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 14 r Ret.kSb = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 14 r Ret.kCid = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
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
  have p3 : rowNat tr 14 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hlen : f.labels.length = ls0.length := by rw [hfl0, shiftLabels_length]
  rw [hL0] at hcase
  simp only [Option.getD_some] at hcase
  have hcid : E.cid ≠ 0 := by rw [← pcid]; exact gcid a1
  -- the budget register consumed on a return
  obtain ⟨tpb0, htpb0, hbudE⟩ := R.calls.budget
  have hbudLive : live mB → mB = budMsg s.stackRem tpb0 := fun h =>
    (hbudE mB rfl).mp (R.env_msg h (by simp [mB]) (by simp [mB, Env.lsp]; omega))
  obtain ⟨sv, hch, -, -, hrl⟩ := R.calls.chain
  have hrem30 : s.stackRem < 2 ^ 30 := by omega
  rw [hCons] at hlive
  rw [hCons, hProd]
  -- the produced budget register after a return
  have hbnew : ∀ (cg : Nat), cg < 2 ^ 26 → rowNat tr 14 r Ret.charge = cg →
      (rowNat tr 14 r Ret.fRet = 1 ∨ N = 1) → mB = budMsg s.stackRem tpb0 → mB' = budMsg (s.stackRem + cg) t := by
    intro cg hcg hch htk hmB
    obtain ⟨b0, b1⟩ := hn0 htk
    have hr0 : rowNat tr 14 r Ret.r0 = s.stackRem % 65536 := by
      have := congrArg Msg.l0 hmB; simpa [mB, budMsg] using this
    have hr1 : rowNat tr 14 r Ret.r1 = s.stackRem / 65536 := by
      have := congrArg Msg.l1 hmB; simpa [mB, budMsg] using this
    have hT1 : Ret.tk.eval (tr.row pub 14 r) = 1 := by
      have := tkV; rw [if_pos htk] at this
      have e := Fp.cast_toNat (Ret.tk.eval (tr.row pub 14 r)); rw [this] at e; rw [← e]; rfl
    have gb := gbud
    rw [Expr.eval_mul', hT1] at gb
    simp only [Expr.eval_sub', Expr.eval_add', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat', B16,
      Trace.row] at gb
    rw [cell_cast, cell_cast, cell_cast, cell_cast, cell_cast, hr0, hr1, hch] at gb
    have e : ((rowNat tr 14 r Ret.n0 + 65536 * rowNat tr 14 r Ret.n1 : Nat) : F) =
        ((s.stackRem % 65536 + 65536 * (s.stackRem / 65536) + cg : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
    have e' := natEq e (by omega) (by omega)
    simp only [mB', budMsg, Msg.mk.injEq, true_and]
    exact ⟨by omega, by omega, p1⟩
  -- the output STATE on a taken return
  have houtR : (cc Ret.fRet + cc Ret.fRif * N = 1) → ∀ k' pc' sb' cid' : Nat,
      rowNat tr 14 r Ret.retpc = X.offOf k' + pc' → rowNat tr 14 r Ret.sbc = sb' → rowNat tr 14 r Ret.cidc = cid' →
      rowOut Ret.table tr pub 14 r = stMsg (X.offOf k' + pc') (t + 1) (S + fee) 0 sb' cid' := by
    intro h1 k' pc' sb' cid' f3 f4 f5
    rw [hOut, h1]
    simp only [stMsg, cc, f3, f4, f5, p1, p2, efee', Lean.Grind.Semiring.natCast_add, List.cons.injEq, and_true]
    refine ⟨by grind, trivial, trivial, by grind, by grind⟩
  -- the record of a taken return and the kinds of the instruction
  have hkinds : ∀ (o : Nat), op = o →
      (o = Ctrl.opHalt → kindOf ls0 ins = some .halt) ∧ (o = Ctrl.opHif → kindOf ls0 ins = some .haltIf) := by
    intro o ho
    constructor <;> intro hoo <;> subst ho hoo <;>
    rcases hcase with ⟨v, hv, h, hl⟩ | ⟨v, hv, h, hl⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨x, hv, h, hl⟩ | ⟨x, hv, h, hl⟩ |
      ⟨x, hv, h, hl⟩ | ⟨_, hf, _⟩ | ⟨hk, h, hl⟩ | ⟨tg, hk, h, hl⟩ | ⟨tg, hk, h, hl⟩ | ⟨hk, h, hl⟩ | ⟨hk, h, hl⟩ |
      ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩ <;>
    first
      | exact hk
      | (exfalso; revert h; simp [Ctrl.opHalt, Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHif, opCall])
      | (exfalso; revert hf; decide)
      | (exfalso; simp [Ctrl.opHalt, Ctrl.opHif] at hmem)
      | (exfalso; revert hgl; simp [Ctrl.opHalt, Ctrl.opHif])
  rcases hcases with ⟨eR, eI⟩ | ⟨eR, eI, eN⟩ | ⟨eR, eI, eN⟩
  · -- plain return
    have htk : rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 := Or.inl eR
    have hopH : op = Ctrl.opHalt := by rw [hop, eR, eI]; simp
    have hkind := ctrl_kind_halt ((hkinds op rfl).1 hopH)
    rw [← hlen] at hkind
    simp only [if_pos htk, show ¬ rowNat tr 14 r Ret.fRif = 1 by omega, ite_false, List.nil_append] at hlive ⊢
    have hmR := hlive mR (by simp)
    have hmB := hbudLive (hlive mB (by simp))
    have hmBl : live (budMsg s.stackRem tpb0) := hmB ▸ hlive mB (by simp)
    have h1 : cc Ret.fRet + cc Ret.fRif * N = 1 := by
      simp only [cc, show rowNat tr 14 r Ret.fRet = 1 from eR, show rowNat tr 14 r Ret.fRif = 0 from eI]; grind
    by_cases hg : X.R * (S + fee - S_seg) ≤ segb
    · obtain ⟨fc, rest', cS, hrest, hmeq, s', hstep, hrel⟩ :=
        step_return X R hins hkind hfee hg hg64 hcid hmR rfl pcid hmBl
      have f3 := congrArg Msg.l0 hmeq; have f4 := congrArg Msg.l1 hmeq; have f5 := congrArg Msg.l2 hmeq
      have f6 := congrArg Msg.l3 hmeq
      simp only [mR, callMsg] at f3 f4 f5 f6
      refine ⟨cS.k, fc.pc, fee, 0, cS.sb, cS.cid, hfl, by omega, houtR h1 _ _ _ _ f3 f4 f5,
        fun _ => ⟨fun _ => ⟨s', hstep, ?_⟩, fun h => absurd h (by decide)⟩⟩
      rw [hbnew _ (X.factsOf R.kLt).chargeLt f6 htk hmB, hmB]
      exact hrel
    · obtain ⟨fc, rest', cS, hrest, hmeq⟩ := R.call_rec hcid hmR rfl pcid
      have f3 := congrArg Msg.l0 hmeq; have f4 := congrArg Msg.l1 hmeq; have f5 := congrArg Msg.l2 hmeq
      simp only [mR, callMsg] at f3 f4 f5
      exact ⟨cS.k, fc.pc, fee, 0, cS.sb, cS.cid, hfl, by omega, houtR h1 _ _ _ _ f3 f4 f5, fun hg' => absurd hg' hg⟩
  all_goals
    have hopF : op = Ctrl.opHif := by rw [hop, eR, eI]; simp
    obtain ⟨l, rfl, hl'⟩ := ctrl_kind_hif ((hkinds op rfl).2 hopF)
    rw [← hlen] at hl'
    have h1 := ctrl_brIf_h R hins
    have hmC := hlive mC (by simp [eI])
    have sc : mC.space = 0 ∧ mC.slot = s.stack.size - 1 := ⟨rfl, by
      show (cc Ret.kSb + cc 3 - ((1 : Nat) : F)).toNat = _
      simp only [cc]; exact slot_toNat psb p3 hsbR h1 hszP⟩
    obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmC sc.1 sc.2 (by omega)
    obtain ⟨o0, o1, -⟩ := okc
    simp only [mC] at o0 o1
    have hNv : N = ((if rowNat tr 14 r Ret.c + rowNat tr 14 r (Ret.c + 1) = 0 then 0 else 1 : Nat) : F) :=
      gnzv (by omega)
    have hval : mC.val = 0 ↔ rowNat tr 14 r Ret.c + rowNat tr 14 r (Ret.c + 1) = 0 := by
      simp only [Msg.val, val4, mC]; omega
  · -- taken: return to the caller
    have htk : rowNat tr 14 r Ret.fRet = 1 ∨ N = 1 := Or.inr eN
    have hnz0 : rowNat tr 14 r Ret.c + rowNat tr 14 r (Ret.c + 1) ≠ 0 := by
      intro h0; rw [if_pos h0] at hNv; rw [hNv] at eN; exact absurd eN (by decide)
    simp only [if_pos htk, show rowNat tr 14 r Ret.fRif = 1 from eI, ite_true, List.cons_append, List.nil_append]
      at hlive ⊢
    have hmR := hlive mR (by simp)
    have hmB := hbudLive (hlive mB (by simp))
    have hmBl : live (budMsg s.stackRem tpb0) := hmB ▸ hlive mB (by simp)
    have h1' : cc Ret.fRet + cc Ret.fRif * N = 1 := by
      simp only [cc, show rowNat tr 14 r Ret.fRet = 0 from eR, show rowNat tr 14 r Ret.fRif = 1 from eI, eN]; grind
    by_cases hg : X.R * (S + fee - S_seg) ≤ segb
    · obtain ⟨fc, rest', cS, hrest, hmeq, s', hstep, hrel⟩ :=
        (step_returnIf X R hl' hins hfee hg hg64 hcid mC hmC sc).1 (fun h => hnz0 (hval.mp h)) hmR rfl pcid hmBl
      have f3 := congrArg Msg.l0 hmeq; have f4 := congrArg Msg.l1 hmeq; have f5 := congrArg Msg.l2 hmeq
      have f6 := congrArg Msg.l3 hmeq
      simp only [mR, callMsg] at f3 f4 f5 f6
      refine ⟨cS.k, fc.pc, fee, 0, cS.sb, cS.cid, hfl, by omega, houtR h1' _ _ _ _ f3 f4 f5,
        fun _ => ⟨fun _ => ⟨s', hstep, ?_⟩, fun h => absurd h (by decide)⟩⟩
      rw [hbnew _ (X.factsOf R.kLt).chargeLt f6 htk hmB, hmB]
      exact hrel
    · obtain ⟨fc, rest', cS, hrest, hmeq⟩ := R.call_rec hcid hmR rfl pcid
      have f3 := congrArg Msg.l0 hmeq; have f4 := congrArg Msg.l1 hmeq; have f5 := congrArg Msg.l2 hmeq
      simp only [mR, callMsg] at f3 f4 f5
      exact ⟨cS.k, fc.pc, fee, 0, cS.sb, cS.cid, hfl, by omega, houtR h1' _ _ _ _ f3 f4 f5, fun hg' => absurd hg' hg⟩
  · -- not taken: continue at pc + 1
    have htk : ¬ (rowNat tr 14 r Ret.fRet = 1 ∨ N = 1) := by
      rintro (h | h)
      · omega
      · rw [eN] at h; exact absurd h (by decide)
    have hz : rowNat tr 14 r Ret.c + rowNat tr 14 r (Ret.c + 1) = 0 := by
      by_cases hc : rowNat tr 14 r Ret.c + rowNat tr 14 r (Ret.c + 1) = 0
      · exact hc
      · exfalso; rw [if_neg hc] at hNv; rw [hNv] at eN; exact absurd eN (by decide)
    simp only [if_neg htk, show rowNat tr 14 r Ret.fRif = 1 from eI, ite_true, List.append_nil] at hlive ⊢
    have h0' : cc Ret.fRet + cc Ret.fRif * N = 0 := by
      simp only [cc, show rowNat tr 14 r Ret.fRet = 0 from eR, show rowNat tr 14 r Ret.fRif = 1 from eI, eN]; grind
    have hout : rowOut Ret.table tr pub 14 r = stMsg (X.offOf E.k + (pc + 1)) (t + 1) (S + fee) 0 E.sb E.cid := by
      rw [hOut, h0']
      simp only [stMsg, cc, p0, p1, p2, efee', psb, pcid, Lean.Grind.Semiring.natCast_add, List.cons.injEq, and_true]
      refine ⟨by grind, trivial, trivial, by grind, by grind⟩
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, hout, fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    exact (step_returnIf X R hl' hins hfee hg hg64 hcid mC hmC sc).2 (hval.mpr hz)

end WasmBase
