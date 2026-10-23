import WasmBase.Main.Rows
import WasmBase.StepOps
import WasmBase.StepOps2
import WasmBase.Local.Add
/-!
# Row lemma: ADD (`i32/i64.add`, `i32/i64.sub`)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- Flags of an ADD row: bits, mutually exclusive.

Stated against the row's own constraint vanishing (`hcon`) rather than `Holds` of a fixed AIR: that is
all the proof uses, and it lets the same lemma serve `wasmBaseAir`, `wasmBaseHostAir` and
`wasmBaseRegAir`, whose table 1 is the same `Add.table`.  `add_flags` below is the `Holds` wrapper. -/
theorem add_flags_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Add.table.constraints, e.eval (natRow (rowNat tr 1 r) (tr.row pub 1 r)) = 0) :
    (rowNat tr 1 r 5 = 0 ∨ rowNat tr 1 r 5 = 1) ∧ (rowNat tr 1 r 6 = 0 ∨ rowNat tr 1 r 6 = 1) ∧
      rowNat tr 1 r 5 + rowNat tr 1 r 6 ≤ 1 ∧ (rowNat tr 1 r 7 = 0 ∨ rowNat tr 1 r 7 = 1) := by
  simp only [Add.table, Add.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hcon
  obtain ⟨bA, bS, b64, hAS, -⟩ := hcon
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Add.fAdd, Add.fSub, Add.is64] at bA bS hAS b64
  have h5 := bool_nat (rowNat_lt _ _ _ _) bA
  have h6 := bool_nat (rowNat_lt _ _ _ _) bS
  have := zero_of_mul_nat (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _) hAS
  exact ⟨h5, h6, by omega, bool_nat (rowNat_lt _ _ _ _) b64⟩

theorem add_flags {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 1) :
    (rowNat tr 1 r 5 = 0 ∨ rowNat tr 1 r 5 = 1) ∧ (rowNat tr 1 r 6 = 0 ∨ rowNat tr 1 r 6 = 1) ∧
      rowNat tr 1 r 5 + rowNat tr 1 r 6 ≤ 1 ∧ (rowNat tr 1 r 7 = 0 ∨ rowNat tr 1 r 7 = 1) :=
  add_flags_of (table_constr H (by simp [air_len]) hr)

theorem add_count_eq {i : Inter} (hi : i ∈ Add.inters) : i.count = Add.act :=
  of_decide_eq_true (List.all_eq_true.mp
    (show Add.inters.all (fun i => decide (i.count = Add.act)) = true by decide) i hi)

theorem add_act_eval (tr : Trace) (pub : List F) (r : Nat) :
    (Add.act.eval (tr.row pub 1 r)).toNat = (rowNat tr 1 r 5 + rowNat tr 1 r 6) % P := by
  simp only [Add.act, v, Expr.eval_add', Expr.eval_col, Trace.row, Add.fAdd, Add.fSub]
  rw [cell_cast, cell_cast, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast]

theorem add_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Add.table.constraints, e.eval (natRow (rowNat tr 1 r) (tr.row pub 1 r)) = 0) :
    ∀ i ∈ Add.inters, (i.count.eval (tr.row pub 1 r)).toNat ≤ 1 := by
  have hP' := P_val
  obtain ⟨-, -, hs, -⟩ := add_flags_of hcon
  intro i hi
  rw [add_count_eq hi, add_act_eval, Nat.mod_eq_of_lt (by omega)]; exact hs

theorem add_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 1) :
    ∀ i ∈ Add.inters, (i.count.eval (tr.row pub 1 r)).toNat ≤ 1 :=
  add_counts_of (table_constr H (by simp [air_len]) hr)

theorem add_inactive {pub : List F} {tr : Trace} {r : Nat}
    (hna : ¬ rowAct Add.table tr pub 1 r) :
    ∀ i ∈ Add.inters, (i.count.eval (tr.row pub 1 r)).toNat ≠ 1 := by
  intro i hi
  rw [add_count_eq hi]
  simpa [rowAct, Add.table, Add.inters, stdState, stateIn] using hna

theorem add_rnToNat (tr : Trace) (t r i : Nat) : (((rowNat tr t r i : Nat) : F)).toNat = rowNat tr t r i :=
  Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)

theorem add_zeroToNat : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by rw [P_val]; omega)

theorem add_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 1) (hact : rowAct Add.table tr pub 1 r) :
    RowFacts X (rowIn Add.table tr pub 1 r) (rowOut Add.table tr pub 1 r)
      (rowCons Add.table tr pub 1 r) (rowProd Add.table tr pub 1 r) := by
  have hP' := P_val
  have ht : 1 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 1 r i < P := rowNat_lt tr 1 r
  have hcon : ∀ e ∈ Add.constraints, e.eval (natRow (rowNat tr 1 r) (tr.row pub 1 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨f5, f6, f56, f7⟩ := add_flags H hr
  have cnt : (Add.act.eval (tr.row pub 1 r)).toNat = 1 := by
    simpa only [rowAct, Add.table, Add.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero] using hact
  have a56 : rowNat tr 1 r 5 + rowNat tr 1 r 6 = 1 := by
    rw [add_act_eval, Nat.mod_eq_of_lt (by omega)] at cnt; exact cnt
  have hocc : ∀ i ∈ Add.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 1 r)),
      (i.count.eval (tr.row pub 1 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Add.table.inters from hi)
  -- messages
  have hIn : rowIn Add.table tr pub 1 r =
      [((rowNat tr 1 r 0 : Nat) : F), ((rowNat tr 1 r 1 : Nat) : F), ((rowNat tr 1 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 1 r 28 : Nat) : F), ((rowNat tr 1 r 29 : Nat) : F)] := by
    simp only [rowIn, Add.table, Add.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cTs, cS,
      Add.kSb, Add.kCid]
  have hOut : rowOut Add.table tr pub 1 r =
      [((rowNat tr 1 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 1 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 1 r 2 : Nat) : F) + ((rowNat tr 1 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 1 r 28 : Nat) : F), ((rowNat tr 1 r 29 : Nat) : F)] := by
    simp only [rowOut, Add.table, Add.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, cPc, cTs, cS, cFee, Add.kSb, Add.kCid]
  have hCons : rowCons Add.table tr pub 1 r =
      [⟨0, (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 1 r 7, rowNat tr 1 r 8,
          rowNat tr 1 r 9, rowNat tr 1 r 10, rowNat tr 1 r 11, rowNat tr 1 r 12⟩,
        ⟨0, (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 1 r 7, rowNat tr 1 r 14,
          rowNat tr 1 r 15, rowNat tr 1 r 16, rowNat tr 1 r 17, rowNat tr 1 r 18⟩] := by
    rw [rowCons, rowMsgs_eq, show Add.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
      [stkRecv (v Add.kSb + v cH - 2) (v Add.is64) (limbsOf Add.a) (v Add.ta) Add.act,
       stkRecv (v Add.kSb + v cH - 1) (v Add.is64) (limbsOf Add.b) (v Add.tb) Add.act] by decide]
    simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, cnt, ite_true]
    simp only [List.map_cons, List.map_nil, limbsOf, List.range, List.range.loop, List.cons_append,
      List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', cell_cast, Trace.row, cH, Add.kSb, Add.is64,
      Add.a, Add.ta, Add.b, Add.tb, Nat.reduceAdd, decMsg, List.getD_cons_zero, List.getD_cons_succ,
      add_rnToNat, add_zeroToNat]
  have hProd : rowProd Add.table tr pub 1 r =
      [⟨0, (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 1 r 7, rowNat tr 1 r 20,
          rowNat tr 1 r 21, rowNat tr 1 r 22, rowNat tr 1 r 23, rowNat tr 1 r 1⟩] := by
    rw [rowProd, rowMsgs_eq, show Add.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
      [stkSend (v Add.kSb + v cH - 2) (v Add.is64) (limbsOf Add.r) (v cTs) Add.act] by decide]
    simp only [List.filterMap_cons, List.filterMap_nil, stkSend, chSend, cnt, ite_true]
    simp only [List.map_cons, List.map_nil, limbsOf, List.range, List.range.loop, List.cons_append,
      List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', cell_cast, Trace.row, cH, Add.kSb, cTs, Add.is64,
      Add.r, Nat.reduceAdd, decMsg, List.getD_cons_zero, List.getD_cons_succ, add_rnToNat, add_zeroToNat]
  -- time checks of the consumed values
  have tA := hocc _ (show r16 (v cTs - v Add.ta - 1 - B16 * v Add.ha) Add.act ∈ Add.inters by simp [Add.inters, timeChk])
  have tA' := hocc _ (show r16 (4 * v Add.ha) Add.act ∈ Add.inters by simp [Add.inters, timeChk])
  have tB := hocc _ (show r16 (v cTs - v Add.tb - 1 - B16 * v Add.hb) Add.act ∈ Add.inters by simp [Add.inters, timeChk])
  have tB' := hocc _ (show r16 (4 * v Add.hb) Add.act ∈ Add.inters by simp [Add.inters, timeChk])
  simp only [r16, cnt] at tA tA' tB tB'
  simp only [List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_sub', Expr.eval_mul',
    Expr.eval_ofNat', B16, cell_cast, Trace.row, cTs, Add.ta, Add.ha, Add.tb, Add.hb] at tA tA' tB tB'
  obtain ⟨nA, hnA, eA⟩ := time_chk L tA tA'
  obtain ⟨nB, hnB, eB⟩ := time_chk L tB tB'
  rw [add_rnToNat] at eA eB
  -- result limbs are 16-bit
  have hR16 : ∀ i, i < 4 → rowNat tr 1 r (20 + i) < 65536 := by
    intro i hi
    have h := hocc _ (show r16 (v (Add.r + i)) Add.act ∈ Add.inters by
      unfold Add.inters; exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [r16, cnt] at h
    simp only [List.map_cons, List.map_nil, v, Expr.eval_col, cell_cast, Trace.row, Add.r] at h
    obtain ⟨x, hx, hxl⟩ := L.r16 _ h rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hx
    rw [← hx, add_rnToNat] at hxl
    exact hxl
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Add.op (v cH) (v cFee) zeros4 Add.act) (by simp [Add.inters, stdState])
  simp only [fetch, cnt] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hlt := recordOf_op_lt hrc
  rw [hre] at hm hlt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hlt
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, zeros4, v, Expr.eval_col,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cell_cast, Trace.row, cPc, cH, cFee, Add.op, Add.is64,
    Add.fSub, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 1 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = 0x6A + 18 * rowNat tr 1 r 7 + rowNat tr 1 r 6 := by
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
  have p0 : rowNat tr 1 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 1 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 1 r 2 = S := natEq i2 (hcP _) (by omega)
  have p28 : rowNat tr 1 r 28 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have p29 : rowNat tr 1 r 29 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
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
  have p3 : rowNat tr 1 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  have hout : rowOut Add.table tr pub 1 r = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', p28, p29]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hCons, hProd] at *
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  -- the instruction is `.num op` with op a binop
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
  have hbin : isBinop op := by
    rw [hop]; rcases f6 with g6 | g6 <;> rcases f7 with g7 | g7 <;> rw [g6, g7] <;> simp [isBinop, binops]
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hbin
  obtain ⟨ls0, hL0, -⟩ := R.labels
  have hk : kindOf ls0 (.num op) = some (.straight 2 1) := by simp [kindOf, hfam, hpops]
  obtain ⟨h2, -⟩ := verify_straight X R.kLt hpcl hins hL0 R.height hk (by intro bt; simp) (by simp)
    (by simp) (by simp) (by intro l; simp) (by intro l; simp)
  have sl2 : (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat = s.stack.size - 2 :=
    slot_toNat p28 p3 hsbR h2 hszP
  have sl1 : (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat = s.stack.size - 1 :=
    slot_toNat p28 p3 hsbR (by omega) hszP
  have hwk : opW op = 32 + 32 * rowNat tr 1 r 7 ∧ opK op = rowNat tr 1 r 6 := by
    rw [hop]; rcases f6 with g6 | g6 <;> rcases f7 with g7 | g7 <;> rw [g6, g7] <;> simp [opW, opK]
  obtain ⟨s', hs', hrel⟩ := step_binop X R hins hbin hfee hg hg64
    ⟨0, (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 1 r 7, rowNat tr 1 r 8,
          rowNat tr 1 r 9, rowNat tr 1 r 10, rowNat tr 1 r 11, rowNat tr 1 r 12⟩
    ⟨0, (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 1 r 7, rowNat tr 1 r 14,
          rowNat tr 1 r 15, rowNat tr 1 r 16, rowNat tr 1 r 17, rowNat tr 1 r 18⟩
    ⟨0, (((rowNat tr 1 r 28 : Nat) : F) + ((rowNat tr 1 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 1 r 7, rowNat tr 1 r 20,
          rowNat tr 1 r 21, rowNat tr 1 r 22, rowNat tr 1 r 23, rowNat tr 1 r 1⟩
    (hlive _ (by simp)) (hlive _ (by simp)) ⟨rfl, sl2⟩ ⟨rfl, sl1⟩
    ⟨rfl, sl2, p1, by rw [hwk.1]; rcases f7 with g7 | g7 <;> rw [g7] <;> rfl⟩
    (by
      intro oka okb
      simp only [Msg.ok] at oka okb
      obtain ⟨a0, a1, a2, a3, -⟩ := oka
      obtain ⟨b0, b1, b2, b3, -⟩ := okb
      have ha : ∀ i, i < 4 → rowNat tr 1 r (Add.a + i) < 65536 := by
        intro i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> (simp only [Add.a, Nat.reduceAdd]; assumption)
      have hb : ∀ i, i < 4 → rowNat tr 1 r (Add.b + i) < 65536 := by
        intro i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> (simp only [Add.b, Nat.reduceAdd]; assumption)
      have hr' : ∀ i, i < 4 → rowNat tr 1 r (Add.r + i) < 65536 := fun i hi => hR16 i hi
      obtain ⟨-, hup, hsem⟩ := add_sound (rowNat tr 1 r) (tr.row pub 1 r) hcP hcon a56 ha hb hr'
      simp only [Add.a, Add.b, Add.r, Add.is64, Add.fSub, Nat.reduceAdd] at hup hsem
      have r0 := hR16 0 (by omega); have r1 := hR16 1 (by omega)
      have r2 := hR16 2 (by omega); have r3 := hR16 3 (by omega)
      simp only [Nat.reduceAdd] at r0 r1 r2 r3
      refine ⟨⟨r0, r1, r2, r3, ?_⟩, ?_⟩
      · rcases f7 with g7 | g7
        · exact Or.inl ⟨g7, (hup g7).2.2.2.2.1, (hup g7).2.2.2.2.2⟩
        · exact Or.inr g7
      · simp only [Msg.val]; rw [hwk.1, hwk.2]; exact hsem)
  exact ⟨s', hs', hrel⟩

end WasmBase
