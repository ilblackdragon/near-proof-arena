import WasmBase.Main.Rows
import WasmBase.StepOps2
import WasmBase.Local.Simple
/-!
# Row lemma: STACK (`drop`, `select`)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- A well-formed message re-slotted and re-timed is the encoding of its value. -/
theorem stack_enc_reslot (m : Msg) (hm : m.ok) (sp sl tp : Nat) :
    enc sp sl m.toVal tp = ⟨sp, sl, m.tag, m.l0, m.l1, m.l2, m.l3, tp⟩ := by
  have hm' : (⟨sp, sl, m.tag, m.l0, m.l1, m.l2, m.l3, tp⟩ : Msg).ok := hm
  have e := enc_of_ok hm'
  have ht : (⟨sp, sl, m.tag, m.l0, m.l1, m.l2, m.l3, tp⟩ : Msg).toVal = m.toVal := rfl
  rw [ht] at e
  exact e

theorem stack_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 7) (hact : rowAct Stack.table tr pub 7 r) :
    RowFacts X (rowIn Stack.table tr pub 7 r) (rowOut Stack.table tr pub 7 r)
      (rowCons Stack.table tr pub 7 r) (rowProd Stack.table tr pub 7 r) := by
  have hP' := P_val
  have ht : 7 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 7 r i < P := rowNat_lt tr 7 r
  have hcon : ∀ e ∈ Stack.table.constraints, e.eval (natRow (rowNat tr 7 r) (tr.row pub 7 r)) = 0 :=
    table_constr H ht hr
  have hc' := hcon
  simp only [Stack.table, Stack.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hc'
  obtain ⟨bD, bS, hDS, -⟩ := hc'
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Stack.fDrop, Stack.fSel] at bD bS hDS
  have dD := bool_nat (hcP _) bD
  have dS := bool_nat (hcP _) bS
  have dDS := zero_of_mul_nat (hcP _) (hcP _) hDS
  have a1 : rowNat tr 7 r 5 + rowNat tr 7 r 6 = 1 := by
    have h := hact
    simp only [rowAct, Stack.table, Stack.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      v, Expr.eval_col, Expr.eval_add', Stack.act, cell_cast, Trace.row, Stack.kSb, Stack.kCid, Stack.fDrop, Stack.fSel] at h
    rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)] at h
    exact h
  have hocc : ∀ i ∈ Stack.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 7 r)),
      (i.count.eval (tr.row pub 7 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Stack.table.inters from hi)
  have cntA : (Expr.eval (tr.row pub 7 r) Stack.act).toNat = 1 := by
    simp only [Stack.act, v, Expr.eval_add', Expr.eval_col, Trace.row, cell_cast, Stack.fDrop, Stack.fSel]
    rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]; exact a1
  have cntS : (Expr.eval (tr.row pub 7 r) (v Stack.fSel)).toNat = rowNat tr 7 r 6 := rfl
  have hIn : rowIn Stack.table tr pub 7 r =
      [((rowNat tr 7 r 0 : Nat) : F), ((rowNat tr 7 r 1 : Nat) : F), ((rowNat tr 7 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 7 r 28 : Nat) : F), ((rowNat tr 7 r 29 : Nat) : F)] := by
    simp only [rowIn, Stack.table, Stack.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Stack.kSb, Stack.kCid, cPc, cTs, cS]
  have hOut : rowOut Stack.table tr pub 7 r =
      [((rowNat tr 7 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 7 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 7 r 2 : Nat) : F) + ((rowNat tr 7 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 7 r 28 : Nat) : F), ((rowNat tr 7 r 29 : Nat) : F)] := by
    simp only [rowOut, Stack.table, Stack.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Stack.kSb, Stack.kCid, cPc, cTs, cS, cFee]
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Stack.op (v cH) (v cFee) zeros4 Stack.act)
    (by simp [Stack.inters, stdState])
  simp only [fetch, cntA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hlt := recordOf_op_lt hrc
  rw [hre] at hm hlt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hlt
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, zeros4, v, Expr.eval_col,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cell_cast, Trace.row, Stack.kSb, Stack.kCid, cPc, cH, cFee, Stack.op,
    Stack.fDrop, Stack.fSel, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, -, -, -, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 7 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = 0x1A * rowNat tr 7 r 5 + 0x1B * rowNat tr 7 r 6 := by
    simp only [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add] at eop
    exact (natEq eop (by omega) (by omega)).symm
  -- the time checks of the three possibly-consumed values
  have tchk : ∀ (tp hi : Nat) (cnt : Expr), (Expr.eval (tr.row pub 7 r) cnt).toNat = 1 →
      (timeChk (v cTs) (v tp) (v hi) cnt).all (fun i => Stack.inters.any (fun j => decide (j = i))) = true →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 7 r tp + 1 + n : Nat) : F) = ((rowNat tr 7 r 1 : Nat) : F) := by
    intro tp hi cnt hc hsub'
    have hsub : ∀ i ∈ timeChk (v cTs) (v tp) (v hi) cnt, i ∈ Stack.inters := fun i hi =>
      by obtain ⟨j, hj, e⟩ := List.any_eq_true.mp (List.all_eq_true.mp hsub' i hi)
         rw [← of_decide_eq_true e]; exact hj
    have o1 := hocc _ (hsub (r16 (v cTs - v tp - 1 - B16 * v hi) cnt) (by simp [timeChk]))
    have o2 := hocc _ (hsub (r16 (4 * v hi) cnt) (by simp [timeChk]))
    simp only [r16] at o1 o2
    rw [hc] at o1 o2
    simp only [List.map_cons, List.map_nil, v, Expr.eval_sub', Expr.eval_mul', Expr.eval_col,
      Expr.eval_ofNat', B16, Trace.row, cTs] at o1 o2
    obtain ⟨n, hn, he⟩ := time_chk L o1 o2
    exact ⟨n, hn, by simp only [cell_cast, Fp.toNat_cast_of_lt (hcP _)] at he; exact he⟩
  have tA := tchk Stack.tA Stack.hA Stack.act cntA (by decide)
  have rawCons : rowMsgs Stack.table tr pub 7 r busStk false =
      ([[((0 : Nat) : F), tr.cell 7 r 28 + tr.cell 7 r 3 - ((1 : Nat) : F), tr.cell 7 r 7, tr.cell 7 r 8, tr.cell 7 r 9,
          tr.cell 7 r 10, tr.cell 7 r 11, tr.cell 7 r 12]] ++
       (if rowNat tr 7 r 6 = 1 then
        [[((0 : Nat) : F), tr.cell 7 r 28 + tr.cell 7 r 3 - ((2 : Nat) : F), tr.cell 7 r 14, tr.cell 7 r 15, tr.cell 7 r 16,
          tr.cell 7 r 17, tr.cell 7 r 18, tr.cell 7 r 19],
         [((0 : Nat) : F), tr.cell 7 r 28 + tr.cell 7 r 3 - ((3 : Nat) : F), tr.cell 7 r 14, tr.cell 7 r 21, tr.cell 7 r 22,
          tr.cell 7 r 23, tr.cell 7 r 24, tr.cell 7 r 25]] else [])) := by
    rw [rowMsgs_eq]
    simp only [Stack.table, Stack.inters, stdState, stateIn, stateOut, fetch, stkSend, stkRecv, chSend, chRecv,
      timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
      busStk, busR16]
    simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide,
      show (3 : Nat) = 2 ↔ False by decide, false_and,
      decide_false, Bool.false_eq_true, ite_false, true_and, and_true, decide_true, ite_true, List.filterMap_cons,
      List.filterMap_nil, cntA, cntS]
    by_cases h6 : rowNat tr 7 r 6 = 1 <;>
    simp only [h6, ite_true, ite_false, decide_true, decide_false, Bool.true_eq_false, Bool.false_eq_true,
      List.filterMap_nil, List.filterMap_cons, limbsOf, List.range, List.range.loop, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil, v, Expr.eval_sub', Expr.eval_add', Expr.eval_col,
      Expr.eval_ofNat', Trace.row, cH, Stack.kSb, Stack.tagA, Stack.A, Stack.tA, Stack.tagV, Stack.V2, Stack.t2, Stack.V1,
      Stack.t1, Nat.reduceAdd, Stack.fSel, cntS]
  have rawProd : rowMsgs Stack.table tr pub 7 r busStk true =
      (if rowNat tr 7 r 6 = 1 then
        [[((0 : Nat) : F), tr.cell 7 r 28 + tr.cell 7 r 3 - ((3 : Nat) : F), tr.cell 7 r 14, Expr.eval (tr.row pub 7 r) (Stack.out 0),
          Expr.eval (tr.row pub 7 r) (Stack.out 1), Expr.eval (tr.row pub 7 r) (Stack.out 2),
          Expr.eval (tr.row pub 7 r) (Stack.out 3), tr.cell 7 r 1]] else []) := by
    rw [rowMsgs_eq]
    simp only [Stack.table, Stack.inters, stdState, stateIn, stateOut, fetch, stkSend, stkRecv, chSend, chRecv,
      timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
      busStk, busR16]
    simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide,
      show (3 : Nat) = 2 ↔ False by decide, false_and,
      decide_false, Bool.false_eq_true, ite_false, true_and, and_true, decide_true, ite_true, List.filterMap_cons,
      List.filterMap_nil, cntA, cntS]
    by_cases h6 : rowNat tr 7 r 6 = 1 <;>
    simp only [h6, ite_true, ite_false, decide_true, decide_false, Bool.true_eq_false, Bool.false_eq_true,
      List.filterMap_nil, List.filterMap_cons, List.range, List.range.loop, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil, v, Expr.eval_sub', Expr.eval_add', Expr.eval_col,
      Expr.eval_ofNat', Trace.row, cH, Stack.kSb, cTs, Stack.tagV, Nat.reduceAdd, Stack.fSel, cntS]
  -- common facts
  have hIn1 : lvl (rowIn Stack.table tr pub 7 r) = ((rowNat tr 7 r 1 : Nat) : F) := by rw [hIn]; rfl
  have hgas : gasF (rowOut Stack.table tr pub 7 r) = gasF (rowIn Stack.table tr pub 7 r) + ((fee : Nat) : F) := by
    rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']
  have hts : lvl (rowOut Stack.table tr pub 7 r) = lvl (rowIn Stack.table tr pub 7 r) + 1 := by
    rw [hIn, hOut]; rfl
  have hprodT : ∀ x ∈ rowProd Stack.table tr pub 7 r, x.tp < P ∧ ((x.tp : Nat) : F) = lvl (rowIn Stack.table tr pub 7 r) := by
    intro x hx
    rw [rowProd, rawProd] at hx
    split at hx
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hx
      subst hx
      exact ⟨hcP 1, by rw [hIn1]; rfl⟩
    · simp at hx
  have hprodNd : (rowProd Stack.table tr pub 7 r).Nodup := by
    rw [rowProd, rawProd]; split <;> simp
  -- the spec step: shared prefix
  have spec_pre : ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop)
      (S_seg segb : Nat),
      RelW X E s f tps tpl t pc S live S_seg segb → rowIn Stack.table tr pub 7 r = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      t + 1 < P → S + X.maxFee < P → q = E.k ∧ l = pc ∧ pc0 = X.offOf E.k + pc ∧ rowNat tr 7 r 1 = t ∧
        (∀ k, k ≤ s.stack.size - E.sb → (tr.cell 7 r 28 + tr.cell 7 r 3 - ((k : Nat) : F)).toNat = s.stack.size - k) ∧
        rowOut Stack.table tr pub 7 r = stMsg (X.offOf E.k + (pc + 1)) (t + 1) (S + fee) 0 E.sb E.cid := by
    intro E s f tps tpl t pc S live S_seg segb R hin ht1 hS
    rw [hIn] at hin
    obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
    have hpcl := R.pcLt
    have hoffb := X.off_bound R.kLt
    have htot := X.mf.total
    obtain ⟨ls0, hL0, hfl0⟩ := R.labels
    have p0 : rowNat tr 7 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
    have p1 : rowNat tr 7 r 1 = t := natEq i1 (hcP _) (by omega)
    have p2 : rowNat tr 7 r 2 = S := natEq i2 (hcP _) (by omega)
    have psb : rowNat tr 7 r 28 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
    have pcid : rowNat tr 7 r 29 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
    have hsbR := R.sbLe
    have hpc : pc0 = X.offOf E.k + pc := natEq (e0.symm.trans i0) (by omega) (by omega)
    subst hpc
    obtain ⟨hqk, hlpc⟩ := X.loc_unique hq hl R.kLt hpcl hoff
    subst q
    subst l
    have hH := R.height
    have hHb := CF.hBound pc hpcl
    have eh' := eh
    rw [hH] at eh' hHb
    simp only [Option.getD_some] at eh' hHb
    have p3 : rowNat tr 7 r 3 = s.stack.size - E.sb := natEq eh' (hcP _) (by omega)
    have hszP : s.stack.size < P := by have := R.sbLt; omega
    refine ⟨rfl, rfl, rfl, p1, fun k hk => by rw [cell_cast, cell_cast]; exact slot_toNat psb p3 hsbR hk hszP, ?_⟩
    rw [hOut, p0, p1, p2, efee', psb, pcid, ← Nat.add_assoc]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  have z0 : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by omega)
  rcases (show (rowNat tr 7 r 5 = 1 ∧ rowNat tr 7 r 6 = 0) ∨ (rowNat tr 7 r 5 = 0 ∧ rowNat tr 7 r 6 = 1) by omega)
    with ⟨g5, g6⟩ | ⟨g5, g6⟩
  · -- drop
    have hCons : rowCons Stack.table tr pub 7 r =
        [⟨0, (tr.cell 7 r 28 + tr.cell 7 r 3 - ((1 : Nat) : F)).toNat, rowNat tr 7 r 7, rowNat tr 7 r 8, rowNat tr 7 r 9,
          rowNat tr 7 r 10, rowNat tr 7 r 11, rowNat tr 7 r 12⟩] := by
      rw [rowCons, rawCons, if_neg (by omega : ¬ rowNat tr 7 r 6 = 1)]
      simp only [List.append_nil, List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, z0]
      rfl
    have hProd : rowProd Stack.table tr pub 7 r = [] := by
      rw [rowProd, rawProd, if_neg (by omega : ¬ rowNat tr 7 r 6 = 1)]; rfl
    refine ⟨?_, by rw [hIn]; rfl, hts, ⟨fee, hfl, hgas⟩, ?_, hprodT, hprodNd⟩
    rotate_left
    · rw [hCons, hIn1]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact tA
    intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
    obtain ⟨hqk, hlpc, hpc, p1, slot, hout⟩ := spec_pre E s f tps tpl t pc S live S_seg segb R hin ht1 hS
    subst q
    subst l
    obtain ⟨ls0, hL0, -⟩ := R.labels
    subst hpc
    have hop' : op = 0x1A := by rw [hop, g5, g6]
    have hdrop : ins = .drop := by
      rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h1, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
        ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
      all_goals first
        | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
        | (exfalso; omega)
        | exact h1
        | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
        | (exfalso; simp only [opCall] at h; omega)
        | (exfalso; rw [hop'] at hf; revert hf; decide)
    subst hdrop
    obtain ⟨h1, -, -, -⟩ := verify_straight X R.kLt R.pcLt hins hL0 R.height (pops := 1) (pushes := 0) rfl
      (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
    rw [hCons, hProd] at *
    have hma := hlive _ (List.mem_singleton_self _)
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, hout, fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    exact step_drop X R hins hfee hg hg64 _ hma ⟨rfl, slot 1 h1⟩
  · -- select
    have hCons : rowCons Stack.table tr pub 7 r =
        [⟨0, (tr.cell 7 r 28 + tr.cell 7 r 3 - ((1 : Nat) : F)).toNat, rowNat tr 7 r 7, rowNat tr 7 r 8, rowNat tr 7 r 9,
          rowNat tr 7 r 10, rowNat tr 7 r 11, rowNat tr 7 r 12⟩,
         ⟨0, (tr.cell 7 r 28 + tr.cell 7 r 3 - ((2 : Nat) : F)).toNat, rowNat tr 7 r 14, rowNat tr 7 r 15, rowNat tr 7 r 16,
          rowNat tr 7 r 17, rowNat tr 7 r 18, rowNat tr 7 r 19⟩,
         ⟨0, (tr.cell 7 r 28 + tr.cell 7 r 3 - ((3 : Nat) : F)).toNat, rowNat tr 7 r 14, rowNat tr 7 r 21, rowNat tr 7 r 22,
          rowNat tr 7 r 23, rowNat tr 7 r 24, rowNat tr 7 r 25⟩] := by
      rw [rowCons, rawCons, if_pos g6]
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, decMsg, List.getD_cons_zero,
        List.getD_cons_succ, z0]
      rfl
    have hProd : rowProd Stack.table tr pub 7 r =
        [⟨0, (tr.cell 7 r 28 + tr.cell 7 r 3 - ((3 : Nat) : F)).toNat, rowNat tr 7 r 14,
          (Expr.eval (tr.row pub 7 r) (Stack.out 0)).toNat, (Expr.eval (tr.row pub 7 r) (Stack.out 1)).toNat,
          (Expr.eval (tr.row pub 7 r) (Stack.out 2)).toNat, (Expr.eval (tr.row pub 7 r) (Stack.out 3)).toNat,
          rowNat tr 7 r 1⟩] := by
      rw [rowProd, rawProd, if_pos g6]
      simp only [List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, z0]
      rfl
    have cS1 : (Expr.eval (tr.row pub 7 r) (v Stack.fSel)).toNat = 1 := by rw [cntS, g6]
    have t2 := tchk Stack.t2 Stack.h2 (v Stack.fSel) cS1 (by decide)
    have t1 := tchk Stack.t1 Stack.h1 (v Stack.fSel) cS1 (by decide)
    refine ⟨?_, by rw [hIn]; rfl, hts, ⟨fee, hfl, hgas⟩, ?_, hprodT, hprodNd⟩
    rotate_left
    · rw [hCons, hIn1]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨tA, t2, t1⟩
    intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
    obtain ⟨hqk, hlpc, hpc, p1, slot, hout⟩ := spec_pre E s f tps tpl t pc S live S_seg segb R hin ht1 hS
    subst q
    subst l
    obtain ⟨ls0, hL0, -⟩ := R.labels
    subst hpc
    have hop' : op = 0x1B := by rw [hop, g5, g6]
    obtain ⟨ty, hsel⟩ : ∃ ty, ins = .select ty := by
      rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨ty, h1, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
        ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
      all_goals first
        | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
        | (exfalso; omega)
        | exact ⟨ty, h1⟩
        | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
        | (exfalso; simp only [opCall] at h; omega)
        | (exfalso; rw [hop'] at hf; revert hf; decide)
    subst hsel
    obtain ⟨h3, -, -, -⟩ := verify_straight X R.kLt R.pcLt hins hL0 R.height (pops := 3) (pushes := 1)
      (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
    rw [hCons, hProd] at *
    have hmc := hlive _ (List.mem_cons_self)
    have hm2 := hlive _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hm1 := hlive _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, hout, fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    refine step_select X R hins hfee hg hg64 _ _ _ _ hmc hm2 hm1 ⟨rfl, slot 1 (by omega)⟩
      ⟨rfl, slot 2 (by omega)⟩ ⟨rfl, slot 3 h3⟩ ?_
    intro okc ok1 ok2
    obtain ⟨l0, l1, -, -, -⟩ := okc
    have SS := stack_sound (rowNat tr 7 r) (tr.row pub 7 r) hcP hcon ⟨l0, l1⟩
    obtain ⟨-, -, -, -, -, hsA, -, hout'⟩ := SS
    obtain ⟨-, zA2, zA3⟩ := hsA g6
    have ho : ∀ i, (Expr.eval (tr.row pub 7 r) (Stack.out i)).toNat =
        if rowNat tr 7 r 8 + rowNat tr 7 r 9 = 0 then rowNat tr 7 r (15 + i) else rowNat tr 7 r (21 + i) := by
      intro i
      rw [row_eq_natRow, hout' i]
      by_cases hz : rowNat tr 7 r 8 + rowNat tr 7 r 9 = 0 <;>
        simp only [Stack.A, Stack.V1, Stack.V2, Nat.reduceAdd, hz, ite_true, ite_false] <;>
        exact Fp.toNat_cast_of_lt (hcP _)
    simp only [ho, Nat.reduceAdd]
    have hval : (⟨0, (tr.cell 7 r 28 + tr.cell 7 r 3 - ((1 : Nat) : F)).toNat, rowNat tr 7 r 7, rowNat tr 7 r 8, rowNat tr 7 r 9,
        rowNat tr 7 r 10, rowNat tr 7 r 11, rowNat tr 7 r 12⟩ : Msg).val = 0 ↔
        rowNat tr 7 r 8 + rowNat tr 7 r 9 = 0 := by
      simp only [Msg.val, val4]
      simp only [Stack.A, Nat.reduceAdd] at zA2 zA3
      rw [zA2, zA3]; omega
    by_cases hz : rowNat tr 7 r 8 + rowNat tr 7 r 9 = 0
    · rw [if_pos (hval.mpr hz), stack_enc_reslot _ ok2, slot 3 h3, p1]
      simp only [hz, ite_true]
    · rw [if_neg (fun h => hz (hval.mp h)), stack_enc_reslot _ ok1, slot 3 h3, p1]
      simp only [hz, ite_false]

end WasmBase

namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

theorem stack_count_cases (i : Inter) (hi : i ∈ Stack.inters) : i.count = Stack.act ∨ i.count = v Stack.fSel := by
  have := List.all_eq_true.mp
    (show Stack.inters.all (fun i => decide (i.count = Stack.act) || decide (i.count = v Stack.fSel)) = true by decide) i hi
  simpa using this

theorem stack_flags_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Stack.table.constraints, e.eval (natRow (rowNat tr 7 r) (tr.row pub 7 r)) = 0) :
    rowNat tr 7 r 5 + rowNat tr 7 r 6 ≤ 1 := by
  simp only [Stack.table, Stack.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hcon
  obtain ⟨bD, bS, hDS, -⟩ := hcon
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Stack.fDrop, Stack.fSel] at bD bS hDS
  have := bool_nat (rowNat_lt _ _ _ _) bD
  have := bool_nat (rowNat_lt _ _ _ _) bS
  have := zero_of_mul_nat (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _) hDS
  omega

theorem stack_flags {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 7) :
    rowNat tr 7 r 5 + rowNat tr 7 r 6 ≤ 1 :=
  stack_flags_of (table_constr H (by simp [air_len]) hr)

theorem stack_act_eval (pub : List F) (tr : Trace) (r : Nat) (h : rowNat tr 7 r 5 + rowNat tr 7 r 6 ≤ 1) :
    (Stack.act.eval (tr.row pub 7 r)).toNat = rowNat tr 7 r 5 + rowNat tr 7 r 6 := by
  have hP' := P_val
  simp only [Stack.act, v, Expr.eval_add', Expr.eval_col, Trace.row, cell_cast, Stack.fDrop, Stack.fSel]
  rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]

theorem stack_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Stack.table.constraints, e.eval (natRow (rowNat tr 7 r) (tr.row pub 7 r)) = 0) :
    ∀ i ∈ Stack.inters, (i.count.eval (tr.row pub 7 r)).toNat ≤ 1 := by
  have hf := stack_flags_of hcon
  intro i hi
  rcases stack_count_cases i hi with hc | hc <;> rw [hc]
  · rw [stack_act_eval pub tr r hf]; exact hf
  · show rowNat tr 7 r 6 ≤ 1; omega

theorem stack_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 7) :
    ∀ i ∈ Stack.inters, (i.count.eval (tr.row pub 7 r)).toNat ≤ 1 :=
  stack_counts_of (table_constr H (by simp [air_len]) hr)

theorem stack_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 7)
    (hna : ¬ rowAct Stack.table tr pub 7 r) :
    ∀ i ∈ Stack.inters, (i.count.eval (tr.row pub 7 r)).toNat ≠ 1 := by
  have hf := stack_flags H hr
  have ha : rowNat tr 7 r 5 + rowNat tr 7 r 6 ≠ 1 := by
    intro h; apply hna
    simp only [rowAct, Stack.table, Stack.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero]
    rw [stack_act_eval pub tr r hf]; exact h
  intro i hi
  rcases stack_count_cases i hi with hc | hc <;> rw [hc]
  · rw [stack_act_eval pub tr r hf]; exact ha
  · show rowNat tr 7 r 6 ≠ 1; omega

end WasmBase
