import WasmBase.Main.Rows
import WasmBase.StepCtrl
import WasmBase.StepOps2
import WasmBase.StepMem
import WasmBase.Local.Simple
/-!
# Row lemma: LOCAL (`local.get`, `local.set`, `local.tee`, `global.get`, `global.set`)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- Re-encoding a well-formed message's value with new coordinates keeps its tag and limbs. -/
theorem local_enc {m : Msg} (hm : m.ok) (sp sl tp : Nat) :
    enc sp sl m.toVal tp = ⟨sp, sl, m.tag, m.l0, m.l1, m.l2, m.l3, tp⟩ :=
  enc_of_ok (m := ⟨sp, sl, m.tag, m.l0, m.l1, m.l2, m.l3, tp⟩) hm

theorem local_filterC :
    Local.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)) =
      [chRecv Local.space (v Local.idx) (v Local.tagL) (limbsOf Local.L) (v Local.tL) Local.act,
       stkRecv (v Local.kSb + v cH - 1) (v Local.tagV) (limbsOf Local.V) (v Local.tV) Local.wr] := by decide

theorem local_filterP :
    Local.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) =
      [chSend Local.space (v Local.idx) Local.newTag ((List.range 4).map Local.newVal) (v cTs) Local.act,
       stkSend (v Local.kSb + v cH - 1 + Local.rd) Local.newTag ((List.range 4).map Local.newVal) (v cTs)
         (v Local.fGet + v Local.fTee + v Local.fGGet)] := by decide

set_option maxHeartbeats 4000000 in
theorem local_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 9) (hact : rowAct Local.table tr pub 9 r) :
    RowFacts X (rowIn Local.table tr pub 9 r) (rowOut Local.table tr pub 9 r)
      (rowCons Local.table tr pub 9 r) (rowProd Local.table tr pub 9 r) := by
  have hP' := P_val
  have ht : 9 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 9 r i < P := rowNat_lt tr 9 r
  have hcon : ∀ e ∈ Local.table.constraints, e.eval (natRow (rowNat tr 9 r) (tr.row pub 9 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨bG, bS, bT, bGG, bGS, hsum, bL, bV, zL, zV, hne⟩ := local_sound (rowNat tr 9 r) (tr.row pub 9 r) hcP hcon
  replace bG : rowNat tr 9 r 5 = 0 ∨ rowNat tr 9 r 5 = 1 := bG
  replace bS : rowNat tr 9 r 6 = 0 ∨ rowNat tr 9 r 6 = 1 := bS
  replace bT : rowNat tr 9 r 7 = 0 ∨ rowNat tr 9 r 7 = 1 := bT
  replace bGG : rowNat tr 9 r 26 = 0 ∨ rowNat tr 9 r 26 = 1 := bGG
  replace bGS : rowNat tr 9 r 27 = 0 ∨ rowNat tr 9 r 27 = 1 := bGS
  replace hsum : rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 ≤ 1 := hsum
  replace bL : rowNat tr 9 r 9 = 0 ∨ rowNat tr 9 r 9 = 1 := bL
  replace bV : rowNat tr 9 r 16 = 0 ∨ rowNat tr 9 r 16 = 1 := bV
  replace zL : rowNat tr 9 r 9 = 0 → rowNat tr 9 r 12 = 0 ∧ rowNat tr 9 r 13 = 0 := zL
  replace zV : rowNat tr 9 r 16 = 0 → rowNat tr 9 r 19 = 0 ∧ rowNat tr 9 r 20 = 0 := zV
  have hcs : ∀ a b : Nat, a + b ≤ 3 → (((a : Nat) : F) + ((b : Nat) : F)).toNat = a + b := by
    intro a b hab; rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]
  have hc3 : ∀ a b c : Nat, a + b + c ≤ 3 →
      (((a : Nat) : F) + ((b : Nat) : F) + ((c : Nat) : F)).toNat = a + b + c := by
    intro a b c h
    rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]
  have cntA0 : (Local.act.eval (tr.row pub 9 r)).toNat =
      rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 := by
    show (tr.cell 9 r 5 + tr.cell 9 r 6 + tr.cell 9 r 7 + tr.cell 9 r 26 + tr.cell 9 r 27).toNat = _
    rw [cell_cast, cell_cast, cell_cast, cell_cast, cell_cast]
    simp only [← Lean.Grind.Semiring.natCast_add]; exact Fp.toNat_cast_of_lt (by omega)
  have a1 : rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 = 1 :=
    cntA0.symm.trans hact
  have hocc : ∀ i ∈ Local.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 9 r)),
      (i.count.eval (tr.row pub 9 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Local.table.inters from hi)
  have cntA : (Local.act.eval (tr.row pub 9 r)).toNat = 1 := hact
  have cntW : (Local.wr.eval (tr.row pub 9 r)).toNat = rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 27 := by
    show (tr.cell 9 r 6 + tr.cell 9 r 7 + tr.cell 9 r 27).toNat = _
    rw [cell_cast, cell_cast, cell_cast]; exact hc3 _ _ _ (by omega)
  have cntS : ((v Local.fGet + v Local.fTee + v Local.fGGet).eval (tr.row pub 9 r)).toNat =
      rowNat tr 9 r 5 + rowNat tr 9 r 7 + rowNat tr 9 r 26 := by
    show (tr.cell 9 r 5 + tr.cell 9 r 7 + tr.cell 9 r 26).toNat = _
    rw [cell_cast, cell_cast, cell_cast]; exact hc3 _ _ _ (by omega)
  -- Nat values of the new tag / limbs
  -- the flag pattern: exactly one op
  have hcases : (rowNat tr 9 r 5 = 1 ∧ rowNat tr 9 r 6 = 0 ∧ rowNat tr 9 r 7 = 0 ∧ rowNat tr 9 r 26 = 0 ∧ rowNat tr 9 r 27 = 0) ∨
      (rowNat tr 9 r 5 = 0 ∧ rowNat tr 9 r 6 = 1 ∧ rowNat tr 9 r 7 = 0 ∧ rowNat tr 9 r 26 = 0 ∧ rowNat tr 9 r 27 = 0) ∨
      (rowNat tr 9 r 5 = 0 ∧ rowNat tr 9 r 6 = 0 ∧ rowNat tr 9 r 7 = 1 ∧ rowNat tr 9 r 26 = 0 ∧ rowNat tr 9 r 27 = 0) ∨
      (rowNat tr 9 r 5 = 0 ∧ rowNat tr 9 r 6 = 0 ∧ rowNat tr 9 r 7 = 0 ∧ rowNat tr 9 r 26 = 1 ∧ rowNat tr 9 r 27 = 0) ∨
      (rowNat tr 9 r 5 = 0 ∧ rowNat tr 9 r 6 = 0 ∧ rowNat tr 9 r 7 = 0 ∧ rowNat tr 9 r 26 = 0 ∧ rowNat tr 9 r 27 = 1) := by
    omega
  have hNT : Local.newTag.eval (tr.row pub 9 r) =
      (((if rowNat tr 9 r 5 + rowNat tr 9 r 26 = 1 then rowNat tr 9 r 9 else rowNat tr 9 r 16) : Nat) : F) := by
    show (tr.cell 9 r 5 + tr.cell 9 r 26) * tr.cell 9 r 9 + (tr.cell 9 r 6 + tr.cell 9 r 7 + tr.cell 9 r 27) *
      tr.cell 9 r 16 = _
    simp only [cell_cast]
    rcases hcases with ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ |
      ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ <;> simp only [g5, g6, g7, g26, g27] <;> simp <;> grind
  have hNV : ∀ i, (Local.newVal i).eval (tr.row pub 9 r) =
      (((if rowNat tr 9 r 5 + rowNat tr 9 r 26 = 1 then rowNat tr 9 r (10 + i) else rowNat tr 9 r (17 + i)) : Nat) : F) := by
    intro i
    show (tr.cell 9 r 5 + tr.cell 9 r 26) * tr.cell 9 r (10 + i) + (tr.cell 9 r 6 + tr.cell 9 r 7 + tr.cell 9 r 27) *
      tr.cell 9 r (17 + i) = _
    simp only [cell_cast]
    rcases hcases with ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ |
      ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ <;> simp only [g5, g6, g7, g26, g27] <;> simp <;> grind
  have hIn : rowIn Local.table tr pub 9 r =
      [((rowNat tr 9 r 0 : Nat) : F), ((rowNat tr 9 r 1 : Nat) : F), ((rowNat tr 9 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 9 r 23 : Nat) : F), ((rowNat tr 9 r 24 : Nat) : F)] := by
    simp only [rowIn, Local.table, Local.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Local.kSb, Local.kCid, cPc, cTs, cS]
  have hOut : rowOut Local.table tr pub 9 r =
      [((rowNat tr 9 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 9 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 9 r 2 : Nat) : F) + ((rowNat tr 9 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 9 r 23 : Nat) : F), ((rowNat tr 9 r 24 : Nat) : F)] := by
    simp only [rowOut, Local.table, Local.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Local.kSb, Local.kCid, cPc, cTs, cS, cFee]
  -- the consumed and produced messages
  let c := rowNat tr 9 r
  let NT := if c 5 + c 26 = 1 then c 9 else c 16
  let NV := fun i => if c 5 + c 26 = 1 then c (10 + i) else c (17 + i)
  let spN := (Local.space.eval (tr.row pub 9 r)).toNat
  have hNTl : NT < P := by simp only [NT]; split <;> exact hcP _
  have hNVl : ∀ i, NV i < P := fun i => by simp only [NV]; split <;> exact hcP _
  let mL : Msg := ⟨spN, c 8, c 9, c 10, c 11, c 12, c 13, c 14⟩
  let mV : Msg := ⟨0, (((c 23 : Nat) : F) + ((c 3 : Nat) : F) - ((1 : Nat) : F)).toNat, c 16, c 17, c 18, c 19, c 20, c 21⟩
  let mo : Msg := ⟨spN, c 8, NT, NV 0, NV 1, NV 2, NV 3, c 1⟩
  let ms : Msg := ⟨0, (((c 23 : Nat) : F) + ((c 3 : Nat) : F) - ((1 : Nat) : F) + (((c 5 : Nat) : F) +
    ((c 26 : Nat) : F))).toNat, NT, NV 0, NV 1, NV 2, NV 3, c 1⟩
  have hCons : rowCons Local.table tr pub 9 r = mL :: (if c 6 + c 7 + c 27 = 1 then [mV] else []) := by
    rw [rowCons, rowMsgs_eq]
    show (List.filterMap _ (Local.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)))).map decMsg = _
    rw [local_filterC]
    simp only [List.filterMap_cons, List.filterMap_nil, chRecv, stkRecv, cntA, cntW, ite_true]
    have eL : decMsg ([Local.space, v Local.idx, v Local.tagL] ++ limbsOf Local.L ++ [v Local.tL] |>.map (·.eval (tr.row pub 9 r))) = mL := by
      simp only [limbsOf, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, decMsg, List.getD_cons_zero, List.getD_cons_succ]
      simp only [v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Local.idx, Local.tagL, Local.L, Local.tL,
        Nat.reduceAdd, Fp.toNat_cast_of_lt (hcP _), mL, c, spN]
    by_cases hw : rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 27 = 1
    · simp only [hw, ite_true, List.filterMap_cons, List.map_cons, List.map_nil, eL, List.cons.injEq, true_and, c]
      simp only [limbsOf, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', cell_cast, Trace.row, Local.kSb, Local.kCid, Local.tagV,
        Local.V, Local.tV, cH, Nat.reduceAdd, decMsg, List.getD_cons_zero, List.getD_cons_succ,
        Fp.toNat_cast_of_lt (hcP _), mV, c]
      exact ⟨rfl, trivial⟩
    · simp only [hw, ite_false, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil, eL, c]
  have hProd : rowProd Local.table tr pub 9 r = mo :: (if c 5 + c 7 + c 26 = 1 then [ms] else []) := by
    rw [rowProd, rowMsgs_eq]
    show (List.filterMap _ (Local.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)))).map decMsg = _
    rw [local_filterP]
    simp only [List.filterMap_cons, List.filterMap_nil, chSend, stkSend, cntA, cntS, ite_true]
    have eO : decMsg ([Local.space, v Local.idx, Local.newTag] ++ (List.range 4).map Local.newVal ++ [v cTs] |>.map
        (·.eval (tr.row pub 9 r))) = mo := by
      simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, hNT, hNV, decMsg, List.getD_cons_zero, List.getD_cons_succ]
      simp only [v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Local.idx, cTs,
        Fp.toNat_cast_of_lt (hcP _), Fp.toNat_cast_of_lt hNTl, Fp.toNat_cast_of_lt (hNVl _), mo, c, NT, NV, spN]
    by_cases hw : rowNat tr 9 r 5 + rowNat tr 9 r 7 + rowNat tr 9 r 26 = 1
    · simp only [hw, ite_true, List.filterMap_cons, List.map_cons, List.map_nil, eO, List.cons.injEq, true_and, c]
      simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, hNT, hNV]
      simp only [v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', cell_cast, Trace.row, Local.kSb, Local.kCid,
        Local.rd, Local.fGet, Local.fGGet, cH, cTs, decMsg, List.getD_cons_zero, List.getD_cons_succ,
        Fp.toNat_cast_of_lt (hcP _), ms, c]
      exact ⟨by rw [Msg.mk.injEq]; exact ⟨Fp.toNat_cast_of_lt (by omega), rfl, Fp.toNat_cast_of_lt hNTl,
        Fp.toNat_cast_of_lt (hNVl 0), Fp.toNat_cast_of_lt (hNVl 1), Fp.toNat_cast_of_lt (hNVl 2),
        Fp.toNat_cast_of_lt (hNVl 3), rfl⟩, trivial⟩
    · simp only [hw, ite_false, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil, eO, c]
  -- channel time checks
  have tchk : ∀ (cnt : Expr) (tpc hic : Nat), (cnt.eval (tr.row pub 9 r)).toNat = 1 →
      r16 (v cTs - v tpc - 1 - B16 * v hic) cnt ∈ Local.inters → r16 (4 * v hic) cnt ∈ Local.inters →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 9 r tpc + 1 + n : Nat) : F) = ((rowNat tr 9 r 1 : Nat) : F) := by
    intro cnt tpc hic hc m1 m2
    have h1 := hocc _ m1
    have h2 := hocc _ m2
    simp only [r16, hc] at h1 h2
    simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat',
      B16, cTs, Trace.row] at h1 h2
    obtain ⟨n, hn, e⟩ := time_chk L h1 h2
    exact ⟨n, hn, e.trans (cell_cast tr 9 r 1)⟩
  have tL := tchk Local.act Local.tL Local.hL cntA (by simp [Local.inters, timeChk]) (by simp [Local.inters, timeChk])
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Local.op (v cH) (v cFee) [v Local.idx, 0, 0, 0] Local.act) (by simp [Local.inters, stdState])
  simp only [fetch, cntA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hoplt := recordOf_op_lt hrc
  rw [hre] at hm hoplt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add',
    Expr.eval_mul', Expr.eval_ofNat', cell_cast, Trace.row, Local.kSb, Local.kCid, cPc, cH, cFee, Local.op, Local.idx, Local.fSet,
    Local.fTee, Local.fGGet, Local.fGSet, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, ex0, ex1, ex2, ex3⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 9 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = 0x20 + rowNat tr 9 r 6 + 2 * rowNat tr 9 r 7 + 3 * rowNat tr 9 r 26 + 4 * rowNat tr 9 r 27 := by
    simp only [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add] at eop
    exact (natEq eop (by omega) (by omega)).symm
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee, hfl, ?_⟩, ?_, ?_, ?_⟩
  rotate_left
  · rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']
  · rw [hCons, hIn]
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact tL
    · split at hx
      · rename_i hw
        simp only [List.mem_singleton] at hx; subst hx
        exact tchk Local.wr Local.tV Local.hV (by rw [cntW]; exact hw) (by simp [Local.inters, timeChk]) (by simp [Local.inters, timeChk])
      · simp at hx
  · rw [hProd, hIn]
    intro x hx
    simp only [List.mem_cons] at hx
    have : x.tp = rowNat tr 9 r 1 := by
      rcases hx with rfl | hx
      · rfl
      · split at hx
        · simp only [List.mem_singleton] at hx; subst hx; rfl
        · simp at hx
    rw [this]; exact ⟨hcP _, rfl⟩
  · rw [hProd]
    split
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
        and_true]
      intro h; have := congrArg Msg.space h; simp only [mo, ms, c, spN] at this
      refine hne a1 ?_
      rw [← row_eq_natRow, ← Fp.cast_toNat (Local.space.eval (tr.row pub 9 r)), this]; rfl
    · simp
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have p0 : rowNat tr 9 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 9 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 9 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 9 r 23 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 9 r 24 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
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
  have p3 : rowNat tr 9 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  have hout : rowOut Local.table tr pub 9 r = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hCons] at hlive
  rw [hCons, hProd]
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  have hlL : live mL := hlive mL List.mem_cons_self
  have spU : Local.space.eval (tr.row pub 9 r) = (1 - (((rowNat tr 9 r 26 : Nat) : F) + ((rowNat tr 9 r 27 : Nat) : F))) *
      (((16 : Nat) : F) + ((rowNat tr 9 r 24 : Nat) : F)) +
      ((2 : Nat) : F) * (((rowNat tr 9 r 26 : Nat) : F) + ((rowNat tr 9 r 27 : Nat) : F)) := by
    simp only [Local.space, Local.isG, v, Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      Expr.eval_col, cell_cast, Trace.row, Local.kCid, Local.fGGet, Local.fGSet]
    grind
  have hsp : rowNat tr 9 r 26 = 0 → rowNat tr 9 r 27 = 0 → spN = E.lsp := fun a b => by
    show (Local.space.eval (tr.row pub 9 r)).toNat = _
    rw [spU, a, b, show (1 - (((0 : Nat) : F) + ((0 : Nat) : F))) * (((16 : Nat) : F) + ((rowNat tr 9 r 24 : Nat) : F)) +
      ((2 : Nat) : F) * (((0 : Nat) : F) + ((0 : Nat) : F)) = ((16 + rowNat tr 9 r 24 : Nat) : F) by
        rw [Lean.Grind.Semiring.natCast_add]; grind, pcid, Fp.toNat_cast_of_lt (by have := R.cidLt; omega)]; rfl
  have hspG : rowNat tr 9 r 26 + rowNat tr 9 r 27 = 1 → spN = 2 := fun a => by
    show (Local.space.eval (tr.row pub 9 r)).toNat = _
    rw [spU, ← Lean.Grind.Semiring.natCast_add, a, show (1 - ((1 : Nat) : F)) * (((16 : Nat) : F) +
      ((rowNat tr 9 r 24 : Nat) : F)) + ((2 : Nat) : F) * ((1 : Nat) : F) = ((2 : Nat) : F) by grind]
    exact Fp.toNat_cast_of_lt (by omega)
  -- the local index
  have hxl : ∀ x, ((X.pfOf E.k).code[pc]? = some (.localGet x) ∨ (X.pfOf E.k).code[pc]? = some (.localSet x) ∨
      (X.pfOf E.k).code[pc]? = some (.localTee x)) → x < f.locals.size := by
    intro x h
    rw [R.nloc]
    have hmem : ∀ i, (X.pfOf E.k).code[pc]? = some i → i ∈ (X.pfOf E.k).code.toList := fun i hi => by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
    rcases h with h | h | h
    · exact CF.locIdx _ (hmem _ h) x (Or.inl rfl)
    · exact CF.locIdx _ (hmem _ h) x (Or.inr (Or.inl rfl))
    · exact CF.locIdx _ (hmem _ h) x (Or.inr (Or.inr rfl))
  have hx0 : ∀ x, x0 = x → x < 2 ^ 16 → rowNat tr 9 r 8 = x := fun x h hlt => by
    subst h; exact natEq ex0 (hcP _) (by omega)
  have hnl : f.locals.size ≤ 64 := by rw [R.nloc]; exact CF.nloc
  have e3 : (((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) +
      ((1 : Nat) : F)).toNat = s.stack.size := by
    rw [show ((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) + ((1 : Nat) : F) =
      ((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) by grind]
    exact slot_toNat0 psb p3 hsbR hszP
  have e3' : 1 ≤ s.stack.size - E.sb → (((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) +
      ((0 : Nat) : F)).toNat = s.stack.size - 1 := by
    intro h1
    rw [show ((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) + ((0 : Nat) : F) =
      ((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) by grind]
    exact slot_toNat psb p3 hsbR h1 hszP
  have e3g : ∀ a b : Nat, a + b = 1 → (((rowNat tr 9 r 23 : Nat) : F) + ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) +
      (((a : Nat) : F) + ((b : Nat) : F))).toNat = s.stack.size := by
    intro a b hab
    rw [← Lean.Grind.Semiring.natCast_add a b, hab, ← e3]
  have e3g' : ∀ a b : Nat, a + b = 0 → 1 ≤ s.stack.size - E.sb → (((rowNat tr 9 r 23 : Nat) : F) +
      ((rowNat tr 9 r 3 : Nat) : F) - ((1 : Nat) : F) + (((a : Nat) : F) + ((b : Nat) : F))).toNat = s.stack.size - 1 := by
    intro a b hab h1
    rw [← Lean.Grind.Semiring.natCast_add a b, hab, ← e3' h1]
  rcases hcases with ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ |
      ⟨g5, g6, g7, g26, g27⟩ | ⟨g5, g6, g7, g26, g27⟩ <;> rw [g6, g7, g26, g27] at hop <;>
  rcases hcase with ⟨v, hv, h, hl⟩ | ⟨v, hv, h, hl⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨x, hv, h, hl⟩ | ⟨x, hv, h, hl⟩ |
    ⟨x, hv, h, hl⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨x, hv, h, hl, hx16⟩ | ⟨x, hv, h, hl, hx16⟩ | ⟨_, _, _, h, _⟩
  all_goals first
    | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
    | (exfalso; omega)
    | (exfalso; rw [hop] at hf; revert hf; decide)
    | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
    | (exfalso; simp only [opCall] at h; omega)
    | skip
  · -- local.get
    simp only [List.cons.injEq, and_true] at hl
    have hv' : (X.pfOf E.k).code[pc]? = some (.localGet x) := hv ▸ hins
    have hxv := hxl x (Or.inl hv')
    have e8 : rowNat tr 9 r 8 = x := hx0 x hl.1 (by omega)
    have sL := hsp g26 g27
    obtain ⟨s', hs', hrel⟩ := step_localGet X R hv' hxv hfee hg hg64 mL hlL ⟨sL, e8⟩ mo ms
      (fun hok => by rw [local_enc hok]; simp only [mo, mL, NT, NV, c, g5, g26, ite_true, e8, p1, sL, Nat.reduceAdd])
      (fun hok => by
        rw [local_enc hok]; simp only [ms, mL, NT, NV, c, p1]
        rw [e3g _ _ (by omega)]; simp only [g5, g26, ite_true, Nat.reduceAdd])
    refine ⟨s', hs', ?_⟩
    have i1 : (if c 6 + c 7 + c 27 = 1 then [mV] else []) = [] := by simp [c, g6, g7, g27]
    have i2 : (if c 5 + c 7 + c 26 = 1 then [ms] else []) = [ms] := by simp [c, g5, g7, g26]
    rw [i1, i2, stepLive_congr (fun _ => Iff.rfl) (show ∀ y, y ∈ [mo, ms] ↔ y ∈ [ms, mo] by
      intro y; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)]
    exact hrel
  · -- local.set
    simp only [List.cons.injEq, and_true] at hl
    have hv' : (X.pfOf E.k).code[pc]? = some (.localSet x) := hv ▸ hins
    have hxv := hxl x (Or.inr (Or.inl hv'))
    have e8 : rowNat tr 9 r 8 = x := hx0 x hl.1 (by omega)
    have sL := hsp g26 g27
    obtain ⟨h1, -⟩ := verify_straight X R.kLt hpcl hv' hL0 R.height (pops := 1) (pushes := 0)
      (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
    have hmV : live mV := hlive mV (by simp [c, g6, g7, g27])
    obtain ⟨s', hs', hrel⟩ := step_localSet X R hv' hxv hfee hg hg64 mV mL mo hmV hlL
      ⟨rfl, by simp only [mV, c]; exact slot_toNat psb p3 hsbR h1 hszP⟩ ⟨sL, e8⟩
      (fun hok => by rw [local_enc hok]; simp only [mo, mV, NT, NV, c, g5, g26, e8, p1, sL, Nat.reduceAdd]; rfl)
    refine ⟨s', hs', ?_⟩
    have i1 : (if c 6 + c 7 + c 27 = 1 then [mV] else []) = [mV] := by simp [c, g6, g7, g27]
    have i2 : (if c 5 + c 7 + c 26 = 1 then [ms] else []) = [] := by simp [c, g5, g7, g26]
    rw [i1, i2, stepLive_congr (show ∀ y, y ∈ [mL, mV] ↔ y ∈ [mV, mL] by intro y; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)
      (fun _ => Iff.rfl)]
    exact hrel
  · -- local.tee
    simp only [List.cons.injEq, and_true] at hl
    have hv' : (X.pfOf E.k).code[pc]? = some (.localTee x) := hv ▸ hins
    have hxv := hxl x (Or.inr (Or.inr hv'))
    have e8 : rowNat tr 9 r 8 = x := hx0 x hl.1 (by omega)
    have sL := hsp g26 g27
    obtain ⟨h1, -⟩ := verify_straight X R.kLt hpcl hv' hL0 R.height (pops := 1) (pushes := 1)
      (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
    have hmV : live mV := hlive mV (by simp [c, g6, g7, g27])
    obtain ⟨s', hs', hrel⟩ := step_localTee X R hv' hxv hfee hg hg64 mV mL mo ms hmV hlL
      ⟨rfl, by simp only [mV, c]; exact slot_toNat psb p3 hsbR h1 hszP⟩ ⟨sL, e8⟩
      (fun hok => by rw [local_enc hok]; simp only [mo, mV, NT, NV, c, g5, g26, e8, p1, sL, Nat.reduceAdd]; rfl)
      (fun hok => by
        rw [local_enc hok]; simp only [ms, mV, NT, NV, c, p1]
        rw [e3g' _ _ (by omega) h1]; simp only [g5, g26, Nat.reduceAdd]; rfl)
    refine ⟨s', hs', ?_⟩
    have i1 : (if c 6 + c 7 + c 27 = 1 then [mV] else []) = [mV] := by simp [c, g6, g7, g27]
    have i2 : (if c 5 + c 7 + c 26 = 1 then [ms] else []) = [ms] := by simp [c, g5, g7, g26]
    rw [i1, i2, stepLive_congr (show ∀ y, y ∈ [mL, mV] ↔ y ∈ [mV, mL] by intro y; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)
      (show ∀ y, y ∈ [mo, ms] ↔ y ∈ [ms, mo] by intro y; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)]
    exact hrel
  · -- global.get
    simp only [List.cons.injEq, and_true] at hl
    have hv' : (X.pfOf E.k).code[pc]? = some (.globalGet x) := hv ▸ hins
    have e8 : rowNat tr 9 r 8 = x := hx0 x hl.1 hx16
    have sG := hspG (by omega)
    obtain ⟨s', hs', hrel⟩ := step_globalGet X R hv' hx16 hfee hg hg64 mL hlL ⟨sG, e8⟩ mo ms
      (fun hok => by rw [local_enc hok]; simp only [mo, mL, NT, NV, c, g5, g26, ite_true, e8, p1, sG, Nat.reduceAdd])
      (fun hok => by
        rw [local_enc hok]; simp only [ms, mL, NT, NV, c, p1]
        rw [e3g _ _ (by omega)]; simp only [g5, g26, ite_true, Nat.reduceAdd])
    refine ⟨s', hs', ?_⟩
    have i1 : (if c 6 + c 7 + c 27 = 1 then [mV] else []) = [] := by simp [c, g6, g7, g27]
    have i2 : (if c 5 + c 7 + c 26 = 1 then [ms] else []) = [ms] := by simp [c, g5, g7, g26]
    rw [i1, i2, stepLive_congr (fun _ => Iff.rfl) (show ∀ y, y ∈ [mo, ms] ↔ y ∈ [ms, mo] by
      intro y; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)]
    exact hrel
  · -- global.set
    simp only [List.cons.injEq, and_true] at hl
    have hv' : (X.pfOf E.k).code[pc]? = some (.globalSet x) := hv ▸ hins
    have e8 : rowNat tr 9 r 8 = x := hx0 x hl.1 hx16
    have sG := hspG (by omega)
    obtain ⟨h1, -⟩ := verify_straight X R.kLt hpcl hv' hL0 R.height (pops := 1) (pushes := 0)
      (by simp [kindOf, hx16]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
    have hmV : live mV := hlive mV (by simp [c, g6, g7, g27])
    obtain ⟨s', hs', hrel⟩ := step_globalSet X R hv' hx16 hfee hg hg64 mV mL mo hmV hlL
      ⟨rfl, by simp only [mV, c]; exact slot_toNat psb p3 hsbR h1 hszP⟩ ⟨sG, e8⟩
      (fun hok => by rw [local_enc hok]; simp only [mo, mV, NT, NV, c, g5, g26, e8, p1, sG, Nat.reduceAdd]; rfl)
    refine ⟨s', hs', ?_⟩
    have i1 : (if c 6 + c 7 + c 27 = 1 then [mV] else []) = [mV] := by simp [c, g6, g7, g27]
    have i2 : (if c 5 + c 7 + c 26 = 1 then [ms] else []) = [] := by simp [c, g5, g7, g26]
    rw [i1, i2, stepLive_congr (show ∀ y, y ∈ [mL, mV] ↔ y ∈ [mV, mL] by intro y; simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm)
      (fun _ => Iff.rfl)]
    exact hrel

end WasmBase

namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

theorem local_count_cases : ∀ i ∈ Local.inters,
    i.count = Local.act ∨ i.count = Local.wr ∨ i.count = v Local.fGet + v Local.fTee + v Local.fGGet := by
  intro i hi
  have := List.all_eq_true.mp (show Local.inters.all (fun i => decide (i.count = Local.act ∨ i.count = Local.wr ∨
    i.count = v Local.fGet + v Local.fTee + v Local.fGGet)) = true by decide) i hi
  exact of_decide_eq_true this

/-- The three count values of a LOCAL row, as naturals. -/
theorem local_count_vals_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Local.table.constraints, e.eval (natRow (rowNat tr 9 r) (tr.row pub 9 r)) = 0) :
    rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 ≤ 1 ∧
    (Local.act.eval (tr.row pub 9 r)).toNat =
      rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 ∧
    (Local.wr.eval (tr.row pub 9 r)).toNat = rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 27 ∧
    ((v Local.fGet + v Local.fTee + v Local.fGGet).eval (tr.row pub 9 r)).toNat =
      rowNat tr 9 r 5 + rowNat tr 9 r 7 + rowNat tr 9 r 26 := by
  have hP' := P_val
  have hcP : ∀ i, rowNat tr 9 r i < P := rowNat_lt tr 9 r
  obtain ⟨-, -, -, -, -, hsum, -⟩ := local_sound (rowNat tr 9 r) (tr.row pub 9 r) hcP hcon
  replace hsum : rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 ≤ 1 := hsum
  refine ⟨hsum, ?_, ?_, ?_⟩
  · show (tr.cell 9 r 5 + tr.cell 9 r 6 + tr.cell 9 r 7 + tr.cell 9 r 26 + tr.cell 9 r 27).toNat = _
    simp only [cell_cast, ← Lean.Grind.Semiring.natCast_add]; exact Fp.toNat_cast_of_lt (by omega)
  · show (tr.cell 9 r 6 + tr.cell 9 r 7 + tr.cell 9 r 27).toNat = _
    simp only [cell_cast, ← Lean.Grind.Semiring.natCast_add]; exact Fp.toNat_cast_of_lt (by omega)
  · show (tr.cell 9 r 5 + tr.cell 9 r 7 + tr.cell 9 r 26).toNat = _
    simp only [cell_cast, ← Lean.Grind.Semiring.natCast_add]; exact Fp.toNat_cast_of_lt (by omega)

theorem local_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Local.table.constraints, e.eval (natRow (rowNat tr 9 r) (tr.row pub 9 r)) = 0) :
    ∀ i ∈ Local.inters, (i.count.eval (tr.row pub 9 r)).toNat ≤ 1 := by
  obtain ⟨hs, ha, hw, hg⟩ := local_count_vals_of hcon
  intro i hi
  rcases local_count_cases i hi with h | h | h <;> rw [h] <;> omega

theorem local_count_vals {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 9) :
    rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 ≤ 1 ∧
    (Local.act.eval (tr.row pub 9 r)).toNat =
      rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 ∧
    (Local.wr.eval (tr.row pub 9 r)).toNat = rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 27 ∧
    ((v Local.fGet + v Local.fTee + v Local.fGGet).eval (tr.row pub 9 r)).toNat =
      rowNat tr 9 r 5 + rowNat tr 9 r 7 + rowNat tr 9 r 26 :=
  local_count_vals_of (table_constr H (by simp [air_len]) hr)

theorem local_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 9) :
    ∀ i ∈ Local.inters, (i.count.eval (tr.row pub 9 r)).toNat ≤ 1 :=
  local_counts_of (table_constr H (by simp [air_len]) hr)

theorem local_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 9)
    (hna : ¬ rowAct Local.table tr pub 9 r) :
    ∀ i ∈ Local.inters, (i.count.eval (tr.row pub 9 r)).toNat ≠ 1 := by
  obtain ⟨hs, ha, hw, hg⟩ := local_count_vals H hr
  have h0 : rowNat tr 9 r 5 + rowNat tr 9 r 6 + rowNat tr 9 r 7 + rowNat tr 9 r 26 + rowNat tr 9 r 27 = 0 := by
    have : (Local.act.eval (tr.row pub 9 r)).toNat ≠ 1 := hna
    omega
  intro i hi
  rcases local_count_cases i hi with h | h | h <;> rw [h] <;> omega
