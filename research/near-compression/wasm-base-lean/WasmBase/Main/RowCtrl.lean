import WasmBase.Main.Rows
import WasmBase.StepCtrl
import WasmBase.StepOps2
import WasmBase.Local.Simple
/-!
# Row lemma: CTRL (block / loop / nested end, br, br_if, end-of-function / return / br-to-function,
br_if-to-function)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

theorem ctrl_kind_next {ls : List Label} {ins : Instr} (h : kindOf ls ins = some .next) :
    (∃ bt, ins = .block bt) ∨ ins = .loop none ∨ (ins = .end_ ∧ ∃ a b rest, ls = a :: b :: rest) := by
  cases ins <;> simp only [kindOf, reduceCtorEq, Option.some.injEq] at h <;> try simp
  case loop bt => cases bt <;> simp_all [kindOf]
  case end_ => split at h <;> simp_all
  case br l => split at h <;> simp_all
  case brIf l => split at h <;> simp_all
  case num op => split at h <;> (try simp_all)
  case load => split at h <;> simp_all
  case store => split at h <;> simp_all
  case globalGet => split at h <;> simp_all
  case globalSet => split at h <;> simp_all

theorem ctrl_kind_jump {ls : List Label} {ins : Instr} {tg : Nat} (h : kindOf ls ins = some (.jump tg)) :
    ∃ l lab, ins = .br l ∧ l + 1 < ls.length ∧ ls[l]? = some lab ∧ tg = lab.target := by
  cases ins <;> simp only [kindOf, reduceCtorEq, Option.some.injEq] at h
  case loop bt => cases bt <;> simp_all [kindOf]
  case end_ => split at h <;> simp_all
  case br l =>
    split at h
    · simp at h
    · rename_i hl
      cases hls : ls[l]? with
      | none => simp [hls] at h
      | some lab => simp only [hls, Option.map_some, Option.some.injEq, Kind.jump.injEq] at h
                    exact ⟨l, lab, rfl, by omega, hls, h.symm⟩
  case brIf l => split at h <;> (try simp at h) <;> (try (cases ls[l]? <;> simp_all))
  case num op => split at h <;> (try simp_all)
  case load => split at h <;> simp_all
  case store => split at h <;> simp_all
  case globalGet => split at h <;> simp_all
  case globalSet => split at h <;> simp_all

theorem ctrl_kind_jif {ls : List Label} {ins : Instr} {tg : Nat} (h : kindOf ls ins = some (.jumpIf tg)) :
    ∃ l lab, ins = .brIf l ∧ l + 1 < ls.length ∧ ls[l]? = some lab ∧ tg = lab.target := by
  cases ins <;> simp only [kindOf, reduceCtorEq, Option.some.injEq] at h
  case loop bt => cases bt <;> simp_all [kindOf]
  case end_ => split at h <;> simp_all
  case br l => split at h <;> (try simp at h) <;> (try (cases ls[l]? <;> simp_all))
  case brIf l =>
    split at h
    · simp at h
    · rename_i hl
      cases hls : ls[l]? with
      | none => simp [hls] at h
      | some lab => simp only [hls, Option.map_some, Option.some.injEq, Kind.jumpIf.injEq] at h
                    exact ⟨l, lab, rfl, by omega, hls, h.symm⟩
  case num op => split at h <;> (try simp_all)
  case load => split at h <;> simp_all
  case store => split at h <;> simp_all
  case globalGet => split at h <;> simp_all
  case globalSet => split at h <;> simp_all

theorem ctrl_kind_halt {ls : List Label} {ins : Instr} (h : kindOf ls ins = some .halt) :
    (ins = .end_ ∧ ls.length = 1) ∨ ins = .ret ∨ (∃ l, ins = .br l ∧ l + 1 ≥ ls.length) := by
  cases ins <;> simp only [kindOf, reduceCtorEq, Option.some.injEq] at h <;> try simp
  case loop bt => cases bt <;> simp_all [kindOf]
  case end_ => split at h <;> simp_all
  case br l => split at h <;> (try simp_all) <;> (try (cases ls[l]? <;> simp_all))
  case brIf l => split at h <;> (try simp at h) <;> (try (cases ls[l]? <;> simp_all))
  case num op => split at h <;> (try simp_all)
  case load => split at h <;> simp_all
  case store => split at h <;> simp_all
  case globalGet => split at h <;> simp_all
  case globalSet => split at h <;> simp_all

theorem ctrl_kind_hif {ls : List Label} {ins : Instr} (h : kindOf ls ins = some .haltIf) :
    ∃ l, ins = .brIf l ∧ l + 1 ≥ ls.length := by
  cases ins <;> simp only [kindOf, reduceCtorEq, Option.some.injEq] at h
  case loop bt => cases bt <;> simp_all [kindOf]
  case end_ => split at h <;> simp_all
  case br l => split at h <;> (try simp at h) <;> (try (cases ls[l]? <;> simp_all))
  case brIf l =>
    split at h
    · exact ⟨l, rfl, by omega⟩
    · cases ls[l]? <;> simp_all
  case num op => split at h <;> simp_all
  case load => split at h <;> simp_all
  case store => split at h <;> simp_all
  case globalGet => split at h <;> simp_all
  case globalSet => split at h <;> simp_all

theorem ctrl_facts (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Ctrl.constraints, e.eval (natRow c rw) = 0) :
    (c 5 = 0 ∨ c 5 = 1) ∧ (c 6 = 0 ∨ c 6 = 1) ∧ (c 7 = 0 ∨ c 7 = 1) ∧ (c 8 = 0 ∨ c 8 = 1) ∧
    (c 9 = 0 ∨ c 9 = 1) ∧ c 5 + c 6 + c 7 + c 8 + c 9 ≤ 1 ∧
    (c 11 + c 12 < P → Ctrl.nz.eval (natRow c rw) = ((if c 11 + c 12 = 0 then 0 else 1 : Nat) : F)) ∧
    (c 8 + c 9 = 0 ∨ c 17 = 0) := by
  simp only [Ctrl.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, v, Ctrl.act, Ctrl.nz, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at hc
  obtain ⟨bN, bJ, bI, bH, bF, bAct, hnz, hcid⟩ := hc
  have n := bool_nat (hP _) bN; have j := bool_nat (hP _) bJ; have i := bool_nat (hP _) bI
  have h := bool_nat (hP _) bH; have f := bool_nat (hP _) bF
  refine ⟨n, j, i, h, f, ?_, fun hz => ?_, ?_⟩
  · have hs : c Ctrl.fNext + c Ctrl.fJump + c Ctrl.fJif + c Ctrl.fHalt + c Ctrl.fHif < P := by
      have := P_val; simp only [Ctrl.fNext, Ctrl.fJump, Ctrl.fJif, Ctrl.fHalt, Ctrl.fHif] at *; omega
    have := bool_nat hs (by simpa only [Lean.Grind.Semiring.natCast_add] using bAct)
    simp only [Ctrl.fNext, Ctrl.fJump, Ctrl.fJif, Ctrl.fHalt, Ctrl.fHif] at this; omega
  · have hn := nz_val (inv := c Ctrl.inv) hz (by
      have : (((c 11 : Nat) : F) + ((c 12 : Nat) : F)) * (((1 : Nat) : F) - (((c 11 : Nat) : F) + ((c 12 : Nat) : F)) *
        ((c Ctrl.inv : Nat) : F)) = 0 := hnz
      simpa only [Lean.Grind.Semiring.natCast_add] using this)
    simp only [Ctrl.nz, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, natRow]
    rw [show ((c Ctrl.c : F) + (c (Ctrl.c + 1) : F)) = ((c 11 + c 12 : Nat) : F) by
      simp only [Lean.Grind.Semiring.natCast_add]; rfl]
    exact hn
  · simp only [Ctrl.fHalt, Ctrl.fHif, Ctrl.kCid] at hcid h f
    have hs : c 8 + c 9 < P := by have := P_val; omega
    exact zero_of_mul_nat hs (hP _) (by simpa only [Lean.Grind.Semiring.natCast_add] using hcid)

theorem ctrl_view_pop (a : Array Val) (tps : Nat → Nat) (h : 1 ≤ a.size) (x : Msg) :
    (x ∈ stackView a tps ∧ x ≠ enc 0 (a.size - 1) (a[a.size - 1]?.getD default) (tps (a.size - 1))) ↔
      x ∈ stackView a.pop tps := by
  simp only [mem_stackView, Array.size_pop]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hne⟩
    have : i ≠ a.size - 1 := fun e => hne (by subst e; rfl)
    exact ⟨i, by omega, by rw [pop_get a i (by omega)]⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, by omega, by rw [pop_get a i (by omega)]⟩, fun e => ?_⟩
    have := congrArg Msg.slot e
    simp [enc] at this; omega

theorem ctrl_brIf_h {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb) {l : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.brIf l)) : 1 ≤ s.stack.size - E.sb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt
  unfold verifyAt at hv
  obtain ⟨ls0, hL0, -⟩ := R.labels
  rw [hins, hL0, R.height] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.1.1

theorem ctrl_filterC :
    Ctrl.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)) =
      [stkRecv (v Ctrl.kSb + v cH - 1) 0 [v Ctrl.c, v (Ctrl.c + 1), 0, 0] (v Ctrl.tc) Ctrl.cnd] := by decide

theorem ctrl_filterP : Ctrl.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) = [] := by decide

theorem ctrl_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 8) (hact : rowAct Ctrl.table tr pub 8 r) :
    RowFacts X (rowIn Ctrl.table tr pub 8 r) (rowOut Ctrl.table tr pub 8 r)
      (rowCons Ctrl.table tr pub 8 r) (rowProd Ctrl.table tr pub 8 r) := by
  have hP' := P_val
  have ht : 8 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 8 r i < P := rowNat_lt tr 8 r
  have hcon : ∀ e ∈ Ctrl.table.constraints, e.eval (natRow (rowNat tr 8 r) (tr.row pub 8 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨g5, g6, g7, g8, g9, hsum, hnzF, hcid0⟩ := ctrl_facts (rowNat tr 8 r) (tr.row pub 8 r) hcP hcon
  have cntA0 : (Ctrl.act.eval (tr.row pub 8 r)).toNat =
      rowNat tr 8 r 5 + rowNat tr 8 r 6 + rowNat tr 8 r 7 + rowNat tr 8 r 8 + rowNat tr 8 r 9 := by
    show (tr.cell 8 r 5 + tr.cell 8 r 6 + tr.cell 8 r 7 + tr.cell 8 r 8 + tr.cell 8 r 9).toNat = _
    rw [cell_cast, cell_cast, cell_cast, cell_cast, cell_cast]
    simp only [← Lean.Grind.Semiring.natCast_add]
    exact Fp.toNat_cast_of_lt (by omega)
  have a1 : rowNat tr 8 r 5 + rowNat tr 8 r 6 + rowNat tr 8 r 7 + rowNat tr 8 r 8 + rowNat tr 8 r 9 = 1 :=
    cntA0.symm.trans hact
  have cntA : (Ctrl.act.eval (tr.row pub 8 r)).toNat = 1 := hact
  have cntC : (Ctrl.cnd.eval (tr.row pub 8 r)).toNat = rowNat tr 8 r 7 + rowNat tr 8 r 9 := by
    show (tr.cell 8 r 7 + tr.cell 8 r 9).toNat = _
    rw [cell_cast, cell_cast, ← Lean.Grind.Semiring.natCast_add]
    exact Fp.toNat_cast_of_lt (by omega)
  have hocc : ∀ i ∈ Ctrl.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 8 r)),
      (i.count.eval (tr.row pub 8 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Ctrl.table.inters from hi)
  -- the STATE messages
  let N := Ctrl.nz.eval (natRow (rowNat tr 8 r) (tr.row pub 8 r))
  let cc : Nat → F := fun i => ((rowNat tr 8 r i : Nat) : F)
  have hIn : rowIn Ctrl.table tr pub 8 r = [cc 0, cc 1, cc 2, ((0 : Nat) : F), cc 16, cc 17] := by
    simp only [rowIn, Ctrl.table, Ctrl.inters, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cTs, cS,
      Ctrl.kSb, Ctrl.kCid, cc]
  have hOut : rowOut Ctrl.table tr pub 8 r =
      [cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 +
        cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)), cc 1 + ((1 : Nat) : F), cc 2 + cc 4, cc 8 + cc 9 * N,
        cc 16, cc 17] := by
    simp only [rowOut, Ctrl.table, Ctrl.inters, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil]
    rw [row_eq_natRow]
    simp only [Ctrl.pcNext, Ctrl.pc1, Ctrl.halted, v, Expr.eval_col, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
      Expr.eval_ofNat', natRow, cPc, cTs, cS, cFee, Ctrl.fNext, Ctrl.fJump, Ctrl.fJif, Ctrl.fHalt, Ctrl.fHif,
      Ctrl.tgt, Ctrl.kSb, Ctrl.kCid, cc, N, cast_one]
  -- the consumed condition
  let mC : Msg := ⟨0, (cc 16 + cc 3 - ((1 : Nat) : F)).toNat, 0, rowNat tr 8 r 11, rowNat tr 8 r 12, 0, 0, rowNat tr 8 r 13⟩
  have hCons : rowCons Ctrl.table tr pub 8 r =
      if rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 then [mC] else [] := by
    rw [rowCons, rowMsgs_eq]
    show (List.filterMap _ (Ctrl.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)))).map decMsg = _
    rw [ctrl_filterC]
    simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, cntC]
    by_cases hw : rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1
    · simp only [hw, ite_true, List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_col,
        Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', cell_cast, Trace.row, cH, Ctrl.kSb, Ctrl.c, Ctrl.tc, decMsg, List.getD_cons_zero,
        List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _), List.cons.injEq, and_true, mC, cc]
      rw [Msg.mk.injEq]
      exact ⟨Fp.toNat_cast_of_lt (by omega), rfl, Fp.toNat_cast_of_lt (by omega), rfl, rfl,
        Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), rfl⟩
    · simp only [hw, ite_false, List.map_nil]
  have hProd : rowProd Ctrl.table tr pub 8 r = [] := by
    rw [rowProd, rowMsgs_eq]
    show (List.filterMap _ (Ctrl.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)))).map decMsg = _
    rw [ctrl_filterP]; rfl
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Ctrl.op (v cH) (v cFee) [v Ctrl.tgt, 0, 0, 0] Ctrl.act)
    (by simp [Ctrl.inters])
  simp only [fetch, cntA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hoplt := recordOf_op_lt hrc
  rw [hre] at hm hoplt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add',
    Expr.eval_mul', Expr.eval_c, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cH, cFee, Ctrl.op, Ctrl.tgt,
    Ctrl.fNext, Ctrl.fJump, Ctrl.fJif, Ctrl.fHalt, Ctrl.fHif, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, ex0, ex1, ex2, ex3⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 8 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = Ctrl.opNext * rowNat tr 8 r 5 + Ctrl.opJump * rowNat tr 8 r 6 + Ctrl.opJif * rowNat tr 8 r 7 +
      Ctrl.opHalt * rowNat tr 8 r 8 + Ctrl.opHif * rowNat tr 8 r 9 := by
    simp only [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add] at eop
    refine (natEq eop ?_ (by omega)).symm
    simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif]; omega
  -- channel time check of the condition
  have tchk : rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 8 r 13 + 1 + n : Nat) : F) = ((rowNat tr 8 r 1 : Nat) : F) := by
    intro hw
    have hc : (Ctrl.cnd.eval (tr.row pub 8 r)).toNat = 1 := by rw [cntC]; exact hw
    have h1 := hocc (r16 (v cTs - v Ctrl.tc - 1 - B16 * v Ctrl.hc) Ctrl.cnd) (by simp [Ctrl.inters, timeChk])
    have h2 := hocc (r16 (4 * v Ctrl.hc) Ctrl.cnd) (by simp [Ctrl.inters, timeChk])
    simp only [r16, hc] at h1 h2
    simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat',
      B16, cTs, Trace.row] at h1 h2
    obtain ⟨n, hn, e⟩ := time_chk L h1 h2
    exact ⟨n, hn, e.trans (cell_cast tr 8 r 1)⟩
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee, hfl, ?_⟩, ?_, by rw [hProd]; simp,
    by rw [hProd]; simp⟩
  rotate_left
  · rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee', cc]
  · rw [hCons, hIn]
    intro x hx
    split at hx
    · rename_i hw
      simp only [List.mem_singleton] at hx; subst hx
      exact tchk hw
    · simp at hx
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : rowNat tr 8 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 8 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 8 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 8 r 16 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 8 r 17 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
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
  have p3 : rowNat tr 8 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hlen : f.labels.length = ls0.length := by rw [hfl0, shiftLabels_length]
  -- HALT / HALTIF only in the entry frame
  have hent : rowNat tr 8 r 8 + rowNat tr 8 r 9 = 1 → E.rest = [] ∧ E.sb = 0 ∧ E.lsp = 16 := by
    intro h1
    have hc : E.cid = 0 := by
      rw [← pcid]; rcases hcid0 with h | h
      · exact absurd h1 (by rw [h]; decide)
      · exact h
    exact ⟨(R.entry hc).1, (R.entry hc).2, by simp [Env.lsp, hc]⟩
  rw [hL0] at hcase
  simp only [Option.getD_some] at hcase
  rw [hCons] at hlive ⊢
  rw [hProd]
  have mkOut : ∀ (pc' hb : Nat),
      cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 +
        cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = ((pc' : Nat) : F) → cc 8 + cc 9 * N = ((hb : Nat) : F) →
      rowOut Ctrl.table tr pub 8 r = stMsg pc' (t + 1) (S + fee) hb E.sb E.cid := by
    intro pc' hb e1 e2
    rw [hOut, e1, e2]
    simp only [stMsg, cc, p1, p2, efee', psb, pcid, Lean.Grind.Semiring.natCast_add]
  have hgN : ∀ sN stk, Halted X s sN fee stk → X.R * (S + fee - S_seg) ≤ segb →
      X.R * (S + fee - S_seg) + sN.gas.g = segb := by
    rintro sN stk ⟨-, -, hgg⟩ hg
    exact R.step_gas hg hgg
  have c1F : cc 0 = ((X.offOf E.k + pc : Nat) : F) := by simp only [cc, p0]
  -- the condition (when consumed)
  have hcnd : ∀ l, (X.pfOf E.k).code[pc]? = some (.brIf l) → rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 →
      live mC ∧ (mC.space = 0 ∧ mC.slot = s.stack.size - 1) ∧ 1 ≤ s.stack.size - E.sb ∧
      mC = enc 0 (s.stack.size - 1) (s.stack[s.stack.size - 1]?.getD default) (tps (s.stack.size - 1)) ∧
      N = ((if rowNat tr 8 r 11 + rowNat tr 8 r 12 = 0 then 0 else 1 : Nat) : F) ∧
      (mC.val = 0 ↔ rowNat tr 8 r 11 + rowNat tr 8 r 12 = 0) := by
    intro l hl hw
    have h1 := ctrl_brIf_h R hl
    have hmC : live mC := hlive mC (by simp [hw])
    have sc : mC.space = 0 ∧ mC.slot = s.stack.size - 1 := ⟨rfl, by
      show (cc 16 + cc 3 - ((1 : Nat) : F)).toNat = _
      simp only [cc]; exact slot_toNat psb p3 hsbR h1 hszP⟩
    obtain ⟨ec, okc, -, -⟩ := R.stack_dec hmC sc.1 sc.2 (by omega)
    obtain ⟨o0, o1, -⟩ := okc
    simp only [mC] at o0 o1
    refine ⟨hmC, sc, h1, ec, hnzF (by omega), ?_⟩
    simp only [Msg.val, val4, mC]; omega
  rcases (show (rowNat tr 8 r 5 = 1 ∧ rowNat tr 8 r 6 = 0 ∧ rowNat tr 8 r 7 = 0 ∧ rowNat tr 8 r 8 = 0 ∧ rowNat tr 8 r 9 = 0) ∨
      (rowNat tr 8 r 5 = 0 ∧ rowNat tr 8 r 6 = 1 ∧ rowNat tr 8 r 7 = 0 ∧ rowNat tr 8 r 8 = 0 ∧ rowNat tr 8 r 9 = 0) ∨
      (rowNat tr 8 r 5 = 0 ∧ rowNat tr 8 r 6 = 0 ∧ rowNat tr 8 r 7 = 1 ∧ rowNat tr 8 r 8 = 0 ∧ rowNat tr 8 r 9 = 0) ∨
      (rowNat tr 8 r 5 = 0 ∧ rowNat tr 8 r 6 = 0 ∧ rowNat tr 8 r 7 = 0 ∧ rowNat tr 8 r 8 = 1 ∧ rowNat tr 8 r 9 = 0) ∨
      (rowNat tr 8 r 5 = 0 ∧ rowNat tr 8 r 6 = 0 ∧ rowNat tr 8 r 7 = 0 ∧ rowNat tr 8 r 8 = 0 ∧ rowNat tr 8 r 9 = 1)
      by omega) with
    ⟨f5, f6, f7, f8, f9⟩ | ⟨f5, f6, f7, f8, f9⟩ | ⟨f5, f6, f7, f8, f9⟩ | ⟨f5, f6, f7, f8, f9⟩ | ⟨f5, f6, f7, f8, f9⟩ <;>
  rw [f5, f6, f7, f8, f9] at hop <;>
  simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at hop <;>
  rcases hcase with ⟨v, hv, h, hl⟩ | ⟨v, hv, h, hl⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨x, hv, h, hl⟩ | ⟨x, hv, h, hl⟩ |
    ⟨x, hv, h, hl⟩ | ⟨_, hf, _⟩ | ⟨hk, h, hl⟩ | ⟨tg, hk, h, hl⟩ | ⟨tg, hk, h, hl⟩ | ⟨hk, h, hl⟩ | ⟨hk, h, hl⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
  all_goals first
    | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
    | (exfalso; omega)
    | (exfalso; rw [hop] at hf; revert hf; decide)
    | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
    | (exfalso; simp only [opCall] at h; omega)
    | skip
  all_goals (
    have k5 : cc 5 = ((rowNat tr 8 r 5 : Nat) : F) := rfl
    have k6 : cc 6 = ((rowNat tr 8 r 6 : Nat) : F) := rfl
    have k7 : cc 7 = ((rowNat tr 8 r 7 : Nat) : F) := rfl
    have k8 : cc 8 = ((rowNat tr 8 r 8 : Nat) : F) := rfl
    have k9 : cc 9 = ((rowNat tr 8 r 9 : Nat) : F) := rfl
    rw [f5] at k5; rw [f6] at k6; rw [f7] at k7; rw [f8] at k8; rw [f9] at k9
    simp only [cast_zero, cast_one] at k5 k6 k7 k8 k9)
  · -- NEXT: block / loop / nested end
    have i1 : (if rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 then [mC] else []) = [] := by simp [f7, f9]
    rw [i1]
    have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + (pc + 1) : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, c1F]; simp only [Lean.Grind.Semiring.natCast_add, cast_one]; grind)
    have o2 : _ := (show cc 8 + cc 9 * N = ((0 : Nat) : F) by rw [k8, k9, cast_zero]; grind)
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, mkOut _ _ o1 o2,
      fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    rcases ctrl_kind_next hk with ⟨bt, rfl⟩ | rfl | ⟨rfl, a, b, rest, hls⟩
    · exact step_block X R hins hfee hg hg64
    · exact step_loop X R hins hfee hg hg64
    · exact step_end_nested X R (by rw [hfl0, hls]; rfl) hins hfee hg hg64
  · -- JUMP: br to an enclosing label
    have i1 : (if rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 then [mC] else []) = [] := by simp [f7, f9]
    rw [i1]
    obtain ⟨l, lab, rfl, hl', hlab, htg⟩ := ctrl_kind_jump hk
    simp only [List.cons.injEq, and_true] at hl
    have e10 : cc 10 = ((X.offOf E.k + lab.target : Nat) : F) := by rw [← htg, Nat.add_comm, ← hl.1]; exact ex0
    have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + lab.target : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, e10]; grind)
    have o2 : _ := (show cc 8 + cc 9 * N = ((0 : Nat) : F) by rw [k8, k9, cast_zero]; grind)
    refine ⟨E.k, lab.target, fee, 0, E.sb, E.cid, hfl, by omega, mkOut _ _ o1 o2, fun hg => ⟨fun _ =>
      step_br X R (lab := { lab with height := lab.height + E.sb }) (by rw [hlen]; exact hl') (by rw [hfl0, shiftLabels_get, hlab]; rfl) hins hfee hg hg64,
      fun h => absurd h (by decide)⟩⟩
  · -- JUMPIF: br_if to an enclosing label
    obtain ⟨l, lab, rfl, hl', hlab, htg⟩ := ctrl_kind_jif hk
    simp only [List.cons.injEq, and_true] at hl
    have e10 : cc 10 = ((X.offOf E.k + lab.target : Nat) : F) := by rw [← htg, Nat.add_comm, ← hl.1]; exact ex0
    have hw : rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 := by omega
    obtain ⟨hmC, sc, -, -, hN, hval⟩ := hcnd l hins hw
    have i1 : (if rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 then [mC] else []) = [mC] := by simp [hw]
    rw [i1]
    by_cases hz : rowNat tr 8 r 11 + rowNat tr 8 r 12 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), cast_zero] at hN
      have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + (pc + 1) : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, hN, c1F]; simp only [Lean.Grind.Semiring.natCast_add, cast_one]; grind)
      have o2 : _ := (show cc 8 + cc 9 * N = ((0 : Nat) : F) by rw [k8, k9, cast_zero]; grind)
      refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, mkOut _ _ o1 o2,
        fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
      obtain ⟨s', hs', hrel⟩ := step_brIf X R (lab := { lab with height := lab.height + E.sb }) (by rw [hlen]; exact hl') (by rw [hfl0, shiftLabels_get, hlab]; rfl) hins hfee hg hg64 mC hmC sc
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hval.mpr hz))] at hrel
      exact ⟨s', hs', hrel⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hz), cast_one] at hN
      have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + lab.target : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, hN, e10]; grind)
      have o2 : _ := (show cc 8 + cc 9 * N = ((0 : Nat) : F) by rw [k8, k9, cast_zero]; grind)
      refine ⟨E.k, lab.target, fee, 0, E.sb, E.cid, hfl, by omega, mkOut _ _ o1 o2, fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
      obtain ⟨s', hs', hrel⟩ := step_brIf X R (lab := { lab with height := lab.height + E.sb }) (by rw [hlen]; exact hl') (by rw [hfl0, shiftLabels_get, hlab]; rfl) hins hfee hg hg64 mC hmC sc
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hz (hval.mp h)))] at hrel
      exact ⟨s', hs', hrel⟩
  · -- HALT: end of the body / return / br to the function label
    have i1 : (if rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 then [mC] else []) = [] := by simp [f7, f9]
    rw [i1]
    have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + pc : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, c1F]; grind)
    have o2 : _ := (show cc 8 + cc 9 * N = ((1 : Nat) : F) by rw [k8, k9, cast_one]; grind)
    refine ⟨E.k, pc, fee, 1, E.sb, E.cid, hfl, Nat.le_refl _, mkOut _ _ o1 o2, fun hg => ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
    obtain ⟨he1, he2, he3⟩ := hent (by omega)
    obtain ⟨sN, hsN, hHalt⟩ := step_halt X R hins (by rw [hlen]; exact ctrl_kind_halt hk) hfee hg hg64 ⟨he1, he2⟩
    refine ⟨sN, hsN, hHalt.1, hgN _ _ hHalt hg, E.live, fun x hx => he3 ▸ R.envSep x hx, fun x => ?_⟩
    rw [hHalt.2.1, ← he3]
    simp only [stepLive, List.not_mem_nil, not_false_eq_true, and_true, or_false]
    exact R.live x
  · -- HALTIF: br_if to the function label
    obtain ⟨l, rfl, hl'⟩ := ctrl_kind_hif hk
    have hw : rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 := by omega
    obtain ⟨hmC, sc, h1, ec, hN, hval⟩ := hcnd l hins hw
    have i1 : (if rowNat tr 8 r 7 + rowNat tr 8 r 9 = 1 then [mC] else []) = [mC] := by simp [hw]
    rw [i1]
    by_cases hz : rowNat tr 8 r 11 + rowNat tr 8 r 12 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), cast_zero] at hN
      have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + (pc + 1) : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, hN, c1F]; simp only [Lean.Grind.Semiring.natCast_add, cast_one]; grind)
      have o2 : _ := (show cc 8 + cc 9 * N = ((0 : Nat) : F) by rw [k8, k9, hN, cast_zero]; grind)
      refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, mkOut _ _ o1 o2,
        fun hg => ⟨fun _ => (step_haltIf X R (by rw [hlen]; exact hl') hins hfee hg hg64 (by obtain ⟨a, b, -⟩ := hent (by omega); exact ⟨a, b⟩) mC hmC sc).2 (hval.mpr hz),
          fun h => absurd h (by decide)⟩⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hz), cast_one] at hN
      have o1 : _ := (show cc 5 * (cc 0 + 1) + cc 6 * cc 10 + cc 7 * (N * cc 10 + (1 - N) * (cc 0 + 1)) + cc 8 * cc 0 + cc 9 * (N * cc 0 + (1 - N) * (cc 0 + 1)) = (((X.offOf E.k + pc : Nat) : Nat) : F) by rw [k5, k6, k7, k8, k9, hN, c1F]; grind)
      have o2 : _ := (show cc 8 + cc 9 * N = ((1 : Nat) : F) by rw [k8, k9, hN, cast_one]; grind)
      refine ⟨E.k, pc, fee, 1, E.sb, E.cid, hfl, Nat.le_refl _, mkOut _ _ o1 o2, fun hg => ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
      obtain ⟨sN, hsN, hHalt⟩ := (step_haltIf X R (by rw [hlen]; exact hl') hins hfee hg hg64 (by obtain ⟨a, b, -⟩ := hent (by omega); exact ⟨a, b⟩) mC hmC sc).1 (fun h => hz (hval.mp h))
      obtain ⟨-, -, he3⟩ := hent (by omega)
      refine ⟨sN, hsN, hHalt.1, hgN _ _ hHalt hg, E.live, fun x hx => he3 ▸ R.envSep x hx, fun x => ?_⟩
      rw [hHalt.2.1, ← ctrl_view_pop _ _ (by omega) x, ← ec, ← he3]
      simp only [stepLive, List.mem_singleton, List.not_mem_nil, or_false]
      rw [R.live x]
      constructor
      · rintro ⟨hs | hl | he, hne⟩
        · exact Or.inl ⟨hs, hne⟩
        · exact Or.inr (Or.inl hl)
        · exact Or.inr (Or.inr he)
      · rintro (⟨hs, hne⟩ | hl | he)
        · exact ⟨Or.inl hs, hne⟩
        · refine ⟨Or.inr (Or.inl hl), fun e => ?_⟩
          subst e
          obtain ⟨j, -, hj⟩ := mem_localView.mp hl
          have := congrArg Msg.space hj
          simp only [mC, enc, Env.lsp] at this; omega
        · refine ⟨Or.inr (Or.inr he), fun e => ?_⟩
          subst e
          exact (R.envSep _ he).1 rfl

end WasmBase

namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

theorem ctrl_count_cases : ∀ i ∈ Ctrl.inters, i.count = Ctrl.act ∨ i.count = Ctrl.cnd := by
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp (show Ctrl.inters.all (fun i => decide (i.count = Ctrl.act ∨
    i.count = Ctrl.cnd)) = true by decide) i hi)

theorem ctrl_count_vals_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Ctrl.table.constraints, e.eval (natRow (rowNat tr 8 r) (tr.row pub 8 r)) = 0) :
    rowNat tr 8 r 5 + rowNat tr 8 r 6 + rowNat tr 8 r 7 + rowNat tr 8 r 8 + rowNat tr 8 r 9 ≤ 1 ∧
    (Ctrl.act.eval (tr.row pub 8 r)).toNat =
      rowNat tr 8 r 5 + rowNat tr 8 r 6 + rowNat tr 8 r 7 + rowNat tr 8 r 8 + rowNat tr 8 r 9 ∧
    (Ctrl.cnd.eval (tr.row pub 8 r)).toNat = rowNat tr 8 r 7 + rowNat tr 8 r 9 := by
  have hP' := P_val
  have hcP : ∀ i, rowNat tr 8 r i < P := rowNat_lt tr 8 r
  obtain ⟨-, -, -, -, -, hsum, -⟩ := ctrl_facts (rowNat tr 8 r) (tr.row pub 8 r) hcP hcon
  refine ⟨hsum, ?_, ?_⟩
  · show (tr.cell 8 r 5 + tr.cell 8 r 6 + tr.cell 8 r 7 + tr.cell 8 r 8 + tr.cell 8 r 9).toNat = _
    rw [cell_cast, cell_cast, cell_cast, cell_cast, cell_cast]
    simp only [← Lean.Grind.Semiring.natCast_add]
    exact Fp.toNat_cast_of_lt (by omega)
  · show (tr.cell 8 r 7 + tr.cell 8 r 9).toNat = _
    rw [cell_cast, cell_cast, ← Lean.Grind.Semiring.natCast_add]
    exact Fp.toNat_cast_of_lt (by omega)

theorem ctrl_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Ctrl.table.constraints, e.eval (natRow (rowNat tr 8 r) (tr.row pub 8 r)) = 0) :
    ∀ i ∈ Ctrl.inters, (i.count.eval (tr.row pub 8 r)).toNat ≤ 1 := by
  obtain ⟨hs, ha, hc⟩ := ctrl_count_vals_of hcon
  intro i hi
  rcases ctrl_count_cases i hi with h | h <;> rw [h] <;> omega

theorem ctrl_count_vals {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 8) :
    rowNat tr 8 r 5 + rowNat tr 8 r 6 + rowNat tr 8 r 7 + rowNat tr 8 r 8 + rowNat tr 8 r 9 ≤ 1 ∧
    (Ctrl.act.eval (tr.row pub 8 r)).toNat =
      rowNat tr 8 r 5 + rowNat tr 8 r 6 + rowNat tr 8 r 7 + rowNat tr 8 r 8 + rowNat tr 8 r 9 ∧
    (Ctrl.cnd.eval (tr.row pub 8 r)).toNat = rowNat tr 8 r 7 + rowNat tr 8 r 9 :=
  ctrl_count_vals_of (table_constr H (by simp [air_len]) hr)

theorem ctrl_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 8) :
    ∀ i ∈ Ctrl.inters, (i.count.eval (tr.row pub 8 r)).toNat ≤ 1 :=
  ctrl_counts_of (table_constr H (by simp [air_len]) hr)

theorem ctrl_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 8)
    (hna : ¬ rowAct Ctrl.table tr pub 8 r) :
    ∀ i ∈ Ctrl.inters, (i.count.eval (tr.row pub 8 r)).toNat ≠ 1 := by
  obtain ⟨hs, ha, hc⟩ := ctrl_count_vals H hr
  have : (Ctrl.act.eval (tr.row pub 8 r)).toNat ≠ 1 := hna
  intro i hi
  rcases ctrl_count_cases i hi with h | h <;> rw [h] <;> omega

end WasmBase
