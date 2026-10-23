import WasmBase.Main.Rows
import WasmBase.StepOps2
/-!
# Row lemma: CONST (`i32.const`, `i64.const`)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

theorem const_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 6) (hact : rowAct Const.table tr pub 6 r) :
    RowFacts X (rowIn Const.table tr pub 6 r) (rowOut Const.table tr pub 6 r)
      (rowCons Const.table tr pub 6 r) (rowProd Const.table tr pub 6 r) := by
  have hP' := P_val
  have ht : 6 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 6 r i < P := rowNat_lt tr 6 r
  -- constraints
  have hcon : ∀ e ∈ Const.table.constraints, e.eval (natRow (rowNat tr 6 r) (tr.row pub 6 r)) = 0 :=
    table_constr H ht hr
  simp only [Const.table, Const.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hcon
  obtain ⟨-, b64, z2, z3⟩ := hcon
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Const.is64, Const.imm] at b64 z2 z3
  have w64 := bool_nat (hcP _) b64
  have a1 : rowNat tr 6 r 5 = 1 := by
    simpa only [rowAct, Const.table, Const.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      v, Expr.eval_col, Trace.row, Const.act, rowNat] using hact
  -- the row's messages
  have hocc : ∀ i ∈ Const.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 6 r)),
      (i.count.eval (tr.row pub 6 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Const.table.inters from hi)
  have cnt : (Expr.eval (tr.row pub 6 r) (v Const.act)).toNat = 1 := by
    simp only [v, Expr.eval_col, Trace.row, Const.act]; exact a1
  have hIn : rowIn Const.table tr pub 6 r =
      [((rowNat tr 6 r 0 : Nat) : F), ((rowNat tr 6 r 1 : Nat) : F), ((rowNat tr 6 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 6 r 11 : Nat) : F), ((rowNat tr 6 r 12 : Nat) : F)] := by
    simp only [rowIn, Const.table, Const.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Const.kSb, Const.kCid, cPc, cTs, cS]
  have hOut : rowOut Const.table tr pub 6 r =
      [((rowNat tr 6 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 6 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 6 r 2 : Nat) : F) + ((rowNat tr 6 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 6 r 11 : Nat) : F), ((rowNat tr 6 r 12 : Nat) : F)] := by
    simp only [rowOut, Const.table, Const.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Const.kSb, Const.kCid, cPc, cTs, cS, cFee]
  have hCons : rowCons Const.table tr pub 6 r = [] := by
    rw [rowCons, rowMsgs_eq]
    simp [Const.table, Const.inters, stdState, stateIn, stateOut, fetch, stkSend, chSend, busState, busFetch, busStk]
  have hProd : rowProd Const.table tr pub 6 r =
      [⟨0, (((rowNat tr 6 r 11 : Nat) : F) + ((rowNat tr 6 r 3 : Nat) : F)).toNat, rowNat tr 6 r 6, rowNat tr 6 r 7, rowNat tr 6 r 8, rowNat tr 6 r 9, rowNat tr 6 r 10,
        rowNat tr 6 r 1⟩] := by
    rw [rowProd, rowMsgs_eq]
    simp only [Const.table, Const.inters, stdState, stateIn, stateOut, fetch, stkSend, chSend, List.cons_append,
      List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch, busStk]
    simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide, false_and,
      decide_false, Bool.false_eq_true, ite_false, true_and, decide_true, ite_true, List.filterMap_cons,
      List.filterMap_nil, cnt, List.map_cons, List.map_nil]
    simp only [limbsOf, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat', cell_cast, Trace.row, Const.kSb, Const.kCid, cH, cTs,
      Const.is64, Const.imm, Nat.reduceAdd]
    simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (hcP _),
      Fp.toNat_cast_of_lt (show (0 : Nat) < P by omega)]
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Const.op (v cH) (v cFee) (limbsOf Const.imm) (v Const.act))
    (by simp [Const.inters, stdState])
  simp only [fetch, cnt] at hfetch
  -- gas facts need the record; get the pc first
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  have hrec := fetch_rec hpub L hfetch hm0 hpc0
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := hrec
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  rw [hre] at hm
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, limbsOf, List.range,
    List.range.loop, v, Expr.eval_col, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cell_cast, Trace.row, Const.kSb, Const.kCid,
    cPc, cH, cFee, Const.op, Const.is64, Const.imm, Nat.reduceAdd, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, ex0, ex1, ex2, ex3⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 6 r 4 = fee := natEq efee (hcP _) (by omega)
  refine ⟨?_, by rw [hIn]; rfl, ?_, ⟨fee, hfl, ?_⟩, by rw [hCons]; simp, ?_, by rw [hProd]; simp⟩
  rotate_left
  · rw [hIn, hOut]; rfl
  · rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']
  · rw [hProd, hIn]; simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, lvl,
      List.getD_cons_succ, List.getD_cons_zero]; exact ⟨hcP _, trivial⟩
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin _ ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have p0 : rowNat tr 6 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 6 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 6 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 6 r 11 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 6 r 12 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
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
  have p3 : rowNat tr 6 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  -- the operation: op = 0x41 + is64
  have hop : op = 0x41 + rowNat tr 6 r 6 := by
    have hlt := recordOf_op_lt hrc
    rw [hre] at hlt; simp only [List.getD_cons_succ, List.getD_cons_zero] at hlt
    rw [← Lean.Grind.Semiring.natCast_add] at eop
    exact (natEq eop (by omega) (by omega)).symm
  have hout : rowOut Const.table tr pub 6 r = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hCons, hProd]
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  have hx : ∀ x : Nat, x < 65536 → ∀ y, ((y : Nat) : F) = ((x : Nat) : F) → y < P → y = x :=
    fun x hx y hy hyP => natEq hy hyP (by omega)
  have q : ∀ (x0 x1 x2 x3 : Nat) (n : Nat), n < 2 ^ 64 → [x0, x1, x2, x3] = limbs4 n →
      ((rowNat tr 6 r 7 : Nat) : F) = ((x0 : Nat) : F) → ((rowNat tr 6 r 8 : Nat) : F) = ((x1 : Nat) : F) →
      ((rowNat tr 6 r 9 : Nat) : F) = ((x2 : Nat) : F) → ((rowNat tr 6 r 10 : Nat) : F) = ((x3 : Nat) : F) →
      rowNat tr 6 r 7 = n % 65536 ∧ rowNat tr 6 r 8 = n / 65536 % 65536 ∧ rowNat tr 6 r 9 = n / 2 ^ 32 % 65536 ∧
        rowNat tr 6 r 10 = n / 2 ^ 48 % 65536 := by
    intro x0 x1 x2 x3 n hn hl e0 e1 e2 e3
    simp only [limbs4, List.cons.injEq, and_true] at hl
    obtain ⟨l0, l1, l2, l3⟩ := hl
    subst l0 l1 l2 l3
    exact ⟨natEq e0 (hcP _) (by omega), natEq e1 (hcP _) (by omega), natEq e2 (hcP _) (by omega),
      natEq e3 (hcP _) (by omega)⟩
  rcases w64 with g | g <;> rw [g] at hop <;>
  rcases hcase with ⟨v, hv, h, hl⟩ | ⟨v, hv, h, hl⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
  all_goals first
    | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
    | (exfalso; omega)
    | (exfalso; rw [hop] at hf; revert hf; decide)
    | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
    | (exfalso; simp only [opCall] at h; omega)
    | skip
  · -- i32.const
    have hvl := v.toNat_lt
    obtain ⟨q7, q8, q9, q10⟩ := q x0 x1 x2 x3 v.toNat (by omega) hl ex0 ex1 ex2 ex3
    obtain ⟨s', hs', hrel⟩ := step_const X R (Or.inl ⟨v, hv, rfl⟩) hins hfee hg hg64
      ⟨0, (((rowNat tr 6 r 11 : Nat) : F) + ((rowNat tr 6 r 3 : Nat) : F)).toNat, rowNat tr 6 r 6, rowNat tr 6 r 7, rowNat tr 6 r 8, rowNat tr 6 r 9, rowNat tr 6 r 10,
        rowNat tr 6 r 1⟩ (by simp only [enc, vTag, vNum]; rw [slot_toNat0 psb p3 hsbR hszP, g, q7, q8, q9, q10, p1])
    exact ⟨s', hs', hrel⟩
  · -- i64.const
    have hvl := v.toNat_lt
    obtain ⟨q7, q8, q9, q10⟩ := q x0 x1 x2 x3 v.toNat hvl hl ex0 ex1 ex2 ex3
    obtain ⟨s', hs', hrel⟩ := step_const X R (Or.inr ⟨v, hv, rfl⟩) hins hfee hg hg64
      ⟨0, (((rowNat tr 6 r 11 : Nat) : F) + ((rowNat tr 6 r 3 : Nat) : F)).toNat, rowNat tr 6 r 6, rowNat tr 6 r 7, rowNat tr 6 r 8, rowNat tr 6 r 9, rowNat tr 6 r 10,
        rowNat tr 6 r 1⟩ (by simp only [enc, vTag, vNum]; rw [slot_toNat0 psb p3 hsbR hszP, g, q7, q8, q9, q10, p1])
    exact ⟨s', hs', hrel⟩

end WasmBase

namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

theorem const_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Const.table.constraints, e.eval (natRow (rowNat tr 6 r) (tr.row pub 6 r)) = 0) :
    ∀ i ∈ Const.inters, (i.count.eval (tr.row pub 6 r)).toNat ≤ 1 := by
  simp only [Const.table, Const.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hcon
  obtain ⟨bAct, -, -, -⟩ := hcon
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Const.act] at bAct
  have hb := bool_nat (rowNat_lt _ _ _ _) bAct
  intro i hi
  have hc : i.count = v Const.act :=
    of_decide_eq_true (List.all_eq_true.mp
      (show Const.inters.all (fun i => decide (i.count = v Const.act)) = true by decide) i hi)
  rw [hc]
  simp only [v, Expr.eval_col, Trace.row, Const.act]
  show rowNat tr 6 r 5 ≤ 1
  omega

theorem const_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 6) :
    ∀ i ∈ Const.inters, (i.count.eval (tr.row pub 6 r)).toNat ≤ 1 :=
  const_counts_of (table_constr H (by simp [air_len]) hr)

theorem const_inactive {pub : List F} {tr : Trace} {r : Nat}
    (hna : ¬ rowAct Const.table tr pub 6 r) :
    ∀ i ∈ Const.inters, (i.count.eval (tr.row pub 6 r)).toNat ≠ 1 := by
  intro i hi
  have hc : i.count = v Const.act :=
    of_decide_eq_true (List.all_eq_true.mp
      (show Const.inters.all (fun i => decide (i.count = v Const.act)) = true by decide) i hi)
  rw [hc]
  simpa [rowAct, Const.table, Const.inters, stdState, stateIn] using hna

end WasmBase
