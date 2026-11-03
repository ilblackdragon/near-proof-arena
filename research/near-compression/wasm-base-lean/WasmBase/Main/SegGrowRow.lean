import WasmBase.Main.SegGrowSend
import WasmBase.Main.SegGrowStep
/-!
# WasmBase.Main.SegGrowRow — a MEMG row's STATE and CH messages (E2E M6, GROW)

The trace side of a MEMG row (table 32 of `wasmBaseSegAirG`, M3's table): what an active
`memory.grow` / `memory.size` row consumes and produces on the STATE and CH buses, as the
`step_mem*` lemmas (`Main/SegGrowStep.lean`) and the row-spec premises (`memSize_rowSpecJQ`,
`memGrowOk_rowSpecJQ`, `Main/SegExecQ.lean`) take them:

* `memg_grow_msgs` (`f_grow = 1`): consumes the top operand `[0, sb + h − 1, 0, n0, n1, 0, 0, tn]` and the
  size message `[8, 0, 0, old, 0, 0, 0, tz]`; produces the result `[0, sb + h − 1, 0, r0, r1, 0, 0, ts]`
  and the size message `[8, 0, 0, old + ok·n, 0, 0, 0, ts]`;
* `memg_size_msgs` (`f_size = 1`): consumes the size message, produces `[0, sb + h, 0, old, 0, 0, 0, ts]`
  and the size message re-produced unchanged;
* `memg_grow_ok_dec` / `memg_grow_fail_dec`: the produced values in the naturals — on success the
  result is `old` and the new size `old + n ≤ 2048` (`n = n0 + 2^16·n1`); on failure the result limbs
  are `65535, 65535` (`2^32 − 1`), the size stays `old`, and `old + n > 2048`.

Open: the per-state part of the `AtRow` premises (the slot `sb + h − 1` is the stack top through
`RelW.height` and the FETCH answer `h = heights[pc]`, which needs the `checkModuleM3` context).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- A MEMG column of row `r` (table 32). -/
abbrev mgc (tr : Trace) (r i : Nat) : Nat := rowNat tr 32 r i

theorem memg_col_eval (tr : Trace) (pub : List F) (r i : Nat) :
    (v i).eval (tr.row pub 32 r) = ((mgc tr r i : Nat) : F) := by
  simp [v, Expr.eval_col, Trace.row, mgc, rowNat, Fp.cast_toNat]

/-- The CH messages of an active `memory.grow` row (`f_grow = 1`, so `act = 1`, `f_size = 0`). -/
theorem memg_grow_msgs {tr : Trace} {pub : List F} {r : Nat}
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) :
    rowCons MemG.table tr pub 32 r =
      [decMsg [((0 : Nat) : F), ((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F) - 1, ((0 : Nat) : F),
          ((mgc tr r MemG.n0 : Nat) : F), ((mgc tr r MemG.n1 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
          ((mgc tr r MemG.tn : Nat) : F)],
       decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.old : Nat) : F),
          ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.tz : Nat) : F)]] ∧
    rowProd MemG.table tr pub 32 r =
      [decMsg [((0 : Nat) : F), ((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F) - 1, ((0 : Nat) : F),
          ((mgc tr r MemG.ok : Nat) : F) * ((mgc tr r MemG.old : Nat) : F) +
            (((mgc tr r MemG.fGrow : Nat) : F) - ((mgc tr r MemG.ok : Nat) : F)) * ((65535 : Nat) : F),
          (((mgc tr r MemG.fGrow : Nat) : F) - ((mgc tr r MemG.ok : Nat) : F)) * ((65535 : Nat) : F),
          ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r cTs : Nat) : F)],
       decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
          ((mgc tr r MemG.old : Nat) : F) + ((mgc tr r MemG.ok : Nat) : F) *
            (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)),
          ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r cTs : Nat) : F)]] := by
  have one : ((1 : Nat) : F).toNat = 1 := rfl
  have zero : ((0 : Nat) : F).toNat = 0 := rfl
  have hact : (MemG.act.eval (tr.row pub 32 r)).toNat = 1 := by
    simp only [MemG.act, Expr.eval_add', memg_col_eval, hg, hs]; rfl
  constructor
  · unfold rowCons
    rw [rowMsgs_eq]
    simp only [MemG.table, MemG.inters, stateIn, stateOut, fetch, stkRecv, stkSend, chRecv, chSend,
      timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
      busStk, busR16, busGrow]
    simp (config := { decide := true }) only [memg_col_eval, hg, hs, hact, one, zero, Expr.eval_ofNat', Expr.eval_add',
      Expr.eval_sub', Expr.eval_mul', Expr.eval_c, List.filterMap_cons, List.filterMap_nil, List.map_cons,
      List.map_nil, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, and_true, true_and,
      and_false, false_and, List.cons_append, List.nil_append]
    rfl
  · unfold rowProd
    rw [rowMsgs_eq]
    simp only [MemG.table, MemG.inters, stateIn, stateOut, fetch, stkRecv, stkSend, chRecv, chSend,
      timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
      busStk, busR16, busGrow]
    simp (config := { decide := true }) only [memg_col_eval, hg, hs, hact, one, zero, Expr.eval_ofNat', Expr.eval_add',
      Expr.eval_sub', Expr.eval_mul', Expr.eval_c, List.filterMap_cons, List.filterMap_nil, List.map_cons,
      List.map_nil, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, and_true, true_and,
      and_false, false_and, List.cons_append, List.nil_append, MemG.r0, MemG.r1, MemG.newE, MemG.nE]
    rfl

/-- The CH messages of an active `memory.size` row (`f_size = 1`, `f_grow = 0`, hence `ok = 0`). -/
theorem memg_size_msgs {tr : Trace} {pub : List F} {r : Nat}
    (hg : mgc tr r MemG.fGrow = 0) (hs : mgc tr r MemG.fSize = 1) (hok : mgc tr r MemG.ok = 0) :
    rowCons MemG.table tr pub 32 r =
      [decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.old : Nat) : F),
          ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.tz : Nat) : F)]] ∧
    rowProd MemG.table tr pub 32 r =
      [decMsg [((0 : Nat) : F), ((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F), ((0 : Nat) : F),
          ((mgc tr r MemG.old : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
          ((mgc tr r cTs : Nat) : F)],
       decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.old : Nat) : F),
          ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r cTs : Nat) : F)]] := by
  have one : ((1 : Nat) : F).toNat = 1 := rfl
  have zero : ((0 : Nat) : F).toNat = 0 := rfl
  have hact : (MemG.act.eval (tr.row pub 32 r)).toNat = 1 := by
    simp only [MemG.act, Expr.eval_add', memg_col_eval, hg, hs]; rfl
  constructor
  · unfold rowCons
    rw [rowMsgs_eq]
    simp only [MemG.table, MemG.inters, stateIn, stateOut, fetch, stkRecv, stkSend, chRecv, chSend,
      timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
      busStk, busR16, busGrow]
    simp (config := { decide := true }) only [memg_col_eval, hg, hs, hact, one, zero, Expr.eval_ofNat', Expr.eval_add',
      Expr.eval_sub', Expr.eval_mul', Expr.eval_c, List.filterMap_cons, List.filterMap_nil, List.map_cons,
      List.map_nil, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, and_true, true_and,
      and_false, false_and, List.cons_append, List.nil_append]
    rfl
  · unfold rowProd
    rw [rowMsgs_eq]
    simp only [MemG.table, MemG.inters, stateIn, stateOut, fetch, stkRecv, stkSend, chRecv, chSend,
      timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
      busStk, busR16, busGrow]
    simp (config := { decide := true }) only [memg_col_eval, hg, hs, hok, hact, one, zero, Expr.eval_ofNat',
      Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_c, List.filterMap_cons, List.filterMap_nil,
      List.map_cons, List.map_nil, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, and_true,
      true_and, and_false, false_and, List.cons_append, List.nil_append, MemG.r0, MemG.r1, MemG.newE, MemG.nE]
    simp [MemG.szSlot]
    congr 1
    simp only [List.cons.injEq, and_true, true_and]
    grind

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- **A successful `memory.grow` row's messages, decoded**: the result is the `i32` `old`, the new
size message carries `old + n`, with `old + n ≤ 2048` and the operand `n = n0 + 2^16·n1`. -/
theorem memg_grow_ok_dec {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 1) :
    mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ maxPagesM3 ∧
    (rowProd MemG.table tr pub 32 r).map (fun x => (x.l0, x.l1, x.l2)) =
      [(mgc tr r MemG.old, 0, 0), (mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1), 0, 0)] := by
  have hP := P_val
  have e : mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) + mgc tr r MemG.d = maxPagesM3 :=
    segG_grow_ok' H hr hg hok
  have hm : maxPagesM3 = 2048 := rfl
  refine ⟨by omega, ?_⟩
  rw [(memg_grow_msgs hg hs).2]
  simp only [List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, hok, hg,
    List.cons.injEq, Prod.mk.injEq, and_true]
  have c0 : ((1 : Nat) : F) * ((mgc tr r MemG.old : Nat) : F) + (((1 : Nat) : F) - ((1 : Nat) : F)) * ((65535 : Nat) : F)
      = ((mgc tr r MemG.old : Nat) : F) := by grind
  have c1 : (((1 : Nat) : F) - ((1 : Nat) : F)) * ((65535 : Nat) : F) = ((0 : Nat) : F) := by grind
  have c2 : ((mgc tr r MemG.old : Nat) : F) + ((1 : Nat) : F) *
      (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)) =
      ((mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
  rw [c0, c1, c2]
  refine ⟨⟨Fp.toNat_cast_of_lt (by omega), rfl, rfl⟩, Fp.toNat_cast_of_lt (by omega), rfl, rfl⟩

/-- **A failed `memory.grow` row's messages, decoded**: the result limbs are `2^16 − 1, 2^16 − 1`
(`2^32 − 1`), the size message is re-produced as `old`, and `old + n > 2048`. -/
theorem memg_grow_fail_dec {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 0) :
    maxPagesM3 < mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ∧
    (rowProd MemG.table tr pub 32 r).map (fun x => (x.l0, x.l1, x.l2)) =
      [(65535, 65535, 0), (mgc tr r MemG.old, 0, 0)] := by
  have hP := P_val
  have e : mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) =
      maxPagesM3 + 1 + (mgc tr r MemG.e0 + 65536 * mgc tr r MemG.e1) := segG_grow_fail' H hr hg hok
  refine ⟨by omega, ?_⟩
  rw [(memg_grow_msgs hg hs).2]
  simp only [List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, hok, hg,
    List.cons.injEq, Prod.mk.injEq, and_true]
  have c0 : ((0 : Nat) : F) * ((mgc tr r MemG.old : Nat) : F) + (((1 : Nat) : F) - ((0 : Nat) : F)) * ((65535 : Nat) : F)
      = ((65535 : Nat) : F) := by grind
  have c1 : (((1 : Nat) : F) - ((0 : Nat) : F)) * ((65535 : Nat) : F) = ((65535 : Nat) : F) := by grind
  have c2 : ((mgc tr r MemG.old : Nat) : F) + ((0 : Nat) : F) *
      (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)) =
      ((mgc tr r MemG.old : Nat) : F) := by grind
  rw [c0, c1, c2]
  refine ⟨⟨Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), rfl⟩, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), rfl, rfl⟩
end

#print axioms memg_grow_msgs
#print axioms memg_size_msgs
#print axioms memg_grow_ok_dec
#print axioms memg_grow_fail_dec

end WasmBase
