import WasmBase.M2Air
import WasmBase.Main.Rows
import WasmBase.StepOps2
/-!
# WasmBase.Main.M2Link — the E2E M2 chips against the spec interpreter

`WasmBase/M2Air.lean` adds CONV (conversions) and UNREACH (`unreachable`) to `wasmBaseIfRegAir`.
This file proves what each row means in terms of `NearSpecV3.Wasm.exec`/`execNum`.

## Proved (standard axioms only)

* **Spec side.**
  * `extendS_64_32` — `Num.extendS 64 32 n` is `n + (2^64 − 2^32)` when bit 31 is set, `n` otherwise;
  * `execNum_conv` — the spec's three conversion arms are one function `convVal` of the popped value;
  * `exec_unreachable` — `unreachable` aborts with `WasmTrap(Unreachable)`, leaving the state as is.
* **Arithmetic core.** `conv_limbs` — the four output limbs CONV sends,
  `[a0, a1, 65535·sgn·f_exts, 65535·sgn·f_exts]` with tag `f_extu + f_exts`, are the limbs of
  `convVal op v` whenever the consumed limbs are those of `v` (and `sgn`/`rl` split limb 1 as the
  constraint and the R16 lookup force).
* **Row side.**
  * `conv_row_facts` — on a CONV row whose constraints hold and whose `act` is 1: the flags are
    one-hot, an extend's input has zero upper limbs, and for `extend_s` limb 1 is `2^15·sgn + rl`
    with `sgn ∈ {0, 1}`;
  * `conv_row_cons`, `conv_row_prod` — the row's consumed and produced CH messages, decoded;
  * `conv_row_spec` — **join**: on an active CONV row with its R16 query `2·rl` 16-bit, if the
    consumed message is `enc 0 i v tp` then the produced one is `enc 0 i (convVal op v) ts`, where
    `op = 0xA7·f_wrap + 0xAD·f_extu + 0xAC·f_exts` is the opcode its FETCH query carries;
  * `unreach_row` — an active UNREACH row consumes and produces no CH message and sends the STATE
    message with `halted = 2`.
* **REG-C (refill).** `regc_clear_cancels` — a clear row's two new receives are REG's two space-6
  sends (same messages, counts times `clr`), so a clear row consumes the old message and leaves
  nothing; `regc_clear_next` — a clear group's length row is followed by an active fill row of the
  same register, time and host id.
* **Step.** `step_conv` — the spec step of a conversion from a `RelW` state, given the successor
  facts the M2 checker verifies at that pc (`verifyAtM2`'s `.num` arm: same labels, same height).

## Open (named)

* An M2 `Ctx`: `wasm_base_sound`'s context is built from `check`'s facts (`CheckFacts`), which
  `checkModuleM2` does not produce at conversion, `unreachable`, `if (result)` and `ed25519` pcs.
  The M2 instance of the segment theorem (the row-to-step dispatch over 30 tables) is the remaining
  step; `step_conv` takes the successor facts as hypotheses for that reason.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Spec side -/

/-- The value a conversion pushes, from the popped value `v` (`execNum`'s 0xA7/0xAC/0xAD arms). -/
def convVal (op : Nat) (v : Val) : Val :=
  if op = 0xA7 then .i32 (UInt32.ofNat (vNum v % 2 ^ 32))
  else if op = 0xAC then .i64 (UInt64.ofNat (Num.extendS 64 32 (vNum v)))
  else .i64 (UInt64.ofNat (vNum v))

theorem isConvOp_cases {op : Nat} (h : isConvOp op = true) : op = 0xA7 ∨ op = 0xAC ∨ op = 0xAD := by
  simp only [isConvOp, Bool.or_eq_true, beq_iff_eq] at h
  omega

theorem convVal_num (op : Nat) (v : Val) : isNum (convVal op v) := by
  unfold convVal; split
  · trivial
  · split <;> trivial

/-- **The spec's conversions** are `convVal` of the popped value. -/
theorem execNum_conv (s : St) (op : Nat) (hop : isConvOp op = true) :
    execNum s op = .ok (pushV { s with stack := s.stack.pop } (convVal op (s.stack.back?.getD (.i32 0)))) := by
  rcases isConvOp_cases hop with rfl | rfl | rfl <;>
    simp [execNum, convVal, popN_eq, pushI32, pushI64] <;> rfl

/-- Sign extension from 32 to 64 bits, in closed form. -/
theorem extendS_64_32 (n : Nat) (hn : n < 2 ^ 32) :
    Num.extendS 64 32 n = if 2 ^ 31 ≤ n then n + (2 ^ 64 - 2 ^ 32) else n := by
  unfold Num.extendS Num.signed Num.wrap
  rw [Nat.mod_eq_of_lt hn]
  by_cases h : 2 ^ 31 ≤ n
  · rw [if_pos (by simpa using h), if_pos h]; omega
  · rw [if_neg (by simpa using h), if_neg h]; omega

theorem convVal_wrap (x : UInt64) : convVal 0xA7 (.i64 x) = .i32 (UInt32.ofNat (x.toNat % 2 ^ 32)) := by
  simp [convVal, vNum]
theorem convVal_extu (x : UInt32) : convVal 0xAD (.i32 x) = .i64 (UInt64.ofNat x.toNat) := by
  simp [convVal, vNum]
theorem convVal_exts (x : UInt32) :
    convVal 0xAC (.i32 x) = .i64 (UInt64.ofNat (Num.extendS 64 32 x.toNat)) := by
  simp [convVal, vNum]

/-- `unreachable` aborts (`WasmTrap(Unreachable)`) without changing the state. -/
theorem exec_unreachable (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) :
    exec cfg p s f pf .unreachable = .abort s (trapStr "Unreachable") := by
  simp [exec]

/-! ## The arithmetic core -/

/-- **CONV's limbs are the spec conversion.**  `fw, fu, fs` are the one-hot flags, `a0..a3` the
consumed limbs of `v` (tag `fw`), and for `extend_s` limb 1 is `2^15·sg + rl` with `rl < 2^15`. -/
theorem conv_limbs {op : Nat} {v : Val} {fw fu fs a0 a1 a2 a3 sg rl : Nat}
    (hv : isNum v) (hflag : (fw = 1 ∧ fu = 0 ∧ fs = 0 ∧ op = 0xA7) ∨ (fw = 0 ∧ fu = 1 ∧ fs = 0 ∧ op = 0xAD) ∨
      (fw = 0 ∧ fu = 0 ∧ fs = 1 ∧ op = 0xAC))
    (htag : vTag v = fw)
    (h0 : a0 = vNum v % 65536) (h1 : a1 = vNum v / 65536 % 65536)
    (h2 : a2 = vNum v / 2 ^ 32 % 65536) (h3 : a3 = vNum v / 2 ^ 48 % 65536)
    (hs : fs = 1 → a1 = 32768 * sg + rl ∧ sg ≤ 1 ∧ rl < 32768) :
    vTag (convVal op v) = fu + fs ∧ a0 = vNum (convVal op v) % 65536 ∧
      a1 = vNum (convVal op v) / 65536 % 65536 ∧
      65535 * sg * fs = vNum (convVal op v) / 2 ^ 32 % 65536 ∧
      65535 * sg * fs = vNum (convVal op v) / 2 ^ 48 % 65536 := by
  cases v with
  | i32 x =>
    have hx := x.toNat_lt
    simp only [vTag, vNum] at htag h0 h1 h2 h3 ⊢
    rcases hflag with ⟨rfl, -, -, -⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
    · omega
    · rw [convVal_extu]
      simp only [vTag, vNum, UInt64.toNat_ofNat']
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega
    · obtain ⟨e1, hsg, hrl⟩ := hs rfl
      rw [convVal_exts]
      simp only [vTag, vNum, UInt64.toNat_ofNat']
      rw [extendS_64_32 _ hx]
      refine ⟨by first | trivial | rfl, ?_⟩
      by_cases hb : 2 ^ 31 ≤ x.toNat
      · rw [if_pos hb]
        have hs1 : sg = 1 := by omega
        subst hs1
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
      · rw [if_neg hb]
        have hs0 : sg = 0 := by omega
        subst hs0
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  | i64 x =>
    have hx := x.toNat_lt
    simp only [vTag, vNum] at htag h0 h1 h2 h3 ⊢
    rcases hflag with ⟨-, rfl, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [convVal_wrap]
      simp only [vTag, vNum, UInt32.toNat_ofNat']
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega
    · omega
    · omega
  | f32 _ => exact absurd hv id
  | f64 _ => exact absurd hv id
  | ref _ => exact absurd hv id

/-! ## Row side -/

/-- Cell values of a row as naturals. -/
abbrev cn (tr : Trace) (t r i : Nat) : Nat := rowNat tr t r i

theorem conv_col_eval (tr : Trace) (pub : List F) (t r i : Nat) :
    (v i).eval (tr.row pub t r) = ((cn tr t r i : Nat) : F) := by
  simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]

/-- **CONV's constraints, as natural-number facts.** -/
theorem conv_row_facts {tr : Trace} {pub : List F} {t r : Nat}
    (hc : ∀ e ∈ Conv.table.constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0)
    (hact : (Conv.act.eval (tr.row pub t r)).toNat = 1) :
    ((cn tr t r Conv.fWrap = 1 ∧ cn tr t r Conv.fExtU = 0 ∧ cn tr t r Conv.fExtS = 0) ∨
      (cn tr t r Conv.fWrap = 0 ∧ cn tr t r Conv.fExtU = 1 ∧ cn tr t r Conv.fExtS = 0) ∨
      (cn tr t r Conv.fWrap = 0 ∧ cn tr t r Conv.fExtU = 0 ∧ cn tr t r Conv.fExtS = 1)) ∧
    (cn tr t r Conv.fWrap = 0 → cn tr t r (Conv.a + 2) = 0 ∧ cn tr t r (Conv.a + 3) = 0) ∧
    (cn tr t r Conv.sgn ≤ 1) ∧
    (cn tr t r Conv.fExtS = 1 →
      ((cn tr t r (Conv.a + 1) : Nat) : F) = ((32768 * cn tr t r Conv.sgn + cn tr t r Conv.rl : Nat) : F)) := by
  simp only [Conv.table, Conv.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hc
  obtain ⟨bw, bu, bs, -, bsg, z2, z3, es⟩ := hc
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Conv.fWrap, Conv.fExtU, Conv.fExtS, Conv.a, Conv.sgn, Conv.rl] at bw bu bs bsg z2 z3 es
  have hP := rowNat_lt tr t r
  have w := bool_nat (hP _) bw
  have u := bool_nat (hP _) bu
  have s := bool_nat (hP _) bs
  have g := bool_nat (hP _) bsg
  have ha : cn tr t r 5 + cn tr t r 6 + cn tr t r 7 = 1 := by
    simp only [Conv.act, Chips.v, Expr.eval_add', Expr.eval_col, Trace.row, cell_cast] at hact
    rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add,
      Fp.toNat_cast_of_lt (by
        have := w; have := u; have := s
        try simp only [cn, Conv.fWrap, Conv.fExtU, Conv.fExtS] at *
        rw [P_val]; omega)] at hact
    exact hact
  refine ⟨by simp only [cn, Conv.fWrap, Conv.fExtU, Conv.fExtS] at *; omega, ?_, by
    simp only [cn, Conv.sgn]; omega, ?_⟩
  · intro h0
    simp only [cn, Conv.fWrap, Conv.a] at h0 ⊢
    rw [h0] at z2 z3
    exact ⟨zero_of_sel0 (hP _) z2, zero_of_sel0 (hP _) z3⟩
  · intro h1
    simp only [cn, Conv.fExtS, Conv.a, Conv.sgn, Conv.rl] at h1 ⊢
    rw [h1] at es
    have : ((rowNat tr t r (8 + 1) : Nat) : F) =
        ((32768 : Nat) : F) * ((rowNat tr t r 14 : Nat) : F) + ((rowNat tr t r 15 : Nat) : F) := by
      have e1 : ((1 : Nat) : F) = 1 := rfl
      rw [e1] at es; grind
    rw [this]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

/-- The consumed CH message of an active CONV row. -/
theorem conv_row_cons {tr : Trace} {pub : List F} {t r : Nat}
    (hact : (Conv.act.eval (tr.row pub t r)).toNat = 1) :
    rowCons Conv.table tr pub t r =
      [decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub t r), ((cn tr t r Conv.fWrap : Nat) : F),
        ((cn tr t r Conv.a : Nat) : F), ((cn tr t r (Conv.a + 1) : Nat) : F),
        ((cn tr t r (Conv.a + 2) : Nat) : F), ((cn tr t r (Conv.a + 3) : Nat) : F),
        ((cn tr t r Conv.ta : Nat) : F)]] := by
  unfold rowCons
  rw [rowMsgs_eq]
  simp only [Conv.table, Conv.inters, stdState, stateIn, stateOut, fetch, stkRecv, stkSend, chRecv, chSend,
    timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
    busStk, busR16]
  simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide,
    show (3 : Nat) = 2 ↔ False by decide, false_and, decide_false, Bool.false_eq_true, ite_false,
    true_and, and_true, decide_true, ite_true, and_false, List.filterMap_cons, List.filterMap_nil, hact,
    List.map_cons, List.map_nil, limbsOf, List.range, List.range.loop, Expr.eval_ofNat', Conv.tagIn,
    List.cons_append, List.nil_append, Nat.add_zero, Bool.true_eq_false, decide_false,
    List.filterMap_nil,
    conv_col_eval, Nat.reduceAdd]

/-- The produced CH message of an active CONV row. -/
theorem conv_row_prod {tr : Trace} {pub : List F} {t r : Nat}
    (hact : (Conv.act.eval (tr.row pub t r)).toNat = 1) :
    rowProd Conv.table tr pub t r =
      [decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub t r),
        ((cn tr t r Conv.fExtU : Nat) : F) + ((cn tr t r Conv.fExtS : Nat) : F),
        ((cn tr t r Conv.a : Nat) : F), ((cn tr t r (Conv.a + 1) : Nat) : F),
        ((65535 : Nat) : F) * ((cn tr t r Conv.sgn : Nat) : F) * ((cn tr t r Conv.fExtS : Nat) : F),
        ((65535 : Nat) : F) * ((cn tr t r Conv.sgn : Nat) : F) * ((cn tr t r Conv.fExtS : Nat) : F),
        ((cn tr t r cTs : Nat) : F)]] := by
  unfold rowProd
  rw [rowMsgs_eq]
  simp only [Conv.table, Conv.inters, stdState, stateIn, stateOut, fetch, stkRecv, stkSend, chRecv, chSend,
    timeChk, r16, List.cons_append, List.nil_append, List.filter_cons, List.filter_nil, busState, busFetch,
    busStk, busR16]
  simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide,
    show (3 : Nat) = 2 ↔ False by decide, false_and, decide_false, Bool.false_eq_true, ite_false,
    true_and, and_true, decide_true, ite_true, and_false, List.filterMap_cons, List.filterMap_nil, hact,
    List.map_cons, List.map_nil, Conv.outLimbs, Conv.hiOut, Conv.tagOut, Expr.eval_ofNat', Expr.eval_add',
    Expr.eval_mul', conv_col_eval, Nat.reduceAdd, List.cons_append, List.nil_append]

/-- **Join: an active CONV row produces the spec conversion of what it consumes.** -/
theorem conv_row_spec {tr : Trace} {pub : List F} {t r : Nat}
    (hc : ∀ e ∈ Conv.table.constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0)
    (hact : (Conv.act.eval (tr.row pub t r)).toNat = 1)
    (hr16 : cn tr t r Conv.fExtS = 1 → (2 * cn tr t r Conv.rl) % P < 65536)
    {i tp : Nat} {x : Val} (hx : isNum x)
    (hin : decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub t r), ((cn tr t r Conv.fWrap : Nat) : F),
        ((cn tr t r Conv.a : Nat) : F), ((cn tr t r (Conv.a + 1) : Nat) : F),
        ((cn tr t r (Conv.a + 2) : Nat) : F), ((cn tr t r (Conv.a + 3) : Nat) : F),
        ((cn tr t r Conv.ta : Nat) : F)] = enc 0 i x tp) :
    rowCons Conv.table tr pub t r = [enc 0 i x tp] ∧
    rowProd Conv.table tr pub t r =
      [enc 0 i (convVal (0xA7 * cn tr t r Conv.fWrap + 0xAD * cn tr t r Conv.fExtU + 0xAC * cn tr t r Conv.fExtS) x)
        (cn tr t r cTs)] := by
  refine ⟨by rw [conv_row_cons hact, hin], ?_⟩
  rw [conv_row_prod hact]
  obtain ⟨hfl, hz, hsg, hes⟩ := conv_row_facts hc hact
  have hP := rowNat_lt tr t r
  have hP' := P_val
  simp only [decMsg, enc, List.getD_cons_zero, List.getD_cons_succ, Msg.mk.injEq] at hin
  rw [Fp.toNat_cast_of_lt (hP _), Fp.toNat_cast_of_lt (hP _), Fp.toNat_cast_of_lt (hP _),
    Fp.toNat_cast_of_lt (hP _), Fp.toNat_cast_of_lt (hP _), Fp.toNat_cast_of_lt (hP _)] at hin
  obtain ⟨-, hi, htg, e0, e1, e2, e3, etp⟩ := hin
  -- the `extend_s` split of limb 1, in the naturals
  have hs : cn tr t r Conv.fExtS = 1 →
      cn tr t r (Conv.a + 1) = 32768 * cn tr t r Conv.sgn + cn tr t r Conv.rl ∧ cn tr t r Conv.sgn ≤ 1 ∧
        cn tr t r Conv.rl < 32768 := by
    intro h1
    have hrl := hr16 h1
    have e := hes h1
    have hl1 : cn tr t r (Conv.a + 1) < 65536 := by
      have : vNum x / 65536 % 65536 < 65536 := Nat.mod_lt _ (by decide)
      simp only [cn, Conv.a] at e1 ⊢; omega
    have hrl' : cn tr t r Conv.rl < 32768 := by
      have hlt := hP Conv.rl
      have hr := hrl
      have hl := hl1
      simp only [cn] at hlt hr hl e ⊢
      rw [P_val] at hlt hr
      have hq : rowNat tr t r Conv.rl < 1006665729 := by
        by_cases h2 : 2 * rowNat tr t r Conv.rl < 2013265921
        · rw [Nat.mod_eq_of_lt h2] at hr; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hr; omega
      refine Nat.lt_of_not_le fun hcon => ?_
      have hsmall : 32768 * rowNat tr t r Conv.sgn + rowNat tr t r Conv.rl < P := by
        simp only [cn] at hsg; rw [P_val]; omega
      have := natEq e (hP _) hsmall
      by_cases h2 : 2 * rowNat tr t r Conv.rl < 2013265921
      · rw [Nat.mod_eq_of_lt h2] at hr; omega
      · omega
    exact ⟨natEq e (hP _) (by simp only [cn] at *; omega), hsg, hrl'⟩
  have hflag : (cn tr t r Conv.fWrap = 1 ∧ cn tr t r Conv.fExtU = 0 ∧ cn tr t r Conv.fExtS = 0 ∧
        0xA7 * cn tr t r Conv.fWrap + 0xAD * cn tr t r Conv.fExtU + 0xAC * cn tr t r Conv.fExtS = 0xA7) ∨
      (cn tr t r Conv.fWrap = 0 ∧ cn tr t r Conv.fExtU = 1 ∧ cn tr t r Conv.fExtS = 0 ∧
        0xA7 * cn tr t r Conv.fWrap + 0xAD * cn tr t r Conv.fExtU + 0xAC * cn tr t r Conv.fExtS = 0xAD) ∨
      (cn tr t r Conv.fWrap = 0 ∧ cn tr t r Conv.fExtU = 0 ∧ cn tr t r Conv.fExtS = 1 ∧
        0xA7 * cn tr t r Conv.fWrap + 0xAD * cn tr t r Conv.fExtU + 0xAC * cn tr t r Conv.fExtS = 0xAC) := by
    rcases hfl with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨a, b, c, by rw [a, b, c]⟩
    · exact Or.inr (Or.inl ⟨a, b, c, by rw [a, b, c]⟩)
    · exact Or.inr (Or.inr ⟨a, b, c, by rw [a, b, c]⟩)
  obtain ⟨gt, g0, g1, g2, g3⟩ := conv_limbs hx hflag htg.symm e0 e1 e2 e3 hs
  have hb : cn tr t r Conv.fExtU + cn tr t r Conv.fExtS ≤ 1 := by
    rcases hfl with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
  have hh : 65535 * cn tr t r Conv.sgn * cn tr t r Conv.fExtS < P := by
    have : cn tr t r Conv.fExtS ≤ 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 65535 hsg) this
    omega
  simp only [decMsg, enc, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true]
  rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_mul,
    ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (hP _), Fp.toNat_cast_of_lt (hP _),
    Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt hh, Fp.toNat_cast_of_lt (hP _)]
  rw [← hi, gt, ← g0, ← g1, ← g2, ← g3]
  rw [Fp.toNat_cast_of_lt (show cn tr t r Conv.fExtU + cn tr t r Conv.fExtS < P by rw [P_val]; omega)]

/-- **UNREACH**: an active row consumes and produces no value and ends the run with `halted = 2`. -/
theorem unreach_row {tr : Trace} {pub : List F} {t r : Nat}
    (hact : ((v Unreach.act).eval (tr.row pub t r)).toNat = 1) :
    rowCons Unreach.table tr pub t r = [] ∧ rowProd Unreach.table tr pub t r = [] ∧
    rowOut Unreach.table tr pub t r =
      [((cn tr t r cPc : Nat) : F) + 1, ((cn tr t r cTs : Nat) : F) + 1,
       ((cn tr t r cS : Nat) : F) + ((cn tr t r cFee : Nat) : F), ((2 : Nat) : F),
       ((cn tr t r Unreach.kSb : Nat) : F), ((cn tr t r Unreach.kCid : Nat) : F)] := by
  refine ⟨?_, ?_, ?_⟩
  · unfold rowCons; rw [rowMsgs_eq]
    simp [Unreach.table, Unreach.inters, stateIn, stateOut, fetch, busState, busFetch, busStk]
  · unfold rowProd; rw [rowMsgs_eq]
    simp [Unreach.table, Unreach.inters, stateIn, stateOut, fetch, busState, busFetch, busStk]
  · simp only [rowOut, Unreach.table, Unreach.inters, stateOut, List.getD_cons_succ, List.getD_cons_zero,
      List.map_cons, List.map_nil, Expr.eval_add', Expr.eval_ofNat', conv_col_eval]
    rfl

/-! ## REG-C: the clear group of a refill -/

/-- **A clear row cancels its own re-production.**  REG-C's two new receives carry exactly the
messages of REG's two space-6 sends (same slot, tag, value and time `ts`), with the counts multiplied
by `clr`; so on a clear row (`clr = 1`) each register message the row produces is consumed by the same
row, and the row's net effect on space 6 is the consumption of the old message (`cReadFresh`). -/
theorem regc_clear_cancels :
    (RegC.newInters.map (·.msg)) = ((Reg.inters.take 2).map (·.msg)) ∧
    (RegC.newInters.map (·.count)) =
      ((Reg.inters.take 2).map (fun i => i.count * v RegC.clr)) ∧
    (RegC.newInters.all (fun i => i.bus == busStk && !i.send)) ∧
    ((Reg.inters.take 2).all (fun i => i.bus == busStk && i.send)) := by
  refine ⟨rfl, rfl, by decide, by decide⟩

/-- **A clear group is the first half of a refill.**  On a row with `clr = 1` and `kind = 1` (the
clear group's length row) whose REG-C constraints hold, the next row is an active fill row
(`rd = 0`, `clr = 0`) of the same register, at the same time, for the same host call. -/
theorem regc_clear_next {c : Nat → Nat} {rw : Row}
    (hc : ∀ e ∈ RegC.table.constraints, e.eval (natRow c rw) = 0)
    (hcl : c RegC.clr = 1) (hk : c Reg.kind = 1) :
    rw.nxt Reg.rid = ((c Reg.rid : Nat) : F) ∧ rw.nxt Reg.ts = ((c Reg.ts : Nat) : F) ∧
      rw.nxt Reg.hid = ((c Reg.hid : Nat) : F) ∧ rw.nxt Reg.rd = 0 ∧ rw.nxt RegC.clr = 0 ∧
      rw.nxt Reg.act = 1 := by
  have mem : ∀ e ∈ RegC.newConstraints, e ∈ RegC.table.constraints :=
    fun e he => List.mem_append_right _ he
  have g := fun e he => hc e (mem e he)
  have h1 := g RegC.cClrNxtRid (by simp [RegC.newConstraints])
  have h2 := g RegC.cClrNxtTs (by simp [RegC.newConstraints])
  have h3 := g RegC.cClrNxtHid (by simp [RegC.newConstraints])
  have h4 := g RegC.cClrNxtFill (by simp [RegC.newConstraints])
  have h5 := g RegC.cClrNxtClr (by simp [RegC.newConstraints])
  have h6 := g RegC.cClrNxtAct (by simp [RegC.newConstraints])
  simp only [RegC.cClrNxtRid, RegC.cClrNxtTs, RegC.cClrNxtHid, RegC.cClrNxtFill, RegC.cClrNxtClr,
    RegC.cClrNxtAct, RegC.endC, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', natRow, hcl, hk] at h1 h2 h3 h4 h5 h6
  have one : ((1 : Nat) : F) = 1 := rfl
  simp only [one] at h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-! ## The spec step of a conversion -/

variable {S_seg segb : Nat}

/-- **The spec step of a conversion** from a `RelW` state: it consumes the top stack message `ma`
and produces `enc 0 (n − 1) (convVal op ma.toVal) t` — exactly what `conv_row_spec` says the CONV
row produces.  The successor facts are the M2 checker's (`verifyAtM2`, `.num` arm with
`isConvOp`). -/
theorem step_conv (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {op fee : Nat} (hins : (X.pfOf E.k).code[pc]? = some (.num op)) (hop : isConvOp op = true)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb)
    (hg64 : X.g0 < 2 ^ 64) (hstk : E.sb + 1 ≤ s.stack.size)
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - E.sb))
    (ma mr : Msg) (hma : live ma) (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 1)
    (hmr : mr = enc 0 (s.stack.size - 1) (convVal op ma.toVal) t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [ma] [mr]) S_seg segb := by
  obtain ⟨ea, -, -, vt⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  apply step_straight X R hins hfee hg hg64 1 (by omega) ((popK s.stack 1).push (convVal op ma.toVal)) f.locals none
    (pushpop_keep _ _ _) (by rw [pushpop_size]; omega) (pushpop_num _ _ _ (convVal_num _ _) R.numS)
    rfl (fun _ _ => rfl) (by simp) R.numL hnext hL1 (by rw [pushpop_size]; omega)
    (by rw [pushpop_size, hH1]; congr 1; omega)
  · rw [popK_one]
    simp only [exec, execNum_conv _ _ hop, pushV, setFrame, R.frames, R.pcEq]
    rw [back_getD s.stack (by omega), ← vt]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : d = 0 := by omega
      subst this; rw [ea, Nat.add_zero]
    · rintro rfl; exact ⟨0, by omega, by rw [ea, Nat.add_zero]⟩
  · exact prod_one s.stack 1 (by omega) _ t mr hmr

end WasmBase
