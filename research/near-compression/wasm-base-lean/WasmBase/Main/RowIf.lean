import WasmBase.Main.Rows
import WasmBase.IfCheck
import WasmBase.StepIf
import WasmBase.Local.Simple
/-!
# Row lemma: `IF` — the soundness leg

The facts a single active `IF` row gives, from `Holds (wasmBaseIfAir …)`: its CH traffic (one
condition consumed, nothing produced), its FETCH answer (an `if_` with its false target), the
polarity of its STATE successor, and the spec step it licenses.

`Main/RowCtrl.lean` is the template.  Three differences, each the source of real work:

1. **The polarity is in the STATE successor, not a selector.**  `IfC.pcNext = nz·(pc+1) + (1−nz)·tgt`
   with `nz = [c ≠ 0]`; `CTRL`'s `fJif` is `nz·tgt + (1−nz)·(pc+1)`.
2. **The row always consumes its condition** — there is no inactive `IF` row — so `cons = [mC]` and
   `prod = []` unconditionally, unlike `CTRL` where consumption is gated by `cnd`.
3. **Three successor shapes** (true arm, false with `else`, false without), so the spec branch is a
   three-way case rather than `CTRL`'s five selectors.

## Table index

`IF` is appended last: index `22` in `wasmBaseIfAir`, `26` in `wasmBaseIfHostAir`.  `IF` touches only
STATE(0), CH(2), FETCH(1) and R16(3) — buses whose `Looks` consequences (`fetch_rec`, `time_chk`,
`stMsg_cons`, `slot_toNat`) are all stated for the base AIR — so nothing here needs a host fact and
the lemma transfers to the host AIR with `SegHarness`'s premises substituted.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- `IF` is table 22 of the `if` AIR (23 tables). -/
theorem if_air_len (nloc ncode : Nat) : (wasmBaseIfAir nloc ncode).tables.length = 23 := rfl

theorem if_air_t22 (nloc ncode : Nat) :
    (wasmBaseIfAir nloc ncode).tables[22]'(by simp [if_air_len]) = IfC.table := rfl

/-- The `IF` table's CH receive filter: exactly one receiver, the condition. -/
theorem if_filterC :
    IfC.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)) =
      [stkRecv (v IfC.kSb + v cH - 1) 0 [v IfC.c, v (IfC.c + 1), 0, 0] (v IfC.tc) IfC.act] := by
  decide

/-- The `IF` table produces **nothing** on the value channel: `if` pops and pushes no value. -/
theorem if_filterP : IfC.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) = [] := by
  decide

/-- `recordOf` never yields the `IF` opcode: `0x106` is outside every other chip's opcode range. -/
theorem recordOf_ne_opIf {cof : Nat} {ci : Nat → Option Nat} {ls : List Label} {h fee pc : Nat}
    {ins : Instr} {rec : List Nat} (hr : recordOf cof ci ls h fee pc ins = some rec) :
    rec.getD 1 0 ≠ IfC.opIf := by
  obtain ⟨op, x0, x1, x2, x3, rfl, hc⟩ := recordOf_spec hr
  simp only [List.getD_cons_succ, List.getD_cons_zero, IfC.opIf]
  rcases hc with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ |
    ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ <;>
    first | (subst h; decide) | (have := isFamilyNum_le hf; omega) | omega

/-- **The record of an `IF` row.**  A FETCH answer whose opcode is `opIf` must have come from
`recordAtIf`'s `.if_` arm, so it pins the instruction, `endOf`, `elseOf` and the false target. -/
theorem recordAtIf_opIf {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off : Nat} {cinfo : Nat → Option Nat} {pc : Nat} {rec : List Nat}
    (hr : recordAtIf cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = IfC.opIf) :
    ∃ bt e el fee, pf.code[pc]? = some (.if_ bt) ∧ pf.endOf[pc]? = some e ∧
      pf.elseOf[pc]? = some el ∧ rec = [off + pc, IfC.opIf, H[pc]?.getD 0, fee, el + 1 + off, 0, 0, 0] := by
  unfold recordAtIf at hr
  split at hr
  · rename_i ins fee hins hfee
    -- `hr` is one match over the instruction; case on its three arms
    split at hr
    · -- `.if_`
      split at hr
      · rename_i e el he hel
        simp only [Option.some.injEq] at hr
        exact ⟨_, e, el, fee, hins, he, hel, hr.symm⟩
      · simp at hr
    · -- `.else_`: opcode is `opJump`, so `hop` is false
      split at hr
      · simp only [Option.some.injEq] at hr
        subst hr
        simp only [List.getD_cons_succ, List.getD_cons_zero, IfC.opIf, Ctrl.opJump] at hop
        exact absurd hop (by decide)
      · simp at hr
    · -- everything else: `recordOf` never yields `opIf`
      exact absurd hop (recordOf_ne_opIf hr)
  · simp at hr

/-- `((0 : Nat) : F).toNat = 0`, the form `decMsg` leaves behind for a zero limb. -/
theorem if_toNat_zero_cast : (((0 : Nat) : F)).toNat = 0 := by
  rw [Fp.toNat_cast, Nat.zero_mod]

/-- The `IF` row produces nothing on the value channel. -/
theorem if_rowProd {nloc ncode : Nat} {tr : Trace} {pub : List F} {r : Nat} :
    rowProd IfC.table tr pub 22 r = [] := by
  rw [rowProd, rowMsgs_eq]
  show (List.filterMap _ (IfC.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)))).map decMsg = _
  rw [if_filterP]; rfl

/-- `IfC.act` is the selector, so its natural value is `f_if`'s. -/
theorem if_act_val {nloc ncode : Nat} {pub : List F} {tr : Trace} {r : Nat} :
    (IfC.act.eval (tr.row pub 22 r)).toNat = rowNat tr 22 r IfC.fIf := by
  show (tr.cell 22 r IfC.fIf).toNat = rowNat tr 22 r IfC.fIf
  rw [cell_cast]
  exact Fp.toNat_cast_of_lt (rowNat_lt tr 22 r _)

/-- **The condition is consumed, always.**  `IF` has no inactive row, so its CH receive is the
condition — there is no gating count to case on, unlike `CTRL`'s `cnd`.  `hsl` turns the AIR's
field-arithmetic slot `(sb + h) − 1` into the spec's `size − 1`. -/
theorem if_rowCons {nloc ncode : Nat} {tr : Trace} {pub : List F} {r : Nat}
    (hact : rowAct IfC.table tr pub 22 r)
    (hsl : ((rowNat tr 22 r IfC.kSb : F) + (rowNat tr 22 r cH : F) - 1).toNat
             = (rowNat tr 22 r IfC.kSb + rowNat tr 22 r cH) - 1) :
    rowCons IfC.table tr pub 22 r =
      [⟨0, (rowNat tr 22 r IfC.kSb + rowNat tr 22 r cH) - 1, 0,
        rowNat tr 22 r IfC.c, rowNat tr 22 r (IfC.c + 1), 0, 0, rowNat tr 22 r IfC.tc⟩] := by
  -- The activity hypothesis is literally the `v fIf` count, so it is the filter's guard.
  have hcnt : (Expr.eval (tr.row pub 22 r) IfC.act).toNat = 1 := hact
  rw [rowCons, rowMsgs_eq]
  simp only [IfC.table]
  rw [if_filterC]
  simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv]
  rw [ite_eq_left hcnt]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc,
    List.singleton_append, List.cons.injEq, decMsg, v, Expr.eval_col, Expr.eval_sub',
    Expr.eval_add', Expr.eval_ofNat', cell_cast, Trace.row, IfC.kSb, cH, IfC.c, IfC.tc,
    List.getD_cons_zero, List.getD_cons_succ, Msg.mk.injEq, and_true,
    if_toNat_zero_cast, Fp.toNat_cast_of_lt (rowNat_lt tr 22 r _)]
  simp only [IfC.kSb, cH] at hsl
  exact ⟨trivial, hsl⟩

/-! ## The row's STATE shapes

`IF` has 14 columns: the 5 header columns, `f_if, tgt, c0, c1, tc, hc, inv` (5–11), then the frame
`fr_sb, fr_cid` (12, 13).  The STATE input is `stateIn`, whose message is `[pc, ts, S, 0, sb, cid]`;
the output is `stateOut pcNext (ts+1) (S+fee) 0 sb cid`. -/

/-- The `IF` row's STATE input is the standard state message. -/
theorem if_rowIn {tr : Trace} {pub : List F} {r : Nat} :
    rowIn IfC.table tr pub 22 r =
      [((rowNat tr 22 r 0 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F), ((rowNat tr 22 r 2 : Nat) : F),
        ((0 : Nat) : F), ((rowNat tr 22 r IfC.kSb : Nat) : F), ((rowNat tr 22 r IfC.kCid : Nat) : F)] := by
  simp only [rowIn, IfC.table, IfC.inters, stateIn, List.cons_append, List.append_assoc,
    List.nil_append, List.singleton_append, List.getD_cons_zero, List.map_cons, List.map_nil,
    v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, cPc, cTs, cS]

/-- **The polarity.**  The `IF` row's STATE successor is `nz·(pc+1) + (1−nz)·tgt` — `CTRL`'s `fJif`
is the opposite (`nz·tgt + (1−nz)·(pc+1)`), so this is the one place `IF` cannot be copied from
`CTRL`.  The non-zero witness is written in place; `if_rowOut_nz` renames it for the three-way case
in `if_rowSpec`. -/
theorem if_rowOut {tr : Trace} {pub : List F} {r : Nat} :
    rowOut IfC.table tr pub 22 r =
      [IfC.nz.eval (tr.row pub 22 r) * (((rowNat tr 22 r 0 : Nat) : F) + 1) +
          (1 - IfC.nz.eval (tr.row pub 22 r)) * ((rowNat tr 22 r IfC.tgt : Nat) : F),
        ((rowNat tr 22 r 1 : Nat) : F) + 1,
        ((rowNat tr 22 r 2 : Nat) : F) + ((rowNat tr 22 r 4 : Nat) : F),
        ((0 : Nat) : F), ((rowNat tr 22 r IfC.kSb : Nat) : F), ((rowNat tr 22 r IfC.kCid : Nat) : F)] := by
  simp only [rowOut, IfC.table, IfC.inters, stateOut, List.cons_append, List.append_assoc,
    List.nil_append, List.singleton_append, List.getD_cons_succ, List.getD_cons_zero,
    List.map_cons, List.map_nil]
  rw [row_eq_natRow]
  simp only [IfC.pcNext, IfC.pc1, v, Expr.eval_col, Expr.eval_add', Expr.eval_mul',
    Expr.eval_sub', Expr.eval_ofNat', natRow, cPc, cTs, cS, cFee, IfC.tgt, IfC.kSb, IfC.kCid, cast_one]

/-- `if_rowOut` with the non-zero witness named, as the spec's three-way case needs it. -/
theorem if_rowOut_nz {tr : Trace} {pub : List F} {r : Nat} (N : F)
    (hN : N = IfC.nz.eval (tr.row pub 22 r)) :
    rowOut IfC.table tr pub 22 r =
      [N * (((rowNat tr 22 r 0 : Nat) : F) + 1) + (1 - N) * ((rowNat tr 22 r IfC.tgt : Nat) : F),
        ((rowNat tr 22 r 1 : Nat) : F) + 1,
        ((rowNat tr 22 r 2 : Nat) : F) + ((rowNat tr 22 r 4 : Nat) : F),
        ((0 : Nat) : F), ((rowNat tr 22 r IfC.kSb : Nat) : F), ((rowNat tr 22 r IfC.kCid : Nat) : F)] := by
  rw [if_rowOut, ← hN]

end WasmBase
