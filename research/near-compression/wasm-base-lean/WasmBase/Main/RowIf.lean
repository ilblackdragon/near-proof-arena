import WasmBase.Main.Rows
import WasmBase.IfCheck
import WasmBase.StepIf
import WasmBase.Local.Simple
/-!
# Row lemma: `IF` — the soundness leg

`Main/RowCtrl.lean` is the template.  The `IF` row differs in three ways, and each is where the work
is:

1. **The polarity lives in the STATE successor, not in a selector.**  `IfC.pcNext = nz·(pc+1) +
   (1−nz)·tgt` with `nz = [c ≠ 0]`; `CTRL`'s `fJif` is `nz·tgt + (1−nz)·(pc+1)`.  There is no
   `f_next`/`f_jump` choice to read off, so the successor target must be *derived* from `nz`.
2. **The row always consumes its condition.**  `CTRL` gates its CH receive on
   `cnd = f_jif + f_hif`; `IF` has no inactive row, so `cons = [mC]` unconditionally.
3. **Three successor shapes** (true arm; false with `else`; false without), so the spec branch is a
   three-way case rather than `CTRL`'s five selectors.

## What this file establishes

* the table index (`IF` is table 22 of `wasmBaseIfAir`);
* the CH traffic (`if_rowCons`, `if_rowProd`) — one condition consumed, nothing produced;
* the STATE message shapes (`if_rowIn`, `if_rowOut`) with the `nz` polarity;
* the local constraint facts (`if_facts`) from `Holds` alone;
* the fetch-record converse (`recordAtIf_opIf`): a FETCH answer with opcode `opIf` pins the
  instruction, `endOf`, `elseOf` and the false target;
* `if_rowfacts_static`: `halt0`, `tsOut`, `prodT`, `prodNd` from `Holds` alone, and `gasOut`/`consT`
  from the two facts that only a lookup answer supplies (the row's `fee`, and the condition's
  producer-time bound).  Those two are *named* hypotheses, not silently assumed.

## The checker-side premise

`if_rowSpec` is the three-way spec step: `step_if` / `step_if_else` / `step_if_noelse`, dispatched
on the AIR's own `nz` (not on a spec-side value), which is what makes the row's `pcNext` and the
spec's successor the same number in all three shapes.  `if_rowfacts` assembles it with the six
timestamp/definitional fields into a full `RowFacts`.

What the AIR cannot supply is the *checker's* data for the row's pc: the instruction, `endOf`,
`elseOf`, the fee, and the two successor label lists.  For a base instruction `fetch_rec` derives
those from `Looks` + `CheckFacts`; for an `.if_` row the record comes from `recordAtIf` and the
successors from `verifyAtIf`, and the base `Ctx` carries neither — `Check.kindOf` has no `.if_`
case, so `checkModule` rejects an `if` module outright and `checkModuleIf` replaces it.  That
premise is `IfRowData`: one named structure holding exactly the checker output plus the two
FETCH-answer links (`tgt`, `hEq`), so the row lemma is honest about its premise instead of silently
assuming it.  Discharging `IfRowData` is the `checkModuleIf` soundness lane.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- `IF` is table 22 of the `if` AIR (23 tables). -/
theorem if_air_len (nloc ncode : Nat) : (wasmBaseIfAir nloc ncode).tables.length = 23 := by
  simp [wasmBaseIfAir, air_len]

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

/-- `IfC.act` is the selector, so its natural value is `f_if`'s.  Definitional: `act = v fIf`. -/
theorem if_act_val {pub : List F} {tr : Trace} {r : Nat} :
    (IfC.act.eval (tr.row pub 22 r)).toNat = rowNat tr 22 r IfC.fIf := rfl

/-- `recordOf`'s opcode is always below `0x106`: the largest it can emit is `Ctrl.opHif = 0x105`.
This is `recordOf_op_lt`'s case analysis with the tight bound the `IF` table needs. -/
theorem recordOf_op_lt_opIf {cof : Nat} {ci : Nat → Option Nat} {ls : List Label} {h fee pc : Nat}
    {ins : Instr} {rec : List Nat} (hr : recordOf cof ci ls h fee pc ins = some rec) :
    rec.getD 1 0 < IfC.opIf := by
  obtain ⟨op, x0, x1, x2, x3, rfl, hc⟩ := recordOf_spec hr
  simp only [List.getD_cons_succ, List.getD_cons_zero, IfC.opIf]
  rcases hc with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ <;>
  first | (subst h; decide) | (have := isFamilyNum_le hf; omega) | omega

/-- `recordOf` never yields the `IF` opcode. -/
theorem recordOf_ne_opIf {cof : Nat} {ci : Nat → Option Nat} {ls : List Label} {h fee pc : Nat}
    {ins : Instr} {rec : List Nat} (hr : recordOf cof ci ls h fee pc ins = some rec) :
    rec.getD 1 0 ≠ IfC.opIf := by
  have := recordOf_op_lt_opIf hr
  omega

/-- **The record of an `IF` row.**  A FETCH answer whose opcode is `opIf` must have come from
`recordAtIf`'s `.if_` arm, so it pins the instruction, `endOf`, `elseOf` and the false target.
The third conjunct is exactly the shape the AIR row's `x0` carries: `elseOf + 1` in *both* `if`
shapes, because `matchBlocks` sets `elseOf = endOf` when there is no `else`. -/
theorem recordAtIf_opIf {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off : Nat} {cinfo : Nat → Option Nat} {pc : Nat} {rec : List Nat}
    (hr : recordAtIf cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = IfC.opIf) :
    ∃ bt e el fee, pf.code[pc]? = some (.if_ bt) ∧ pf.endOf[pc]? = some e ∧
      pf.elseOf[pc]? = some el ∧ feeUnits cfg pf.gas[pc]? = some fee ∧
      rec = [off + pc, IfC.opIf, H[pc]?.getD 0, fee, el + 1 + off, 0, 0, 0] := by
  unfold recordAtIf at hr
  split at hr
  · rename_i ins fee hins hfee
    split at hr
    · -- `.if_`
      split at hr
      · rename_i e el he hel
        simp only [Option.some.injEq] at hr
        exact ⟨_, e, el, fee, hins, he, hel, hfee, hr.symm⟩
      · simp at hr
    · -- `.else_`: the opcode is `opJump`, so `hop` is false
      split at hr
      · rename_i lab hlab
        simp only [Option.some.injEq] at hr
        subst hr
        simp only [List.getD_cons_succ, List.getD_cons_zero, IfC.opIf, Ctrl.opJump] at hop
        exact absurd hop (by decide)
      · simp at hr
    · -- everything else: `recordOf` never yields `opIf`
      exact absurd hop (recordOf_ne_opIf hr)
  · simp at hr

/-- The `IF` row produces nothing on the value channel. -/
theorem if_rowProd {tr : Trace} {pub : List F} {r : Nat} :
    rowProd IfC.table tr pub 22 r = [] := by
  rw [rowProd, rowMsgs_eq]
  show (List.filterMap _ (IfC.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true)))).map decMsg = _
  rw [if_filterP]; rfl

/-- The `IF` row's STATE input is the standard state message, with the frame columns at
`IfC.kSb`/`IfC.kCid` (12/13).  Stated directly in terms of the row's cells, so consumers can
`rw` it without carrying a `cc` abbreviation around. -/
theorem if_rowIn {tr : Trace} {pub : List F} {r : Nat} :
    rowIn IfC.table tr pub 22 r =
      [tr.cell 22 r 0, tr.cell 22 r 1, tr.cell 22 r 2, ((0 : Nat) : F),
        tr.cell 22 r IfC.kSb, tr.cell 22 r IfC.kCid] := by
  simp only [rowIn, IfC.table, IfC.inters, stateIn, List.cons_append, List.getD_cons_zero,
    List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cPc, cTs, cS,
    IfC.kSb, IfC.kCid]

/-- The `IF` row's STATE output.  The successor pc is `nz·(pc+1) + (1−nz)·tgt` — the polarity that
distinguishes `IF` from `CTRL`'s `fJif`.  `halted = 0` always (`if` never halts the trace). -/
theorem if_rowOut {tr : Trace} {pub : List F} {r : Nat} :
    rowOut IfC.table tr pub 22 r =
      [IfC.nz.eval (tr.row pub 22 r) * (tr.cell 22 r 0 + 1) +
          (1 - IfC.nz.eval (tr.row pub 22 r)) * tr.cell 22 r IfC.tgt,
        tr.cell 22 r 1 + ((1 : Nat) : F), tr.cell 22 r 2 + tr.cell 22 r 4, ((0 : Nat) : F),
        tr.cell 22 r IfC.kSb, tr.cell 22 r IfC.kCid] := by
  simp only [rowOut, IfC.table, IfC.inters, stateOut, List.cons_append, List.getD_cons_succ,
    List.getD_cons_zero, List.map_cons, List.map_nil, IfC.pcNext, IfC.pc1, v, Expr.eval_col,
    Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Trace.row, cPc, cTs, cS, cFee,
    IfC.tgt, IfC.kSb, IfC.kCid, cast_one]

/-- **The condition is consumed, always.**  `IF` has no inactive row, so its CH receive is the
condition — there is no gating count to case on, unlike `CTRL`'s `cnd`.  The slot is kept in the
AIR's own field arithmetic (`(sb + h) − 1`, then `toNat`), exactly as `Ctrl.rowfacts`' `mC` does,
so no `Nat`-subtraction side condition is needed. -/
theorem if_rowCons {tr : Trace} {pub : List F} {r : Nat}
    (hact : rowAct IfC.table tr pub 22 r) :
    rowCons IfC.table tr pub 22 r =
      [⟨0, (tr.cell 22 r IfC.kSb + tr.cell 22 r cH - ((1 : Nat) : F)).toNat, 0,
        rowNat tr 22 r IfC.c, rowNat tr 22 r (IfC.c + 1), 0, 0, rowNat tr 22 r IfC.tc⟩] := by
  have hP' := P_val
  have hcnt : rowNat tr 22 r IfC.fIf = 1 := hact
  rw [rowCons, rowMsgs_eq]
  show (List.filterMap _ (IfC.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = false)))).map decMsg = _
  rw [if_filterC]
  simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv]
  rw [if_act_val, ite_eq_left hcnt]
  have h0 : ((0 : Nat) : F).toNat = 0 := by decide
  simp only [List.map_cons, List.map_nil, List.map_append, List.append_assoc, List.cons_append,
    List.nil_append, v, Expr.eval_col, Expr.eval_sub', Expr.eval_add',
    Expr.eval_ofNat', cell_cast, Trace.row, cH, IfC.kSb, IfC.c, IfC.tc, decMsg,
    List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (rowNat_lt tr 22 r _), h0,
    List.cons.injEq, and_true, Msg.mk.injEq]

/-- **The `IF` row's local constraint facts**, from `Holds` alone: the selector is a bit, and
`nz = [c ≠ 0]`.  This is `Local.if_sound` with its 16-bit hypothesis discharged *conditionally*
(the guard the row lemma actually has when the condition arrives on the CH bus), so no consumer has
to invent a bound. -/
theorem if_facts {nloc ncode : Nat} {pub : List F} {tr : Trace} {r : Nat}
    (H : Holds (wasmBaseIfAir nloc ncode) pub tr) (hr : r < tr.height 22) :
    (rowNat tr 22 r IfC.fIf = 0 ∨ rowNat tr 22 r IfC.fIf = 1) ∧
    (rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) < P →
      IfC.nz.eval (tr.row pub 22 r) =
        ((if rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) = 0 then 0 else 1 : Nat) : F)) := by
  have ht : 22 < (wasmBaseIfAir nloc ncode).tables.length := by simp [if_air_len]
  have hcon : ∀ e ∈ IfC.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 :=
    table_constr H ht hr
  have hP : ∀ i, rowNat tr 22 r i < P := rowNat_lt tr 22 r
  simp only [IfC.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, v, IfC.fIf, IfC.nz, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at hcon
  obtain ⟨hbit, hnz⟩ := hcon
  refine ⟨bool_nat (hP _) hbit, fun hz => ?_⟩
  have hn := nz_val (inv := rowNat tr 22 r IfC.inv) hz
    (by simpa only [Lean.Grind.Semiring.natCast_add] using hnz)
  rw [row_eq_natRow]
  simp only [IfC.nz, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, natRow]
  rw [show (((rowNat tr 22 r IfC.c : Nat) : F) + ((rowNat tr 22 r (IfC.c + 1) : Nat) : F))
      = ((rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) : Nat) : F) by
    rw [Lean.Grind.Semiring.natCast_add]]
  exact hn

/-- **Six of the seven `RowFacts` fields.**  They are *definitional* for this row: the IF table's
STATE in/out messages are fixed expressions, so `halt0`, `tsOut`, `prodT` and `prodNd` need no
`Holds` at all.  `gasOut` needs the row's `fee` and `consT` needs the condition's producer-time
bound; those two come from lookup answers (the FETCH answer and the R16 time check) and are stated
as named hypotheses rather than assumed. -/
theorem if_rowfacts_static {X : Ctx} {pub : List F} {tr : Trace} {r : Nat} {fee : Nat}
    (hfeeMax : fee ≤ X.maxFee) (hgasEq : rowNat tr 22 r cFee = fee)
    (hconsT : ∀ x ∈ rowCons IfC.table tr pub 22 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn IfC.table tr pub 22 r)) :
    (rowIn IfC.table tr pub 22 r).getD 3 0 = 0 ∧
    lvl (rowOut IfC.table tr pub 22 r) = lvl (rowIn IfC.table tr pub 22 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧ gasF (rowOut IfC.table tr pub 22 r) = gasF (rowIn IfC.table tr pub 22 r) + (fee : F)) ∧
    (∀ x ∈ rowCons IfC.table tr pub 22 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn IfC.table tr pub 22 r)) ∧
    (∀ x ∈ rowProd IfC.table tr pub 22 r, x.tp < P ∧ ((x.tp : Nat) : F) = lvl (rowIn IfC.table tr pub 22 r)) ∧
    (rowProd IfC.table tr pub 22 r).Nodup := by
  have hIn := if_rowIn (tr := tr) (pub := pub) (r := r)
  have hOut := if_rowOut (tr := tr) (pub := pub) (r := r)
  have hProd := if_rowProd (tr := tr) (pub := pub) (r := r)
  -- `cFee = 4` definitionally; state the cell fact at the literal column `if_rowOut` produces.
  have hcell : tr.cell 22 r 4 = ((fee : Nat) : F) := by
    rw [← hgasEq, cell_cast, cFee]
  refine ⟨by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee, hfeeMax, ?_⟩, hconsT, ?_, ?_⟩
  · rw [hIn, hOut]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, gasF, hcell]
  · rw [hProd]; intro x hx; simp at hx
  · rw [hProd]; exact List.nodup_nil

/-- `ifStep`'s guard: a successful static `if` step leaves a non-empty frame stack. -/
theorem ifStep_h {p : Prepared} {pf : PFunc} {ls : List Label} {h pc : Nat} {bt : BT}
    {lsT : List Label} {hT ftgt : Nat} {lsF : List Label} {hF : Nat}
    (hs : ifStep p pf ls h pc bt = some (lsT, hT, ftgt, lsF, hF)) : 1 ≤ h := by
  unfold ifStep at hs
  split at hs
  · split at hs
    · split at hs
      · omega
      · simp at hs
    · simp at hs
  · simp at hs

/-- **The checker-side data one `IF` row needs, in exactly the shape the AIR row carries it.**

This is the `if` lane's one outstanding inspection debt.  For a base instruction `fetch_rec` derives
this from `Looks` + `CheckFacts`; an `.if_` row's record instead comes from `recordAtIf` and its two
successors from `verifyAtIf`, neither of which the base `Ctx` carries — `Check.kindOf` has no `.if_`
case, so `checkModule` rejects an `if` module outright and is replaced by `checkModuleIf`.  Naming
the debt keeps the row lemma honest and non-vacuous about its premise; discharging it is the
`checkModuleIf` soundness lane.

`tgt` and `hEq` are the two FETCH-answer links that are *not* implied by the checker output alone:
they say the row's `tgt` cell is `elseOf + 1 + off` and its `h` cell is the checker's height, i.e.
that the row's FETCH query was answered by `recordAtIf`'s record for this pc.

`succ` is `verifyAtIf` at the row's pc, already unfolded through `ifStep`: the pushed label, the
post-pop height `h - 1`, and both successor label lists.  Carrying it in this form keeps the spec
proof free of `ifStep`-unfolding and makes the three-way case split read exactly like the checker. -/
structure IfRowData (X : Ctx) (tr : Trace) (r : Nat) (fee : Nat) where
  /-- checked-function index of the row's frame -/
  k : Nat
  /-- the row's local `pc` -/
  pc : Nat
  bt : BT
  e : Nat
  el : Nat
  kLt : k < X.nf
  pcLt : pc < (X.pfOf k).code.size
  /-- the row's global pc is its STATE pc cell -/
  gpc : X.offOf k + pc = rowNat tr 22 r 0
  ins : (X.pfOf k).code[pc]? = some (.if_ bt)
  endE : (X.pfOf k).endOf[pc]? = some e
  elseE : (X.pfOf k).elseOf[pc]? = some el
  feeEq : feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee
  /-- the AIR's `tgt` cell is `elseOf + 1`, made global -/
  tgt : rowNat tr 22 r IfC.tgt = el + 1 + X.offOf k
  /-- the AIR's `h` cell is the checker's height at `pc` -/
  hEq : rowNat tr 22 r cH = (X.ckOf k).heights[pc]?.getD 0
  hLt : rowNat tr 22 r cH < 2 ^ 16
  /-- `verifyAtIf` at the row's pc, unfolded through `ifStep` -/
  succ : ∀ (ls : List Label) (h : Nat), (X.ckOf k).labels[pc]? = some ls →
    (X.ckOf k).heights[pc]? = some h →
    ∃ hT, 1 ≤ h ∧ hT = h - 1 ∧ pc + 1 < (X.pfOf k).code.size ∧
      (X.ckOf k).labels[pc + 1]? = some (mkIfLabel bt e hT :: ls) ∧
      (X.ckOf k).heights[pc + 1]? = some hT ∧ el + 1 < (X.pfOf k).code.size ∧
      (X.ckOf k).labels[el + 1]? = some (if el = e then ls else mkIfLabel bt e hT :: ls) ∧
      (X.ckOf k).heights[el + 1]? = some hT

/-- **The `IF` row's spec step — the three-way dispatch on the AIR's `nz`.**

The polarity is the AIR's, not the spec's: `IfC.pcNext = nz·(pc+1) + (1−nz)·tgt` with
`nz = [(c0 + c1) ≠ 0]`, so the row lemma cases on `mc.val` — which is `c0 + 2^16·c1`, hence zero
exactly when the AIR's `c0 + c1` is — and then on `elseOf = endOf`, matching
`step_if` / `step_if_else` / `step_if_noelse`. -/
theorem if_rowSpec {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} {r : Nat}
    (H : Holds (wasmBaseIfAir nloc ncode) pub tr) (hr : r < tr.height 22)
    (hact : rowAct IfC.table tr pub 22 r) {fee : Nat} (hfeeMax : fee ≤ X.maxFee)
    (hgasEq : rowNat tr 22 r cFee = fee) (hd : IfRowData X tr r fee) :
    RowSpec X (rowIn IfC.table tr pub 22 r) (rowOut IfC.table tr pub 22 r)
      (rowCons IfC.table tr pub 22 r) (rowProd IfC.table tr pub 22 r) := by
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  have hPv := P_val
  have hP : ∀ i, rowNat tr 22 r i < P := rowNat_lt tr 22 r
  let cc : Nat → F := fun i => ((rowNat tr 22 r i : Nat) : F)
  have hIn' : rowIn IfC.table tr pub 22 r =
      [cc 0, cc 1, cc 2, ((0 : Nat) : F), cc IfC.kSb, cc IfC.kCid] := by
    rw [if_rowIn]; simp only [cc, cell_cast]
  rw [hIn'] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : rowNat tr 22 r 0 = X.offOf E.k + pc := natEq i0 (hP _) (by omega)
  have p1 : rowNat tr 22 r 1 = t := natEq i1 (hP _) (by omega)
  have p2 : rowNat tr 22 r 2 = S := natEq i2 (hP _) (by omega)
  have psb : rowNat tr 22 r IfC.kSb = E.sb := natEq i4 (hP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 22 r IfC.kCid = E.cid := natEq i5 (hP _) (by have := R.cidLt; omega)
  -- identify the row's checker (function, pc) with the spec's frame
  obtain ⟨hk, hpc0, bt, e, el, hkLt, hpcLt, hgpc, hins, hend, hels, hfeeEq, htgt, hcHEq, hcHLt, hsucc⟩ := hd
  have hpcEq : X.offOf hk + hpc0 = X.offOf E.k + pc := by rw [hgpc, ← p0]
  obtain ⟨hkE, -⟩ := X.loc_unique hkLt hpcLt R.kLt R.pcLt hpcEq
  subst hkE
  have hpc0eq : hpc0 = pc := by omega
  rw [hpc0eq] at hins hend hels hfeeEq hsucc hcHEq
  -- the static analysis at the row's pc
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hH0 := R.height
  obtain ⟨hT, hge0, hTeq, hnextT, hLT, hHT, hnextF, hLF, hHF⟩ :=
    hsucc ls0 (s.stack.size - E.sb) hL0 hH0
  have hTv : hT = s.stack.size - 1 - E.sb := by rw [hTeq]; omega
  have hge : 1 ≤ s.stack.size - E.sb := hge0
  have hsz : 0 < s.stack.size := by have := R.sbLe; omega
  have hsb1 : E.sb ≤ s.stack.size - 1 := by have := R.sbLe; omega
  have h3 : rowNat tr 22 r cH = s.stack.size - E.sb := by rw [hcHEq, hH0, Option.getD_some]
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  -- the consumed condition
  let mC : Msg := ⟨0, (tr.cell 22 r IfC.kSb + tr.cell 22 r cH - ((1 : Nat) : F)).toNat, 0,
    rowNat tr 22 r IfC.c, rowNat tr 22 r (IfC.c + 1), 0, 0, rowNat tr 22 r IfC.tc⟩
  have hConsEq : rowCons IfC.table tr pub 22 r = [mC] := if_rowCons hact
  have hProdEq : rowProd IfC.table tr pub 22 r = [] := if_rowProd
  rw [hConsEq] at hlive
  have hmC : live mC := hlive mC (by simp)
  rw [hConsEq, hProdEq]
  have sc : mC.space = 0 ∧ mC.slot = s.stack.size - 1 := by
    refine ⟨rfl, ?_⟩
    show (tr.cell 22 r IfC.kSb + tr.cell 22 r cH - ((1 : Nat) : F)).toNat = s.stack.size - 1
    rw [cell_cast, cell_cast]
    exact slot_toNat psb h3 R.sbLe hge hszP
  obtain ⟨-, okc, -, -⟩ := R.stack_dec hmC sc.1 sc.2 (by omega)
  have hlimbs : rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) < P := by
    have hl : mC.l0 < 65536 ∧ mC.l1 < 65536 := ⟨okc.1, okc.2.1⟩
    simp only [mC] at hl
    omega
  obtain ⟨-, hnzF⟩ := if_facts H hr
  have hvalz : mC.val = 0 ↔ rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) = 0 := by
    simp only [mC, Msg.val, val4]
    omega
  -- the STATE output, once the successor pc is fixed
  have hOut := if_rowOut (tr := tr) (pub := pub) (r := r)
  have hcell4 : rowNat tr 22 r 4 = fee := by simpa only [cFee] using hgasEq
  have e1 : tr.cell 22 r 1 + ((1 : Nat) : F) = ((t + 1 : Nat) : F) := by
    rw [cell_cast, p1, ← Lean.Grind.Semiring.natCast_add]
  have e2 : tr.cell 22 r 2 + tr.cell 22 r 4 = ((S + fee : Nat) : F) := by
    rw [cell_cast, cell_cast, p2, hcell4, ← Lean.Grind.Semiring.natCast_add]
  have e3 : tr.cell 22 r IfC.kSb = ((E.sb : Nat) : F) := by rw [cell_cast, psb]
  have e4 : tr.cell 22 r IfC.kCid = ((E.cid : Nat) : F) := by rw [cell_cast, pcid]
  have e5 : tr.cell 22 r 0 = ((X.offOf E.k + pc : Nat) : F) := by rw [cell_cast, p0]
  have e6 : tr.cell 22 r IfC.tgt = ((el + 1 + X.offOf E.k : Nat) : F) := by rw [cell_cast, htgt]
  -- `pcNext` is already a *global* pc (the AIR's `pc` cell is global, and `tgt` is `off + el + 1`)
  have mkOut : ∀ (pc' : Nat),
      IfC.nz.eval (tr.row pub 22 r) * (tr.cell 22 r 0 + 1) +
        (1 - IfC.nz.eval (tr.row pub 22 r)) * tr.cell 22 r IfC.tgt
        = ((X.offOf E.k + pc' : Nat) : F) →
      rowOut IfC.table tr pub 22 r = stMsg (X.offOf E.k + pc') (t + 1) (S + fee) 0 E.sb E.cid := by
    intro pc' h1
    rw [hOut, h1, e1, e2, e3, e4]
    simp only [stMsg]
  by_cases hz : mC.val = 0
  · -- condition zero: `nz = 0`, so the AIR takes `tgt = elseOf + 1`
    have hc0 : rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) = 0 := hvalz.mp hz
    have hnz : IfC.nz.eval (tr.row pub 22 r) = 0 := by
      rw [hnzF hlimbs, ite_eq_left hc0, cast_zero]
    have hpcOut : IfC.nz.eval (tr.row pub 22 r) * (tr.cell 22 r 0 + 1) +
        (1 - IfC.nz.eval (tr.row pub 22 r)) * tr.cell 22 r IfC.tgt
        = ((X.offOf E.k + (el + 1) : Nat) : F) := by
      rw [hnz, e5, e6]
      grind
    by_cases hne : el = e
    · -- no `else`: the spec pushes no label and jumps to `end + 1`
      have hlsF'' : (if el = e then ls0 else mkIfLabel bt e hT :: ls0) = ls0 := by
        rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
      have hel' : (X.pfOf E.k).elseOf[pc]? = some e := by rw [← hne]; exact hels
      have hnextE : e + 1 < (X.pfOf E.k).code.size := by rw [← hne]; exact hnextF
      have hLFE : (X.ckOf E.k).labels[e + 1]? = some ls0 := by
        rw [← hne]; rw [hlsF''] at hLF; exact hLF
      have hHFE : (X.ckOf E.k).heights[e + 1]? = some (s.stack.size - 1 - E.sb) := by
        rw [← hne, ← hTv]; exact hHF
      refine ⟨E.k, e + 1, fee, 0, E.sb, E.cid, hfeeMax, Nat.zero_le 1,
        mkOut (e + 1) (by rw [hpcOut, hne]),
        fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
      exact step_if_noelse X R hins hend hel' hfeeEq hg hg64 mC hmC sc hsz hsb1 hz hfl0
        hnextE hLFE hHFE rfl
    · -- `else`: the spec pushes a label and jumps to `elseOf + 1`
      have hlsF'' : (if el = e then ls0 else mkIfLabel bt e hT :: ls0) =
          mkIfLabel bt e (s.stack.size - 1 - E.sb) :: ls0 := by
        rw [ite_eq_right_of_eq_false _ _ (eq_false hne), hTv]
      have hnextE : el + 1 < (X.pfOf E.k).code.size := hnextF
      have hLFE : (X.ckOf E.k).labels[el + 1]? = some (mkIfLabel bt e (s.stack.size - 1 - E.sb) :: ls0) := by
        rw [hlsF''] at hLF; exact hLF
      have hHFE : (X.ckOf E.k).heights[el + 1]? = some (s.stack.size - 1 - E.sb) := by
        rw [← hTv]; exact hHF
      refine ⟨E.k, el + 1, fee, 0, E.sb, E.cid, hfeeMax, Nat.zero_le 1, mkOut (el + 1) hpcOut,
        fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
      exact step_if_else X R hins hend hels hne hfeeEq hg hg64 mC hmC sc hsz hsb1 hz hfl0
        hnextE hLFE hHFE rfl
  · -- condition non-zero: `nz = 1`, so the AIR falls through to `pc + 1`
    have hc0 : rowNat tr 22 r IfC.c + rowNat tr 22 r (IfC.c + 1) ≠ 0 := fun h => hz (hvalz.mpr h)
    have hnz : IfC.nz.eval (tr.row pub 22 r) = 1 := by
      rw [hnzF hlimbs, ite_eq_right hc0, cast_one]
    have hpcOut : IfC.nz.eval (tr.row pub 22 r) * (tr.cell 22 r 0 + 1) +
        (1 - IfC.nz.eval (tr.row pub 22 r)) * tr.cell 22 r IfC.tgt
        = ((X.offOf E.k + (pc + 1) : Nat) : F) := by
      rw [hnz, e5, e6]
      grind
    have hLTE : (X.ckOf E.k).labels[pc + 1]? = some (mkIfLabel bt e (s.stack.size - 1 - E.sb) :: ls0) := by
      rw [← hTv]; exact hLT
    have hHTE : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - 1 - E.sb) := by
      rw [← hTv]; exact hHT
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfeeMax, Nat.zero_le 1, mkOut (pc + 1) hpcOut,
      fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    exact step_if X R hins hend hels hfeeEq hg hg64 mC hmC sc hsz hsb1 hz hfl0 hnextT hLTE hHTE
      rfl

/-- **The `IF` row's `RowFacts`**: the spec step above plus the six definitional/timestamp fields
from `if_rowfacts_static`. -/
theorem if_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseIfAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct IfC.table tr pub 22 r) {fee : Nat} (hfeeMax : fee ≤ X.maxFee)
    (hgasEq : rowNat tr 22 r cFee = fee) (hd : IfRowData X tr r fee)
    (hconsT : ∀ x ∈ rowCons IfC.table tr pub 22 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn IfC.table tr pub 22 r)) :
    RowFacts X (rowIn IfC.table tr pub 22 r) (rowOut IfC.table tr pub 22 r)
      (rowCons IfC.table tr pub 22 r) (rowProd IfC.table tr pub 22 r) := by
  obtain ⟨h0, hts, hgas, hcons, hprodT, hprodNd⟩ := if_rowfacts_static hfeeMax hgasEq hconsT
  exact ⟨if_rowSpec H hr hact hfeeMax hgasEq hd, h0, hts, hgas, hcons, hprodT, hprodNd⟩

end WasmBase
