import WasmBase.M2Ctx
import WasmBase.M3Check
/-!
# WasmBase.Main.SegGrowCode — the code facts of a MEMG row from `checkM3` (E2E M6, GROW)

The `step_memSize` / `step_memGrow_*` lemmas (`Main/SegGrowStep.lean`) and the MEMG row-spec
premises (`memSize_rowSpecJQ`, `memGrowOk_rowSpecJQ`, `Main/SegExecQ.lean`) take the code facts of
the row's pc as hypotheses: the instruction, its fee entry, and the straight successor (labels kept,
height `h` / `h + 1`).  Here they are derived from the M3 checker's per-pc functions, as `M2Ctx`
does for the M2 rows:

* **the FETCH converse** `recordAtM3_memGrow_op` / `recordAtM3_memSize_op`: a record of an
  `checkM3`-checked pc with opcode `0x40` (`0x3F`) is the record of `memory.grow`
  (`memory.size`): the instruction, `growFee` (`feeUnits`) of the gas entry, the static height —
  no other record kind (`recordOf`, the M2 kinds, HOST) has these opcodes (`recordOf_op_not_mem`,
  `recordAtM2_op_not_mem`);
* **the successors** `verifyAtM2_memGrow` / `verifyAtM2_memSize` (`checkM3` uses `structOkM2`,
  hence `verifyAtM2`, at every pc): `pc + 1` is in the code with the same labels and height `h`
  (`h + 1`), and `1 ≤ h` for `memory.grow`.

Open: the module-level context (`M3Ctx`, the `M2Ctx` API for `checkModuleM3`) that turns these
per-function facts into the `AtRow` hypotheses of a trace's MEMG rows.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- `recordOf` never produces the MEMG opcodes `0x40` / `0x3F`. -/
theorem recordOf_op_not_mem {cof : Nat} {ci : Nat → Option Nat} {ls : List Label} {h fee pc : Nat}
    {ins : Instr} {rec : List Nat} (hr : recordOf cof ci ls h fee pc ins = some rec) :
    rec.getD 1 0 ≠ Chips.opMemGrow ∧ rec.getD 1 0 ≠ Chips.opMemSize := by
  unfold recordOf at hr
  split at hr <;> (try split at hr) <;> (try split at hr) <;>
    simp only [Option.some.injEq, reduceCtorEq] at hr <;> (try subst hr) <;>
    simp_all [Chips.opMemGrow, Chips.opMemSize, Chips.Ctrl.opNext, Chips.Ctrl.opJump, Chips.Ctrl.opJif,
      Chips.Ctrl.opHalt, Chips.Ctrl.opHif, opCall, isFamilyNum, isLoadOp, isStoreOp] <;> omega

/-- `recordAtM2` never produces the MEMG opcodes (its `memory.grow`/`memory.size` records are the
no-chip `0x240`/`0x241`). -/
theorem recordAtM2_op_not_mem {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) :
    rec.getD 1 0 ≠ Chips.opMemGrow ∧ rec.getD 1 0 ≠ Chips.opMemSize := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | exact recordOf_op_not_mem hr
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp_all [Chips.opMemGrow, Chips.opMemSize, Chips.IfC.opIf, Chips.Ctrl.opJump, Chips.opHost, opHostX,
         opUnreach, opMemGrowX, opMemSizeX, isConvOp]
       done)
    | (simp only [Option.some.injEq] at hr; subst hr
       rename_i hcv
       simp only [isConvOp, Bool.or_eq_true, beq_iff_eq] at hcv
       simp only [List.getD_cons_succ, List.getD_cons_zero, Chips.opMemGrow, Chips.opMemSize]
       omega)

/-- **The FETCH converse for `memory.grow`**: a `checkM3` record with opcode `0x40` is the record of
`memory.grow`, with `growFee`'s fee units and linear flag, and the static height. -/
theorem recordAtM3_memGrow_op {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM3 cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = Chips.opMemGrow) :
    ∃ fee lin, pf.code[pc]? = some .memGrow ∧ growFee cfg pf.gas[pc]? = some (fee, lin) ∧
      rec = [off + pc, Chips.opMemGrow, H[pc]?.getD 0, fee, lin, 0, 0, 0] := by
  unfold recordAtM3 at hr
  split at hr
  · rename_i hc
    cases hg : growFee cfg pf.gas[pc]? with
    | none => simp [hg] at hr
    | some fl =>
      obtain ⟨fee, lin⟩ := fl
      simp only [hg, Option.map_some, Option.some.injEq] at hr
      exact ⟨fee, lin, hc, rfl, hr.symm⟩
  · cases hf : feeUnits cfg pf.gas[pc]? with
    | none => simp [hf] at hr
    | some fee =>
      simp only [hf, Option.map_some, Option.some.injEq] at hr
      subst hr; simp [Chips.opMemGrow, Chips.opMemSize] at hop
  · split at hr
    · split at hr
      · simp only [Option.some.injEq] at hr; subst hr; simp [Chips.opMemGrow, Chips.opHost] at hop
      · exact absurd hop (recordAtM2_op_not_mem hr).1
    · exact absurd hop (recordAtM2_op_not_mem hr).1
  · exact absurd hop (recordAtM2_op_not_mem hr).1

/-- **The FETCH converse for `memory.size`**: a `checkM3` record with opcode `0x3F` is the record of
`memory.size`, with its fee units and the static height. -/
theorem recordAtM3_memSize_op {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM3 cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = Chips.opMemSize) :
    ∃ fee, pf.code[pc]? = some .memSize ∧ feeUnits cfg pf.gas[pc]? = some fee ∧
      rec = [off + pc, Chips.opMemSize, H[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  unfold recordAtM3 at hr
  split at hr
  · cases hg : growFee cfg pf.gas[pc]? with
    | none => simp [hg] at hr
    | some fl =>
      obtain ⟨fee, lin⟩ := fl
      simp only [hg, Option.map_some, Option.some.injEq] at hr
      subst hr; simp [Chips.opMemGrow, Chips.opMemSize] at hop
  · rename_i hc
    cases hf : feeUnits cfg pf.gas[pc]? with
    | none => simp [hf] at hr
    | some fee =>
      simp only [hf, Option.map_some, Option.some.injEq] at hr
      exact ⟨fee, hc, rfl, hr.symm⟩
  · split at hr
    · split at hr
      · simp only [Option.some.injEq] at hr; subst hr; simp [Chips.opMemSize, Chips.opHost] at hop
      · exact absurd hop (recordAtM2_op_not_mem hr).2
    · exact absurd hop (recordAtM2_op_not_mem hr).2
  · exact absurd hop (recordAtM2_op_not_mem hr).2

/-- **The successor of a `memory.grow` pc** (`verifyAtM2`, which `checkM3` checks at every pc):
`pc + 1` is in the code with the same labels and the same height, and `1 ≤ h`. -/
theorem verifyAtM2_memGrow {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat} {pc : Nat}
    (hv : verifyAtM2 p pf L H pc = true) (hc : pf.code[pc]? = some .memGrow) {ls : List Label} {h : Nat}
    (hL : L[pc]? = some ls) (hH : H[pc]? = some h) :
    1 ≤ h ∧ pc + 1 < pf.code.size ∧ L[pc + 1]? = some ls ∧ H[pc + 1]? = some h := by
  unfold verifyAtM2 at hv
  rw [hc, hL, hH] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1, hv.2.1.1, hv.2.1.2, hv.2.2⟩

/-- **The successor of a `memory.size` pc**: same labels, height `h + 1`. -/
theorem verifyAtM2_memSize {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat} {pc : Nat}
    (hv : verifyAtM2 p pf L H pc = true) (hc : pf.code[pc]? = some .memSize) {ls : List Label} {h : Nat}
    (hL : L[pc]? = some ls) (hH : H[pc]? = some h) :
    pc + 1 < pf.code.size ∧ L[pc + 1]? = some ls ∧ H[pc + 1]? = some (h + 1) := by
  unfold verifyAtM2 at hv
  rw [hc, hL, hH] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1.1, hv.1.2, hv.2⟩

#print axioms recordOf_op_not_mem
#print axioms recordAtM2_op_not_mem
#print axioms recordAtM3_memGrow_op
#print axioms recordAtM3_memSize_op
#print axioms verifyAtM2_memGrow
#print axioms verifyAtM2_memSize

end WasmBase
