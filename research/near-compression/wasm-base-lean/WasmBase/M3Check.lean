import WasmBase.M2Check
import WasmBase.M3Air
/-!
# WasmBase.M3Check — the checker of `wasmBaseM3Air` (`checkModuleM3`)

`checkModuleM2` with the three admitted-but-unchipped record kinds replaced by chip records:

| instruction | M2 record | M3 record |
|---|---|---|
| call of a listed host with `i32` parameters or result (`abort`, `promise_yield_resume`, …) | `[pc, 0x242, h, fee, 0, np, ar, 0]` | `[pc, 0x1FF, h, fee, hid, np, ar, 0]` (HOST-W) |
| `memory.size` | `[pc, 0x241, h, fee, 0, 0, 0, 0]` | `[pc, 0x3F, h, fee, 0, 0, 0, 0]` (MEMG) |
| `memory.grow` | `[pc, 0x240, h, 0, 0, 0, 0, 0]` | `[pc, 0x40, h, c/R, lin, 0, 0, 0]` (MEMG) |

The host table row of every host is `[id, np, ar, tmask, ri, 0, 0, 0]` (`hostRowM3`), with
`tmask`/`ri` the `i32` positions of the spec's linker signature (`hostSigs`).  `memory.grow`'s fee
is `charge`'s `count·fee.l + fee.c` with `count` the popped page count at a `.linear` point
(`step`): admitted when `fee.l` is one regular-op unit (PV86: `linearOpUnitCost = regularOpCost`),
so in `R` units the row charges `c/R + lin·n`.  The memory chip hard-codes `maxMemoryPages = 2048`,
so the checker requires it of `cfg`.  A host call whose signature has a non-integer type (none in
the corpus) keeps the M2 no-chip record.
-/
namespace WasmBase
open NearSpecV3.Wasm

/-- `i32` positions of a host's parameters (bit `j`) and whether its result is `i32`. -/
def hostTagsM3 (name : String) : Option (Nat × Nat) :=
  match NearSpecV3.Wasm.hostSigs.find? (·.1 = name) with
  | some (_, ft) =>
    if ft.params.all (fun t => t == .i32 || t == .i64) && ft.results.all (fun t => t == .i32 || t == .i64)
    then
      some (((List.range ft.params.size).map fun j => if ft.params[j]? == some .i32 then 2 ^ j else 0).foldl
          (· + ·) 0,
        if ft.results[0]? == some .i32 then 1 else 0)
    else none
  | none => none

/-- Host id, `np`, `ar`, `tmask`, `ri` of an import call with a HOST-W row. -/
def hostChipM3 (name : String) : Option (Nat × Nat × Nat × Nat × Nat) :=
  (hostFnsM2.find? (fun x => x.2.1 = name && Chips.hostShapeOk x.2.2.1 x.2.2.2)).bind fun x =>
    (hostTagsM3 name).map fun (m, r) => (x.1, x.2.2.1, x.2.2.2, m, r)

/-- The M3 host table row. -/
def hostRowM3 (x : Nat × String × Nat × Nat) : List Nat :=
  let (m, r) := (hostTagsM3 x.2.1).getD (0, 0)
  [x.1, x.2.2.1, x.2.2.2, m, r, 0, 0, 0]

/-- `memory.grow`'s fee in `R` units and its linear flag. -/
def growFee (cfg : NearCfg) : Option (Option (IK × Fee)) → Option (Nat × Nat)
  | some none => some (0, 0)
  | some (some (k, fee)) =>
    if cfg.regularOpCost ≠ 0 ∧ fee.c % cfg.regularOpCost = 0 ∧ fee.c / cfg.regularOpCost < 2 ^ 16 then
      if fee.l = 0 ∨ k ≠ .linear then some (fee.c / cfg.regularOpCost, 0)
      else if fee.l = cfg.regularOpCost then some (fee.c / cfg.regularOpCost, 1)
      else none
    else none
  | none => none

/-- Record of one pc in the M3 domain. -/
def recordAtM3 (cfg : NearCfg) (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat)
    (off : Nat) (cinfo : Nat → Option Nat) (pc : Nat) : Option (List Nat) :=
  let h := H[pc]?.getD 0
  match pf.code[pc]? with
  | some .memGrow =>
    (growFee cfg pf.gas[pc]?).map fun (fee, lin) => [off + pc, Chips.opMemGrow, h, fee, lin, 0, 0, 0]
  | some .memSize =>
    (feeUnits cfg pf.gas[pc]?).map fun fee => [off + pc, Chips.opMemSize, h, fee, 0, 0, 0, 0]
  | some (.call fi) =>
    if fi < p.m.imports.size then
      match (importName p fi).bind hostChipM3, feeUnits cfg pf.gas[pc]? with
      | some (hid, np, ar, _, _), some fee => some [off + pc, Chips.opHost, h, fee, hid, np, ar, 0]
      | _, _ => recordAtM2 cfg p pf L H off cinfo pc
    else recordAtM2 cfg p pf L H off cinfo pc
  | _ => recordAtM2 cfg p pf L H off cinfo pc

def checkM3 (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk cfg pf then
      match analyzeM2 p pf with
      | none => none
      | some (L, H) =>
        if structOkM2 p pf L H then
          match (List.range pf.code.size).mapM (recordAtM3 cfg p pf L H off cinfo) with
          | none => none
          | some recs =>
            some { fn, labels := L, heights := H, arity := pf.type.results.size,
                   localTags := (pf.type.params.toList ++ pf.locals.toList).map vtTag,
                   np := pf.type.params.size, nl := pf.type.params.size + pf.locals.size,
                   charge := pf.stackCharge, prologue := pf.prologueGas / cfg.regularOpCost,
                   resTag := if pf.type.results[0]? == some .i64 then 1 else 0,
                   records := recs.toArray,
                   maxFee := (recs.map fun r => r.getD 3 0).foldl max 0 }
        else none
    else none

/-- **The M3 checker.** -/
def checkModuleM3 (cfg : NearCfg) (p : Prepared) (entry : Nat) : Option ModOutH :=
  let fns := closureFns p entry
  match fns.mapM (fun fn => p.funcs[fn]?) with
  | none => none
  | some pfs =>
  let sizes := pfs.map (·.code.size)
  let offs := prefixOffs sizes 0
  let cinfo := callInfo p fns offs
  match (List.range fns.length).mapM (fun k => checkM3 cfg p (fns.getD k 0) (offs.getD k 0) cinfo) with
  | none => none
  | some cks =>
    let total := sizes.foldl (· + ·) 0
    let recs := (List.range total).map fun j =>
      let kl := locate offs sizes j
      ((cks.getD kl.1 default).records)[kl.2]?.getD []
    if fns.head? = some entry ∧ total < 2 ^ 20 ∧ layoutOk fns offs sizes total = true ∧
        fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (fns.contains ·)) ∧
        (pfs.head?.map (·.type.params.size)) = some 0 ∧
        calledImportsOkM2 p fns = true ∧ cfg.maxMemoryPages = Chips.maxPagesM3 then
      some { mod := { fns, cks, offs, sizes, codeSize := total, records := recs.toArray,
                      maxFee := (cks.map (·.maxFee)).foldl max 0 + (cks.map (·.prologue)).foldl max 0,
                      funcs := (List.range fns.length).map fun k => funcRow (offs.getD k 0) (cks.getD k default) },
             hostRows := hostFnsM2.map hostRowM3 }
    else none

/-! ## Facts -/

/-- `abort` has four `i32` parameters (`tmask = 15`) and no result. -/
theorem abort_tags : hostChipM3 "abort" = some (51, 4, 0, 15, 0) := by decide +kernel

/-- `promise_yield_resume` has an `i32` result (`ri = 1`). -/
theorem yield_resume_tags : hostChipM3 "promise_yield_resume" = some (26, 4, 1, 0, 1) := by
  decide +kernel

/-- Every all-`i64` host keeps the M2 host table row (`tmask = ri = 0`). -/
theorem hostRowM3_i64 (x : Nat × String × Nat × Nat) (h : hostTagsM3 x.2.1 = some (0, 0)) :
    hostRowM3 x = Chips.hostRow x.1 x.2.2.1 x.2.2.2 := by
  unfold hostRowM3 Chips.hostRow; rw [h]; rfl

/-- PV86's memory limit is the chip's. -/
theorem pv86_maxPages : pv86.maxMemoryPages = Chips.maxPagesM3 := rfl

end WasmBase
