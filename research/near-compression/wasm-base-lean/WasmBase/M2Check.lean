import WasmBase.IfCheck
/-!
# WasmBase.M2Check — the E2E M2 checker (`checkModuleM2`)

`checkModuleIfH` extended, without touching it, by what the d3c7–d3c10 corpus census
(`wasmbase-tool census`, `e2e-general/m2/README.md`) shows the uncovered contracts need:

| extension | instructions | how it is proved |
|---|---|---|
| conversions | `i32.wrap_i64` (0xA7), `i64.extend_i32_s` (0xAC), `i64.extend_i32_u` (0xAD) | the `CONV` chip (`WasmBase/M2Air.lean`), record `[pc, op, h, fee, 0, 0, 0, 0]` |
| `unreachable` | 0x00 | the `UNREACH` chip: a trapping row (`halted = 2`), record `[pc, 0, h, fee, 0, 0, 0, 0]` |
| `if` with a result | `if (result t)` … `else` … `end` | checker only: the `IF`/`CTRL` rows are unchanged (§ below) |
| `ed25519_verify` | host id 61, `(6, 1)`, all `i64` | the HOST row as every other oracle-answered host (`hostFnsM2`) |
| **admitted, no chip** | `memory.grow`, `memory.size`, a call of a listed host whose signature the HOST row cannot carry (`abort`: `i32` parameters) | records with opcodes `0x240`/`0x241`/`0x242` that **no chip's FETCH query can produce** |

## Admitted-but-unchipped instructions

A record whose opcode no instruction chip can send is never fetched by a satisfied trace: every
STATE transition is one chip row, and that row's FETCH query carries the chip's own opcode
expression (a combination of boolean flags with values `≤ 0x1FF`).  So the STATE chain can never
pass through such a pc, and a proof covers exactly the runs that do not execute it.  This is sound
and incomplete; the trace generator refuses a run that reaches one (`unchipped opcode`), and the M3
sweep lists those calls as the remainder.

## `if` with a result

The spec pushes `mkIfLabel bt e (h − 1)` with `arity = |results|` on both arms.  The true arm ends
at `else_`, which is CTRL's jump to the label target; the jump does not move operands, so the arm
must end at exactly `label.height + label.arity` (no discard), and the else body starts again at
`label.height`.  Only the static data changes (`analyzeM2`'s `.else_` resets the height;
`verifyAtM2` checks `h = height + arity` at `.else_`).  An `if` with a result and no `else` is
invalid Wasm (validation), and is rejected here too (`el ≠ e`).
-/
namespace WasmBase
open NearSpecV3.Wasm

/-- Conversion opcodes of the `CONV` chip. -/
def isConvOp (op : Nat) : Bool := op == 0xA7 || op == 0xAC || op == 0xAD

/-- FETCH opcode of `unreachable` (the Wasm byte). -/
def opUnreach : Nat := 0x00
/-- Admitted, no chip: `memory.grow`, `memory.size`, a host call outside the HOST row's shape. -/
def opMemGrowX : Nat := 0x240
def opMemSizeX : Nat := 0x241
def opHostX : Nat := 0x242

/-- The M2 host table: `hostFns` plus `ed25519_verify` (id 61, fresh; every existing id stays). -/
def hostFnsM2 : List (Nat × String × Nat × Nat) := Chips.hostFns ++ [(61, "ed25519_verify", 6, 1)]

def hostIdOfM2 (name : String) : Option Nat := (hostFnsM2.find? (fun x => x.2.1 = name)).map (·.1)

/-- Host id and signature an import call **with a HOST row** (np ≤ 9, ar ≤ 1, `i64` parameters). -/
def hostChipM2 (name : String) : Option (Nat × Nat × Nat) :=
  (hostFnsM2.find? (fun x => x.2.1 = name && Chips.hostShapeOk x.2.2.1 x.2.2.2 && Chips.hostArgsI64 name)).map
    fun x => (x.1, x.2.2.1, x.2.2.2)

/-- Signature of any listed host (also those without a HOST row: admitted, no chip). -/
def hostAnyM2 (name : String) : Option (Nat × Nat) :=
  (hostFnsM2.find? (fun x => x.2.1 = name)).map fun x => (x.2.2.1, x.2.2.2)

def importName (p : Prepared) (fi : Nat) : Option String :=
  (p.m.imports[fi]?).bind fun im => if im.kind = 0 then some im.name else none

/-- Signature of a call target in the M2 domain. -/
def sigOfM2 (p : Prepared) (fi : Nat) : Option (Nat × Nat) :=
  if fi < p.m.imports.size then (importName p fi).bind hostAnyM2 else sigOf p fi

/-- Kind of a straight-line instruction in the M2 domain. -/
def kindM2 (ls : List Label) : Instr → Option Kind
  | .num op => if isConvOp op then some (.straight 1 1) else kindOf ls (.num op)
  | .memGrow => some (.straight 1 1)
  | .memSize => some (.straight 0 1)
  | i => kindOf ls i

/-- Static `if` step admitting one result (`arity ≤ 1`, and an `else` when it has a result). -/
def ifStepM2 (pf : PFunc) (ls : List Label) (h pc : Nat) (bt : BT) :
    Option (List Label × Nat × Nat × List Label × Nat) :=
  if (btResults bt).size ≤ 1 then
    match pf.endOf[pc]?, pf.elseOf[pc]? with
    | some e, some el =>
      if 1 ≤ h ∧ ((btResults bt).size = 0 ∨ el ≠ e) then
        let lab := mkIfLabel bt e (h - 1)
        some (lab :: ls, h - 1, el + 1, (if el = e then ls else lab :: ls), h - 1)
      else none
    | _, _ => none
  else none

/-- Static pass of the M2 domain. -/
def analyzeM2 (p : Prepared) (pf : PFunc) : Option (Array (List Label) × Array Nat) := Id.run do
  let n := pf.code.size
  let mut ls : List Label := [rootLabel pf]
  let mut h : Nat := 0
  let mut dead := false
  let mut L : Array (List Label) := #[]
  let mut H : Array Nat := #[]
  for pc in [0:n] do
    let some ins := pf.code[pc]? | return none
    if dead then
      match ins, ls with
      | .end_, lab :: rest@(_ :: _) =>
        L := L.push ls; H := H.push (lab.height + lab.arity)
        ls := rest; h := lab.height + lab.arity; dead := false
      | .end_, [lab] =>
        L := L.push ls; H := H.push (lab.height + lab.arity); dead := false
      | _, _ => return none
    else
      L := L.push ls
      H := H.push h
      match ins with
      | .block bt =>
        match pf.endOf[pc]? with
        | some e =>
          ls := { target := e + 1, arity := (btResults bt).size, height := h, isLoop := false } :: ls
        | none => return none
      | .loop none =>
        ls := { target := pc + 1, arity := 0, height := h, isLoop := true } :: ls
      | .if_ bt =>
        match ifStepM2 pf ls h pc bt with
        | some (lsT, hT, _, _, _) => ls := lsT; h := hT
        | none => return none
      -- the else body starts at the label's height (the true arm left `arity` results above it)
      | .else_ =>
        match ls with
        | lab :: _ => h := lab.height
        | [] => return none
      | .end_ =>
        match ls with
        | _ :: rest@(_ :: _) => ls := rest
        | _ => dead := true
      | .br _ | .ret | .unreachable => dead := true
      | .brIf _ => h := h - 1
      | .call fi =>
        match sigOfM2 p fi with
        | some (np, ar) => if h < np then return none else h := h - np + ar
        | none => return none
      | i =>
        match kindM2 ls i with
        | some (.straight pops pushes) => if h < pops then return none else h := h - pops + pushes
        | _ => return none
  return some (L, H)

/-- Successor obligations of the M2 domain. -/
def verifyAtM2 (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) : Bool :=
  match pf.code[pc]?, L[pc]?, H[pc]? with
  | some ins, some ls, some h =>
    let atQ (q : Nat) (ls' : List Label) (h' : Nat) : Bool :=
      decide (q < pf.code.size) && decide (L[q]? = some ls') && decide (H[q]? = some h')
    match ins with
    | .if_ bt => match ifStepM2 pf ls h pc bt with
      | some (lsT, hT, ftgt, lsF, hF) => atQ (pc + 1) lsT hT && atQ ftgt lsF hF
      | none => false
    | .else_ => match ls with
      | lab :: rest => decide (h = lab.height + lab.arity) && atQ lab.target rest h
      | [] => false
    | .call fi => match sigOfM2 p fi with
      | some (np, ar) => decide (np ≤ h) && atQ (pc + 1) ls (h - np + ar)
      | none => false
    | .unreachable => true
    | .num op => if isConvOp op then decide (1 ≤ h) && atQ (pc + 1) ls h else verifyAt p pf L H pc
    | .memGrow => decide (1 ≤ h) && atQ (pc + 1) ls h
    | .memSize => atQ (pc + 1) ls (h + 1)
    | _ => verifyAt p pf L H pc
  | _, _, _ => false

def structOkM2 (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) : Bool :=
  decide (L.size = pf.code.size) && decide (H.size = pf.code.size) &&
  decide (L[0]? = some [rootLabel pf]) && decide (H[0]? = some 0) &&
  (List.range pf.code.size).all (fun pc => verifyAtM2 p pf L H pc && decide (H[pc]?.getD 0 < 2 ^ 16))

/-- Record of one pc in the M2 domain. -/
def recordAtM2 (cfg : NearCfg) (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat)
    (off : Nat) (cinfo : Nat → Option Nat) (pc : Nat) : Option (List Nat) :=
  match pf.code[pc]?, feeUnits cfg pf.gas[pc]? with
  | some ins, some fee =>
    let h := H[pc]?.getD 0
    match ins with
    | .if_ bt =>
      match pf.endOf[pc]?, pf.elseOf[pc]? with
      | some _e, some el => some [off + pc, Chips.IfC.opIf, h, fee, el + 1 + off, 0, 0, 0]
      | _, _ => none
    | .else_ =>
      match L[pc]? with
      | some (lab :: _) => some [off + pc, Chips.Ctrl.opJump, h, fee, lab.target + off, 0, 0, 0]
      | _ => none
    | .call fi =>
      if fi < p.m.imports.size then
        match (importName p fi).bind hostChipM2 with
        | some (hid, np, ar) => some [off + pc, Chips.opHost, h, fee, hid, np, ar, 0]
        | none => match (importName p fi).bind hostAnyM2 with
          | some (np, ar) => some [off + pc, opHostX, h, fee, 0, np, ar, 0]
          | none => none
      else recordOf off cinfo (L[pc]?.getD []) h fee (off + pc) ins
    | .num op => if isConvOp op then some [off + pc, op, h, fee, 0, 0, 0, 0]
      else recordOf off cinfo (L[pc]?.getD []) h fee (off + pc) ins
    | .unreachable => some [off + pc, opUnreach, h, fee, 0, 0, 0, 0]
    | .memGrow => some [off + pc, opMemGrowX, h, fee, 0, 0, 0, 0]
    | .memSize => some [off + pc, opMemSizeX, h, fee, 0, 0, 0, 0]
    | _ => recordOf off cinfo (L[pc]?.getD []) h fee (off + pc) ins
  | some .memGrow, none =>
    -- `memory.grow` carries a linear fee (`fee.l ≠ 0`); it has no chip, so the record only has to
    -- exist (no chip can fetch it) and its fee field is 0
    some [off + pc, opMemGrowX, H[pc]?.getD 0, 0, 0, 0, 0, 0]
  | _, _ => none

def checkM2 (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk cfg pf then
      match analyzeM2 p pf with
      | none => none
      | some (L, H) =>
        if structOkM2 p pf L H then
          match (List.range pf.code.size).mapM (recordAtM2 cfg p pf L H off cinfo) with
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

/-- Every import the closure calls is a listed host (P3). -/
def calledImportsOkM2 (p : Prepared) (fns : List Nat) : Bool :=
  fns.all fun fn =>
    match p.funcs[fn]? with
    | none => false
    | some pf => pf.code.all fun i => match i with
      | .call fi => if fi < p.m.imports.size then ((importName p fi).bind hostAnyM2).isSome else true
      | _ => true

/-- **The E2E M2 checker.** -/
def checkModuleM2 (cfg : NearCfg) (p : Prepared) (entry : Nat) : Option ModOutH :=
  let fns := closureFns p entry
  match fns.mapM (fun fn => p.funcs[fn]?) with
  | none => none
  | some pfs =>
  let sizes := pfs.map (·.code.size)
  let offs := prefixOffs sizes 0
  let cinfo := callInfo p fns offs
  match (List.range fns.length).mapM (fun k => checkM2 cfg p (fns.getD k 0) (offs.getD k 0) cinfo) with
  | none => none
  | some cks =>
    let total := sizes.foldl (· + ·) 0
    let recs := (List.range total).map fun j =>
      let kl := locate offs sizes j
      ((cks.getD kl.1 default).records)[kl.2]?.getD []
    if fns.head? = some entry ∧ total < 2 ^ 20 ∧ layoutOk fns offs sizes total = true ∧
        fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (fns.contains ·)) ∧
        (pfs.head?.map (·.type.params.size)) = some 0 ∧
        calledImportsOkM2 p fns = true then
      some { mod := { fns, cks, offs, sizes, codeSize := total, records := recs.toArray,
                      maxFee := (cks.map (·.maxFee)).foldl max 0 + (cks.map (·.prologue)).foldl max 0,
                      funcs := (List.range fns.length).map fun k => funcRow (offs.getD k 0) (cks.getD k default) },
             hostRows := hostFnsM2.map fun x => Chips.hostRow x.1 x.2.2.1 x.2.2.2 }
    else none

/-! ## Facts the extension rests on -/

/-- The new host id is fresh. -/
theorem hostFnsM2_ids_nodup : (hostFnsM2.map (·.1)).Nodup := by decide +kernel

/-- `ed25519_verify`'s table entry agrees with the PV86 linker signature (6 `i64` → `i64`). -/
theorem ed25519_sig_agrees :
    (Chips.hostSig? "ed25519_verify").map (fun t => (t.params.size, t.results.size)) = some (6, 1) ∧
    Chips.hostArgsI64 "ed25519_verify" = true := by
  constructor <;> decide +kernel

/-- An `if` with a result needs an `else`: the false successor then carries the label. -/
theorem ifStepM2_result_else {pf : PFunc} {ls : List Label} {h pc : Nat} {bt : BT}
    {lsT lsF : List Label} {hT ftgt hF : Nat} {e el : Nat}
    (he : pf.endOf[pc]? = some e) (hel : pf.elseOf[pc]? = some el) (hr : (btResults bt).size = 1)
    (hs : ifStepM2 pf ls h pc bt = some (lsT, hT, ftgt, lsF, hF)) :
    el ≠ e ∧ lsF = mkIfLabel bt e (h - 1) :: ls ∧ lsT = lsF ∧ hT = h - 1 ∧ hF = h - 1 := by
  unfold ifStepM2 at hs
  rw [he, hel] at hs
  simp only [hr] at hs
  split at hs
  · split at hs
    · rename_i hc
      have hne : el ≠ e := by omega
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      rw [if_neg hne] at hs
      obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hs
      exact ⟨hne, rfl, rfl, rfl, rfl⟩
    · simp at hs
  · simp at hs

end WasmBase
