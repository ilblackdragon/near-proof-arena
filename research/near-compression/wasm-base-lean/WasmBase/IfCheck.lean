import WasmBase.HostCheck
import WasmBase.StepIf
/-!
# WasmBase.IfCheck — the checker extension for `if`

`WasmBase.Check`'s `kindOf` has no `.if_`/`.else_` case, so no real NEAR contract is in the
base-layer domain: `d3tiny` has one `if`, `ttn2` twelve, `d3rich` seventy-seven.  `StepIf.lean`
proved the *spec* step (`step_if`, `step_else`, `popN_snd`); `Chips.IfC` added the `IF` row.  This
module supplies the missing *checker*: the static analysis, the successor obligations, and the code
records, for a domain that admits `if`/`else`.

## The shape of the extension

It follows `HostCheck.lean`'s discipline exactly — **extend, don't touch**: `analyze`, `verifyAt`,
`recordOf`, `check` and `checkModule` are unchanged, so every existing proof, table index and
cached export keeps its meaning.  `wasmBaseAir` stays byte-identical (the `IF` table lives in the
separate `wasmBaseIfAir` / `wasmBaseIfHostAir`).

## What `if` needs beyond `block`

`block` advances to `pc + 1` at the same height.  `if` pops its condition and has **two**
successors, both of which get the same pushed label:

| successor | when | labels | height |
|---|---|---|---|
| `pc + 1` | condition `≠ 0` (falls through) | `lab :: ls` | `h - 1` |
| `elseOf + 1` | condition `= 0` with an `else` | `lab :: ls` | `h - 1` |
| `endOf + 1` | condition `= 0`, no `else` | `ls` (**no push**) | `h - 1` |

where `lab = mkIfLabel bt endOf (h - 1)`.  The third row is why this is not `block` with two
targets: with no `else`, the spec pushes **no** label, because the `end` it jumps to is the one that
already encloses the `if` (`matchBlocks` records `elseOf[i] = endOf[i]` precisely to mark that).

`elseOf = endOf` is therefore the discriminator, and it is exactly what `prepare`'s `matchBlocks`
writes.  The **AIR does not need it**: both shapes send `pc' = elseOf + 1`, which is the same
number, so `IfC.tgt` covers both and only the static label list differs.
-/
namespace WasmBase
open NearSpecV3.Wasm

deriving instance DecidableEq for NearSpecV3.Wasm.BT

/-- `if` with a result keeps its own operand stack; the domain admits only the no-result shape,
which is what every real contract uses in the `if`-as-branch position.  Restricting here keeps
`btResults` out of the height arithmetic. -/
def ifShapeOk (bt : BT) : Bool := (btResults bt).size == 0

/-- Static `if` step: the condition pop and the two successors, or `none` outside the domain. -/
def ifStep (p : Prepared) (pf : PFunc) (ls : List Label) (h pc : Nat) (bt : BT) :
    Option (List Label × Nat × Nat × List Label × Nat) :=
  if ifShapeOk bt then
    match pf.endOf[pc]?, pf.elseOf[pc]? with
    | some e, some el =>
      if 1 ≤ h then
        let lab := mkIfLabel bt e (h - 1)
        some (lab :: ls, h - 1, el + 1, (if el = e then ls else lab :: ls), h - 1)
      else none
    | _, _ => none
  else none

/-- Static analysis, `if`-aware.  Identical to `analyze` except at `.if_` and `.else_`. -/
def analyzeIf (p : Prepared) (pf : PFunc) : Option (Array (List Label) × Array Nat) := Id.run do
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
      -- A dead `.else_` means the true arm ended in an unconditional transfer.  The else body is
      -- still reachable through the `if`'s false branch, but this linear pass no longer knows the
      -- label stack or height it needs, so this shape is **out of the domain** (an explicit,
      -- decidable restriction; `d3rich` does not need it).  Accepting it silently would be the
      -- "test passes, meaning is missing" failure.
      | .else_, _ | _, _ => return none
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
      -- the new case: `if` falls through at the pushed label
      | .if_ bt =>
        match ifStep p pf ls h pc bt with
        | some (lsT, hT, _, _, _) => ls := lsT; h := hT
        | none => return none
      -- `.else_` is the true arm's **jump over the else body** to the label's target.  For this
      -- linear pass it is transparent: the else body that follows is reached by the `if`'s false
      -- branch with the *same* label stack (`lab :: ls`) and height (`h`), so the scan continues
      -- unchanged.  `verifyAtIf` checks the real jump.
      | .else_ => ()
      | .end_ =>
        match ls with
        | _ :: rest@(_ :: _) => ls := rest
        | _ => dead := true
      | .br _ | .ret => dead := true
      | .brIf _ => h := h - 1
      | .call fi =>
        match sigOf p fi with
        | some (np, ar) =>
          if h < np then return none
          h := h - np + ar
        | none => return none
      | i =>
        match kindOf ls i with
        | some (.straight pops pushes) =>
          if h < pops then return none
          h := h - pops + pushes
        | _ => return none
  return some (L, H)

/-- Successor obligations, `if`-aware: both arms must agree with the static data, the `else`-less
shape must **not** push a label, and `.else_` must jump to the head label's target. -/
def verifyAtIf (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) : Bool :=
  match pf.code[pc]?, L[pc]?, H[pc]? with
  | some ins, some ls, some h =>
    let atQ (q : Nat) (ls' : List Label) (h' : Nat) : Bool :=
      decide (q < pf.code.size) && decide (L[q]? = some ls') && decide (H[q]? = some h')
    match ins with
    | .if_ bt => match ifStep p pf ls h pc bt with
      | some (lsT, hT, ftgt, lsF, hF) => atQ (pc + 1) lsT hT && atQ ftgt lsF hF
      | none => false
    | .else_ => match ls with
      | lab :: rest => atQ lab.target rest h
      | [] => false
    | i => verifyAt p pf L H pc
  | _, _, _ => false

/-- Static structure with the `if`-aware successor check. -/
def structOkIf (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) : Bool :=
  decide (L.size = pf.code.size) && decide (H.size = pf.code.size) &&
  decide (L[0]? = some [rootLabel pf]) && decide (H[0]? = some 0) &&
  (List.range pf.code.size).all (fun pc => verifyAtIf p pf L H pc && decide (H[pc]?.getD 0 < 2 ^ 16))

/-- Record of one pc, `if`-aware.  The record must match the `IF` row's FETCH query exactly, and that
query carries only the **false** target in `x0` (the label target is checker-side data — the AIR does
not need it, since both `if` shapes send the same `x0`).  So `x1..x3` are zero like CTRL's. -/
def recordAtIf (cfg : NearCfg) (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat)
    (off : Nat) (cinfo : Nat → Option Nat) (pc : Nat) : Option (List Nat) :=
  match pf.code[pc]?, feeUnits cfg pf.gas[pc]? with
  | some ins, some fee =>
    match ins with
    | .if_ bt =>
      match pf.endOf[pc]?, pf.elseOf[pc]? with
      | some _e, some el => some [off + pc, Chips.IfC.opIf, H[pc]?.getD 0, fee, el + 1 + off, 0, 0, 0]
      | _, _ => none
    -- `.else_` is the existing `Ctrl.fJump` to the label it pops (`step_else` proves exactly that),
    -- so it needs no new opcode: the AIR row is CTRL's `f_jump` with `tgt = lab.target`.
    | .else_ =>
      match L[pc]? with
      | some (lab :: _) => some [off + pc, Chips.Ctrl.opJump, H[pc]?.getD 0, fee, lab.target + off, 0, 0, 0]
      | _ => none
    | _ => recordOf off cinfo (L[pc]?.getD []) (H[pc]?.getD 0) fee (off + pc) ins
  | _, _ => none

/-- A function's check, `if`-aware. -/
def checkIf (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk cfg pf then
      match analyzeIf p pf with
      | none => none
      | some (L, H) =>
        if structOkIf p pf L H then
          match (List.range pf.code.size).mapM (recordAtIf cfg p pf L H off cinfo) with
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

/-- Module-level eligibility check from entry function `entry`, `if`-aware.  This is the check that
decides `eligible` for a module whose functions contain `if`/`else`; everything else is `check`'s. -/
def checkModuleIf (cfg : NearCfg) (p : Prepared) (entry : Nat) : Option ModOut :=
  let fns := closureFns p entry
  match fns.mapM (fun fn => p.funcs[fn]?) with
  | none => none
  | some pfs =>
  let sizes := pfs.map (·.code.size)
  let offs := prefixOffs sizes 0
  let cinfo := callInfo p fns offs
  match (List.range fns.length).mapM (fun k => checkIf cfg p (fns.getD k 0) (offs.getD k 0) cinfo) with
  | none => none
  | some cks =>
    let total := sizes.foldl (· + ·) 0
    let recs := (List.range total).map fun j =>
      let kl := locate offs sizes j
      ((cks.getD kl.1 default).records)[kl.2]?.getD []
    if fns.head? = some entry ∧ total < 2 ^ 20 ∧ layoutOk fns offs sizes total = true ∧
        fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (fns.contains ·)) ∧
        (pfs.head?.map (·.type.params.size)) = some 0 then
      some { fns, cks, offs, sizes, codeSize := total, records := recs.toArray,
             maxFee := (cks.map (·.maxFee)).foldl max 0 + (cks.map (·.prologue)).foldl max 0,
             funcs := (List.range fns.length).map fun k => funcRow (offs.getD k 0) (cks.getD k default) }
    else none

/-! ## `if` **and** host calls together

Neither extension suffices for a real contract: every public D3 contract uses `if` **and** imports
host functions (`storage_write`, `log_utf8`, ...).  `checkModuleIf` above keeps `check`'s
non-host `sigOf`, so it rejects a `.call` to an import; `checkModuleH` rejects `.if_`.  The
composition is the one that matters, so it is built here by mirroring `HostCheck`'s three pieces
over `IfCheck`'s. -/

/-- Static pass, `if`- and host-aware. -/
def analyzeIfH (p : Prepared) (pf : PFunc) : Option (Array (List Label) × Array Nat) := Id.run do
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
      | .else_, _ | _, _ => return none
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
        match ifStep p pf ls h pc bt with
        | some (lsT, hT, _, _, _) => ls := lsT; h := hT
        | none => return none
      | .else_ => ()
      | .end_ =>
        match ls with
        | _ :: rest@(_ :: _) => ls := rest
        | _ => dead := true
      | .br _ | .ret => dead := true
      | .brIf _ => h := h - 1
      | .call fi =>
        match sigOfH p fi with
        | some (np, ar) =>
          if h < np then return none
          h := h - np + ar
        | none => return none
      | i =>
        match kindOf ls i with
        | some (.straight pops pushes) =>
          if h < pops then return none
          h := h - pops + pushes
        | _ => return none
  return some (L, H)

/-- Successor obligations, `if`- and host-aware. -/
def verifyAtIfH (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) : Bool :=
  match pf.code[pc]?, L[pc]?, H[pc]? with
  | some ins, some ls, some h =>
    let atQ (q : Nat) (ls' : List Label) (h' : Nat) : Bool :=
      decide (q < pf.code.size) && decide (L[q]? = some ls') && decide (H[q]? = some h')
    match ins with
    | .if_ bt => match ifStep p pf ls h pc bt with
      | some (lsT, hT, ftgt, lsF, hF) => atQ (pc + 1) lsT hT && atQ ftgt lsF hF
      | none => false
    | .else_ => match ls with
      | lab :: rest => atQ lab.target rest h
      | [] => false
    | .call fi => match sigOfH p fi with
      | some (np, ar) => decide (np ≤ h) && atQ (pc + 1) ls (h - np + ar)
      | none => false
    | i => verifyAt p pf L H pc
  | _, _, _ => false

/-- Static structure, `if`- and host-aware. -/
def structOkIfH (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) : Bool :=
  decide (L.size = pf.code.size) && decide (H.size = pf.code.size) &&
  decide (L[0]? = some [rootLabel pf]) && decide (H[0]? = some 0) &&
  (List.range pf.code.size).all (fun pc => verifyAtIfH p pf L H pc && decide (H[pc]?.getD 0 < 2 ^ 16))

/-- Record of one pc, `if`- and host-aware. -/
def recordAtIfH (cfg : NearCfg) (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat)
    (off : Nat) (cinfo : Nat → Option Nat) (pc : Nat) : Option (List Nat) :=
  match pf.code[pc]?, feeUnits cfg pf.gas[pc]? with
  | some ins, some fee =>
    match ins with
    | .if_ bt =>
      match pf.endOf[pc]?, pf.elseOf[pc]? with
      | some _e, some el => some [off + pc, Chips.IfC.opIf, H[pc]?.getD 0, fee, el + 1 + off, 0, 0, 0]
      | _, _ => none
    | .else_ =>
      match L[pc]? with
      | some (lab :: _) => some [off + pc, Chips.Ctrl.opJump, H[pc]?.getD 0, fee, lab.target + off, 0, 0, 0]
      | _ => none
    | .call fi =>
      if fi < p.m.imports.size then
        match hostOf p fi with
        | some hid => match sigOfH p fi with
          | some (np, ar) => some [off + pc, Chips.opHost, H[pc]?.getD 0, fee, hid, np, ar, 0]
          | none => none
        | none => none
      else recordOf off cinfo (L[pc]?.getD []) (H[pc]?.getD 0) fee (off + pc) ins
    | _ => recordOf off cinfo (L[pc]?.getD []) (H[pc]?.getD 0) fee (off + pc) ins
  | _, _ => none

/-- A function's check, `if`- and host-aware. -/
def checkIfH (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk cfg pf then
      match analyzeIfH p pf with
      | none => none
      | some (L, H) =>
        if structOkIfH p pf L H then
          match (List.range pf.code.size).mapM (recordAtIfH cfg p pf L H off cinfo) with
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

/-- **Which imports must be hosts.**  Per spec §10.0a **P3**, an excluded host function is out of
domain when **called**, not when imported: an uncalled import emits no row and cannot be reached by
the checked closure.  So the condition is not "every import is a host" (what `checkModuleH`
requires, and what rejects a real contract that merely *imports* `ecrecover`), but "every import the
closure actually calls is a host".

`recordAtIfH` already enforces the stronger local fact — it returns `none` for a `.call` to a
non-host import — so this predicate only has to cover call targets outside the closure's code.
It is stated separately so the difference from `checkModuleH` is explicit rather than implied. -/
def calledImportsOk (p : Prepared) (fns : List Nat) : Bool :=
  fns.all fun fn =>
    match p.funcs[fn]? with
    | none => false
    | some pf => pf.code.all fun i => match i with
      | .call fi => if fi < p.m.imports.size then (hostOf p fi).isSome else true
      | _ => true

/-- **The checker that matters for a real D3 contract**: `if` and host imports, together.  Same
module-level conditions as `checkModuleH` except the import condition, which follows P3
(`calledImportsOk`) instead of "every import is a host". -/
def checkModuleIfH (cfg : NearCfg) (p : Prepared) (entry : Nat) : Option ModOutH :=
  let fns := closureFns p entry
  match fns.mapM (fun fn => p.funcs[fn]?) with
  | none => none
  | some pfs =>
  let sizes := pfs.map (·.code.size)
  let offs := prefixOffs sizes 0
  let cinfo := callInfo p fns offs
  match (List.range fns.length).mapM (fun k => checkIfH cfg p (fns.getD k 0) (offs.getD k 0) cinfo) with
  | none => none
  | some cks =>
    let total := sizes.foldl (· + ·) 0
    let recs := (List.range total).map fun j =>
      let kl := locate offs sizes j
      ((cks.getD kl.1 default).records)[kl.2]?.getD []
    if fns.head? = some entry ∧ total < 2 ^ 20 ∧ layoutOk fns offs sizes total = true ∧
        fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (fns.contains ·)) ∧
        (pfs.head?.map (·.type.params.size)) = some 0 ∧
        calledImportsOk p fns = true then
      some { mod := { fns, cks, offs, sizes, codeSize := total, records := recs.toArray,
                      maxFee := (cks.map (·.maxFee)).foldl max 0 + (cks.map (·.prologue)).foldl max 0,
                      funcs := (List.range fns.length).map fun k => funcRow (offs.getD k 0) (cks.getD k default) },
             hostRows := Chips.hostFns.map fun x => Chips.hostRow x.1 x.2.2.1 x.2.2.2 }
    else none

/-! ## Sanity: the extension's two semantic facts

`ifStep` is the whole content of the extension, so it gets the two facts a later lane needs: both
shapes pop exactly one operand, and the `else`-less shape pushes **no** label. -/

/-- Both `if` shapes pop exactly one operand (the condition). -/
theorem ifStep_pop {p : Prepared} {pf : PFunc} {ls : List Label} {h pc : Nat} {bt : BT}
    {lsT lsF : List Label} {hT ftgt hF : Nat}
    (hs : ifStep p pf ls h pc bt = some (lsT, hT, ftgt, lsF, hF)) : hT = h - 1 ∧ hF = h - 1 := by
  unfold ifStep at hs
  split at hs
  · split at hs
    · split at hs
      · simp only [Option.some.injEq] at hs
        obtain ⟨-, rfl, -, -, rfl⟩ := hs
        exact ⟨rfl, rfl⟩
      · simp at hs
    · simp at hs
  · simp at hs

/-- **The structural difference from `block`.**  When `elseOf = endOf` — the spec's marker for an
`if` with no `else` (`Prepare.matchBlocks`) — the false successor pushes **no** label, so its label
list is the input list.  This is the fact `step_if_noelse` will consume. -/
theorem ifStep_noelse_ls {p : Prepared} {pf : PFunc} {ls : List Label} {h pc : Nat} {bt : BT}
    {lsT lsF : List Label} {hT ftgt hF : Nat} {e : Nat}
    (he : pf.endOf[pc]? = some e) (hel : pf.elseOf[pc]? = some e)
    (hs : ifStep p pf ls h pc bt = some (lsT, hT, ftgt, lsF, hF)) : lsF = ls := by
  unfold ifStep at hs
  split at hs
  · split at hs
    · rename_i e0 el0 he0 hel0
      rw [he] at he0
      rw [hel] at hel0
      simp only [Option.some.injEq] at he0 hel0
      subst he0 hel0
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs
        exact hs.2.2.2.1.symm
      · simp at hs
    · simp at hs
  · simp at hs

end WasmBase
