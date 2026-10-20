import WasmBase.HostChip
import WasmBase.CheckFacts
/-!
# WasmBase.HostCheck — host-aware checker (`call` of a declared import)

Extends `WasmBase.check`/`checkModule` without touching them:

* an import call is a straight-line instruction with the signature `(np, ar)` of the **fixed host
  table** (`Chips.hostChipIdOf` / `Chips.hostChipSig`, which reject a listed function whose `(np, ar)`
does not fit the HOST message shape — only `validator_stake`, `np = 3`), and the code record `[pc, opHost, h, fee, hid, np, ar, 0]`;
* `analyzeH` / `verifyAtH` / `structOkH` / `recordAtH` are the same static pass with that extra case;
* `checkModuleH` additionally requires every import to be a function import declared in the host
  table and returns the checked functions, their code records and the cachec HOSTT rows.

Every condition is decidable (`hostChipIdOf` is a `find?` over a fixed list).
-/
namespace WasmBase
open NearSpecV3.Wasm

/-- Signature of a call target in the host-aware domain. -/
def sigOfH (p : Prepared) (fi : Nat) : Option (Nat × Nat) :=
  if fi < p.m.imports.size then
    match p.m.imports[fi]? with
    | some im => if im.kind = 0 then (Chips.hostChipIdOf im.name).bind Chips.hostChipSig else none
    | none => none
  else sigOf p fi

/-- Host id of an import call. -/
def hostOf (p : Prepared) (fi : Nat) : Option Nat :=
  if fi < p.m.imports.size then
    (p.m.imports[fi]?).bind fun im => if im.kind = 0 then Chips.hostIdOf im.name else none
  else none

/-- Static pass, host-aware. -/
def analyzeH (p : Prepared) (pf : PFunc) : Option (Array (List Label) × Array Nat) := Id.run do
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
      | .end_ =>
        match ls with
        | _ :: rest@(_ :: _) => ls := rest
        | _ => dead := true
      | .br _ | .ret => dead := true
      | .brIf _ => h := h - 1
      | .call fi =>
        match sigOfH p fi with
        | some (np, ar) => if h < np then return none else h := h - np + ar
        | none => return none
      | i =>
        match kindOf ls i with
        | some (.straight pops pushes) => if h < pops then return none else h := h - pops + pushes
        | _ => return none
  return some (L, H)

/-- Successor obligations, host-aware. -/
def verifyAtH (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (pc : Nat) : Bool :=
  match pf.code[pc]?, L[pc]?, H[pc]? with
  | some ins, some ls, some h =>
    let fnAr := pf.type.results.size
    let atQ (q : Nat) (ls' : List Label) (h' : Nat) : Bool :=
      decide (q < pf.code.size) && decide (L[q]? = some ls') && decide (H[q]? = some h')
    match ins with
    | .call fi => match sigOfH p fi with
      | some (np, ar) => decide (np ≤ h) && atQ (pc + 1) ls (h - np + ar)
      | none => false
    | i => verifyAt p pf L H pc
  | _, _, _ => false

/-- Static structure with the host-aware successor check. -/
def structOkH (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) : Bool :=
  decide (L.size = pf.code.size) && decide (H.size = pf.code.size) &&
  decide (L[0]? = some [rootLabel pf]) && decide (H[0]? = some 0) &&
  (List.range pf.code.size).all (fun pc => verifyAtH p pf L H pc && decide (H[pc]?.getD 0 < 2 ^ 16))

/-- Record of one pc, host-aware. -/
def recordAtH (cfg : NearCfg) (p : Prepared) (pf : PFunc) (L : Array (List Label)) (H : Array Nat) (off : Nat)
    (cinfo : Nat → Option Nat) (pc : Nat) : Option (List Nat) :=
  match pf.code[pc]?, feeUnits cfg pf.gas[pc]? with
  | some ins, some fee =>
    match ins with
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

/-- A function's check, host-aware. -/
def checkH (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) : Option CheckOut :=
  match p.funcs[fn]? with
  | none => none
  | some pf =>
    if basicOk cfg pf then
      match analyzeH p pf with
      | none => none
      | some (L, H) =>
        if structOkH p pf L H then
          match (List.range pf.code.size).mapM (recordAtH cfg p pf L H off cinfo) with
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

/-- The host-aware module output: `ModOut` plus the cached HOSTT rows. -/
structure ModOutH where
  mod : ModOut
  /-- cached host-table rows used by the module's imports, in host-id order -/
  hostRows : List (List Nat)

/-- Module-level eligibility check from entry function `entry`, host-aware. -/
def checkModuleH (cfg : NearCfg) (p : Prepared) (entry : Nat) : Option ModOutH :=
  let fns := closureFns p entry
  match fns.mapM (fun fn => p.funcs[fn]?) with
  | none => none
  | some pfs =>
  let sizes := pfs.map (·.code.size)
  let offs := prefixOffs sizes 0
  let cinfo := callInfo p fns offs
  match (List.range fns.length).mapM (fun k => checkH cfg p (fns.getD k 0) (offs.getD k 0) cinfo) with
  | none => none
  | some cks =>
    let total := sizes.foldl (· + ·) 0
    let recs := (List.range total).map fun j =>
      let kl := locate offs sizes j
      ((cks.getD kl.1 default).records)[kl.2]?.getD []
    if fns.head? = some entry ∧ total < 2 ^ 20 ∧ layoutOk fns offs sizes total = true ∧
        fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (fns.contains ·)) ∧
        (pfs.head?.map (·.type.params.size)) = some 0 ∧
        p.m.imports.all (fun im => im.kind = 0 ∧ (Chips.hostChipIdOf im.name).isSome) then
      some { mod := { fns, cks, offs, sizes, codeSize := total, records := recs.toArray,
                      maxFee := (cks.map (·.maxFee)).foldl max 0 + (cks.map (·.prologue)).foldl max 0,
                      funcs := (List.range fns.length).map fun k => funcRow (offs.getD k 0) (cks.getD k default) },
             hostRows := Chips.hostFns.map fun x => Chips.hostRow x.1 x.2.2.1 x.2.2.2 }
    else none

end WasmBase
