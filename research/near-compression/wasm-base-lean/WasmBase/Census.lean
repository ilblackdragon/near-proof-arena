import WasmBase.M2Check
/-!
# WasmBase.Census — why a module is outside the checker's domain (E2E M2 census)

Diagnostic only: no proof uses it.  For the closure of an export it lists, per function, the
reasons `checkModuleIfH` would reject it: the `basicOk` sub-conditions, the instructions
`kindOf`/`sigOfH`/`ifStep` do not admit, the static pass failing, and the pcs whose successor
obligation (`verifyAtIfH`) fails (in practice: branches that discard operands).
-/
namespace WasmBase
open NearSpecV3.Wasm

/-- A short name of an instruction (the constructor and its immediates). -/
def insName : Instr → String
  | .num op => s!"num:0x{String.ofList (Nat.toDigits 16 op)}"
  | .float op => s!"float:0x{String.ofList (Nat.toDigits 16 op)}"
  | .load op _ _ => s!"load:0x{String.ofList (Nat.toDigits 16 op)}"
  | .store op _ _ => s!"store:0x{String.ofList (Nat.toDigits 16 op)}"
  | .if_ bt => s!"if:{(btResults bt).size}"
  | .block bt => s!"block:{(btResults bt).size}"
  | .loop bt => s!"loop:{(btResults bt).size}"
  | .call _ => "call"
  | .callIndirect _ _ => "call_indirect"
  | .memGrow => "memory.grow" | .memSize => "memory.size"
  | .memCopy => "memory.copy" | .memFill => "memory.fill"
  | .unreachable => "unreachable" | .nop => "nop"
  | .brTable _ _ => "br_table"
  | i => ((reprStr i).takeWhile (· != ' ')).toString

/-- Local (per-instruction) reasons. -/
def insReason (p : Prepared) (i : Instr) : Option String :=
  match i with
  | .call fi =>
    if fi < p.m.imports.size then
      let nm := (p.m.imports[fi]?.map (·.name)).getD "?"
      match hostOf p fi, sigOfH p fi with
      | none, _ => some s!"host-missing:{nm}"
      | _, none => some s!"host-shape:{nm}"
      | _, _ => none
    else if (sigOf p fi).isNone then some "call-target" else none
  | .if_ bt => if ifShapeOk bt then none else some (insName i)
  | .else_ | .block _ | .loop none | .end_ | .br _ | .brIf _ | .ret => none
  | i => match kindOf [] i with
    | some (.straight _ _) => none
    | _ => some (insName i)

def basicReasons (cfg : NearCfg) (pf : PFunc) : List String :=
  (if pf.type.params.size ≤ 8 then [] else ["params>8"]) ++
  (if pf.type.params.size + pf.locals.size ≤ 64 then [] else ["locals>64"]) ++
  (if pf.type.results.size ≤ 1 then [] else ["results>1"]) ++
  (if pf.locals.all (fun t => t == .i32 || t == .i64) then [] else ["local-type"]) ++
  (if pf.type.params.all (fun t => t == .i32 || t == .i64) then [] else ["param-type"]) ++
  (if pf.type.results.all (fun t => t == .i32 || t == .i64) then [] else ["result-type"]) ++
  (if pf.gas.size = pf.code.size then [] else ["gas-size"]) ++
  (if pf.stackCharge < 2 ^ 26 then [] else ["stack-charge"]) ++
  (if pf.prologueGas % cfg.regularOpCost = 0 then [] else ["prologue"]) ++
  (if (List.range pf.code.size).all (fun pc => (feeUnits cfg pf.gas[pc]?).isSome) then [] else ["fee"])

/-- All reasons for one function (deduplicated, with counts). -/
def fnReasons (cfg : NearCfg) (p : Prepared) (fn : Nat) : List String := Id.run do
  let some pf := p.funcs[fn]? | return ["no-func"]
  let mut rs : List String := basicReasons cfg pf
  for i in pf.code.toList do
    if let some r := insReason p i then rs := rs ++ [r]
  if rs.isEmpty then
    match analyzeIfH p pf with
    | none => rs := rs ++ ["analyze"]
    | some (L, H) =>
      for pc in List.range pf.code.size do
        if !verifyAtIfH p pf L H pc then
          rs := rs ++ [s!"verify:{(pf.code[pc]?.map insName).getD "?"}"]
  return rs

def countDistinct (xs : List String) : List (String × Nat) :=
  xs.foldl (fun acc x => match acc.find? (·.1 = x) with
    | some _ => acc.map fun (y, n) => if y = x then (y, n + 1) else (y, n)
    | none => acc ++ [(x, 1)]) []

/-- The census of an export: per function in the closure, its rejection reasons. -/
def census (cfg : NearCfg) (p : Prepared) (entry : Nat) : List (Nat × List (String × Nat)) :=
  (closureFns p entry).map fun fn => (fn, countDistinct (fnReasons cfg p fn))

/-! ## The same census against the M2 checker (`checkModuleM2`) -/

def insReasonM2 (p : Prepared) (i : Instr) : Option String :=
  match i with
  | .call fi =>
    if fi < p.m.imports.size then
      let nm := (importName p fi).getD "?"
      match (importName p fi).bind hostAnyM2 with
      | none => some s!"host-missing:{nm}"
      | some _ => if ((importName p fi).bind hostChipM2).isNone then some s!"unchipped-host:{nm}" else none
    else if (sigOf p fi).isNone then some "call-target" else none
  | .if_ bt => if (btResults bt).size ≤ 1 then none else some (insName i)
  | .memGrow | .memSize => some s!"unchipped:{insName i}"
  | .else_ | .block _ | .loop none | .end_ | .br _ | .brIf _ | .ret | .unreachable => none
  | i => match kindM2 [] i with
    | some (.straight _ _) => none
    | _ => some (insName i)

/-- Reasons against `checkM2`; `unchipped` entries are admitted (no chip), the rest reject. -/
def fnReasonsM2 (cfg : NearCfg) (p : Prepared) (fn : Nat) : List String := Id.run do
  let some pf := p.funcs[fn]? | return ["no-func"]
  let mut rs : List String := (basicReasons cfg pf).filter (· != "fee")
  for i in pf.code.toList do
    if let some r := insReasonM2 p i then rs := rs ++ [r]
  match analyzeM2 p pf with
  | none => rs := rs ++ ["analyze"]
  | some (L, H) =>
    for pc in List.range pf.code.size do
      if !verifyAtM2 p pf L H pc then
        rs := rs ++ [s!"verify:{(pf.code[pc]?.map insName).getD "?"}"]
      if (recordAtM2 cfg p pf L H 0 (fun _ => some 0) pc).isNone then
        rs := rs ++ [s!"record:{(pf.code[pc]?.map insName).getD "?"}"]
  return rs

def censusM2 (cfg : NearCfg) (p : Prepared) (entry : Nat) : List (Nat × List (String × Nat)) :=
  (closureFns p entry).map fun fn => (fn, countDistinct (fnReasonsM2 cfg p fn))

end WasmBase
