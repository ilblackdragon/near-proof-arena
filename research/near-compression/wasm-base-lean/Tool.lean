import WasmBase.Check
import WasmBase.HostChip
import WasmBase.RegChip
import WasmBase.HostCheck
import WasmBase.ShaAir
import WasmBase.ShaSound
/-!
`wasmbase-tool` — exporter and verifier-side preparation for the direct-Wasm base layer.

* `wasmbase-tool air <nloc> <ngl>`: the AIR `wasmBaseAir nloc ngl` as JSON (the Rust crate interprets it;
  `ngl` is the number of globals).
* `wasmbase-tool airH <nloc> <ngl>`: `wasmBaseHostAir` (the same tables plus HOST, HOSTO, HOSTT).
* `wasmbase-tool prep <file.wasm> <exportName> <g0>`: `prepare` (PV86), `check` of the exported function,
  and a reference execution with the spec's own `step` from the post-`enter` state with
  `gas.g = g0` (after the prologue charge), as JSON.
* `wasmbase-tool eval <nloc> <ngl> <points>`: evaluate every constraint, interaction count and message
  of `wasmBaseAir nloc ngl` at the given points (difftest; selectors are free field values).
* `wasmbase-tool evalH <nloc> <ngl> <points>`: the same for `wasmBaseHostAir`.
* `wasmbase-tool airX <nloc> <ngl>`: `wasmBaseHashAir` (= `wasmBaseHostAir` with `HOSTO`
  extended by the hash-call summary, plus the SHA256 table).
* `wasmbase-tool evalX <nloc> <ngl> <points>`: the same for `wasmBaseHashAir`.
* `wasmbase-tool airR <nloc> <ngl>`: `wasmBaseRegAir` (= `wasmBaseHostAir` plus the REG table).
* `wasmbase-tool evalR <nloc> <ngl> <points>`: the same for `wasmBaseRegAir`.
-/
open NearSpecV3.Wasm WasmBase ZkFormal.Algebra

def jList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
/-- JSON string literal, escaping `\` and `"` (host abort messages contain `rustDebugStr` quotes). -/
def jStr (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap fun c =>
    if c = '"' then ['\\', '"'] else if c = '\\' then ['\\', '\\']
    else if c = '\n' then ['\\', 'n'] else [c]) ++ "\""

def WasmBase.Expr.toJson : WasmBase.Expr → String
  | .c n => s!"[\"c\",{n}]"
  | .col i => s!"[\"v\",{i}]"
  | .nxt i => s!"[\"n\",{i}]"
  | .pub i => s!"[\"p\",{i}]"
  | .first => "[\"first\"]"
  | .last => "[\"last\"]"
  | .trans => "[\"trans\"]"
  | .add a b => s!"[\"+\",{a.toJson},{b.toJson}]"
  | .sub a b => s!"[\"-\",{a.toJson},{b.toJson}]"
  | .mul a b => s!"[\"*\",{a.toJson},{b.toJson}]"

def interJson (i : WasmBase.Inter) : String :=
  s!"\{\"bus\":{i.bus},\"send\":{i.send},\"count\":{Expr.toJson i.count},\"msg\":{jList (i.msg.map Expr.toJson)}}"

/-- Number of leading columns committed as a separate cached trace (CODE: the records; DATA: the
data image). -/
def cachedCols (T : Table) : Nat :=
  if T.name = "CODE" then Chips.Code.cachedWidth else if T.name = "DATA" then Chips.Data.cachedWidth
  else if T.name = "FUNC" then Chips.Func.cachedWidth else 0

/-- End of the data image: one past the last non-zero byte of the initial memory (0 if none). -/
def dataEnd (s : St) : Nat := Id.run do
  let mut e := 0
  for i in [0:s.pages.size] do
    let p := s.pages[i]!
    for j in [0:p.size] do
      if p.get! j != 0 then e := i * pageSize + j + 1
  return e

def tableJson (T : Table) : String :=
  s!"\{\"name\":{jStr T.name},\"cached\":{cachedCols T},\"cols\":{jList (T.cols.map jStr)},\"degree\":{(T.constraints ++ T.inters.flatMap (fun i => i.count :: i.msg)).foldl (fun m e => max m e.degree) 0},\"constraints\":{jList (T.constraints.map Expr.toJson)},\"inters\":{jList (T.inters.map interJson)}}"

def airJson (A : Air) : String :=
  s!"\{\"numPub\":{A.numPub},\"tables\":{jList (A.tables.map tableJson)}}"

/-- Generic evaluation with free selector values (difftest only). -/
def WasmBase.Expr.evalG (cur nxt pub : Nat → F) (sf sl st : F) : WasmBase.Expr → F
  | .c n => (n : F)
  | .col i => cur i
  | .nxt i => nxt i
  | .pub i => pub i
  | .first => sf
  | .last => sl
  | .trans => st
  | .add a b => a.evalG cur nxt pub sf sl st + b.evalG cur nxt pub sf sl st
  | .sub a b => a.evalG cur nxt pub sf sl st - b.evalG cur nxt pub sf sl st
  | .mul a b => a.evalG cur nxt pub sf sl st * b.evalG cur nxt pub sf sl st

def natList (xs : List Nat) : String := jList (xs.map toString)

def runSteps (cfg : NearCfg) (p : Prepared) : Nat → St → Nat → (Nat × Res)
  | 0, _, n => (n, .unmodeled "tool fuel")
  | k + 1, s, n => match step cfg p s with
    | .cont s' => runSteps cfg p k s' (n + 1)
    | r => (n + 1, r)

/-- One observed host call: `ts` is filled in by the trace generator; the rest is the spec's
outcome (`st = 0` success, `1` abort), the request arguments, the result word and the budget after
`g := remaining`. -/
structure HostEv where
  hid : Nat
  np : Nat
  ar : Nat
  args : List Nat
  st : Nat
  word : Nat
  gAfter : Nat
  /-- the register file the call left behind (`[id, bytes]`), i.e. what it filled -/
  regs : List (Nat × List Nat) := []
  deriving Inhabited

def hostEvJson (e : HostEv) : String :=
  "{\"hid\":" ++ toString e.hid ++ ",\"np\":" ++ toString e.np ++ ",\"ar\":" ++ toString e.ar ++
  ",\"args\":" ++ natList e.args ++ ",\"st\":" ++ toString e.st ++ ",\"word\":" ++ toString e.word ++
  ",\"gAfter\":" ++ toString e.gAfter ++
  ",\"regs\":" ++ jList ((e.regs).map fun (id, bs) =>
    "[" ++ toString id ++ "," ++ natList bs ++ "]") ++ "}"

/-- The signature of an import index, from the fixed host table. -/
def hostSigOf (p : Prepared) (fi : Nat) : Option (Nat × Nat × Nat) :=
  match hostOf p fi, sigOfH p fi with
  | some hid, some (np, ar) => some (hid, np, ar)
  | _, _ => none

/-- The host call at the current pc, if any. -/
def hostAt (p : Prepared) (s : St) : Option (Nat × Nat × Nat) :=
  match s.frames with
  | [] => none
  | f :: _ =>
    match p.funcs[f.fn]?, (p.funcs[f.fn]?).bind (fun pf => pf.code[f.pc]?) with
    | some _, some (.call fi) => if fi < p.m.imports.size then hostSigOf p fi else none
    | _, _ => none

/-- Run the spec, recording the abstract host responses at every import call (the response is read
off the spec's own outcome, so the trace generator reproduces the spec exactly). -/
def runStepsH (cfg : NearCfg) (p : Prepared) :
    Nat → St → Nat → List HostEv → (Nat × Res × List HostEv)
  | 0, _, n, evs => (n, .unmodeled "tool fuel", evs)
  | k + 1, s, n, evs =>
    match hostAt p s with
    | some (hid, np, ar) =>
      let sb := s.stack.size - np
      let args := (List.range np).map fun j =>
        (match s.stack[sb + j]?.getD (.i32 0) with
         | .i32 v => v.toNat
         | .i64 v => v.toNat
         | .ref _ => 0)
      match step cfg p s with
      | .cont os =>
        let word := if ar = 1 then
          (match os.stack.back?.getD (.i64 0) with
           | .i32 v => v.toNat
           | .i64 v => v.toNat
           | .ref _ => 0) else 0
        let ev : HostEv := { hid, np, ar, args, st := 0, word, gAfter := os.gas.g,
                             regs := os.registers.toList.map fun (id, d) => (id, d.toList.map (·.toNat)) }
        runStepsH cfg p k os (n + 1) (evs ++ [ev])
      | .abort os e =>
        let ev : HostEv := { hid, np, ar, args, st := 1, word := 0, gAfter := os.gas.g,
                             regs := os.registers.toList.map fun (id, d) => (id, d.toList.map (·.toNat)) }
        (n + 1, .abort os e, evs ++ [ev])
      | r => (n + 1, r, evs)
    | none =>
      match step cfg p s with
      | .cont s' => runStepsH cfg p k s' (n + 1) evs
      | r => (n + 1, r, evs)

def valLimbs : Val → (Nat × List Nat)
  | .i32 v => (0, limbs4 v.toNat)
  | .i64 v => (1, limbs4 v.toNat)
  | .ref _ => (2, [0, 0, 0, 0])

/-- Hex digits → bytes (`none` on a malformed string). -/
def hexBytes (s : String) : Option (List Nat) := Id.run do
  let cs := s.toList
  if cs.length % 2 != 0 then return none
  let mut out : List Nat := []
  let mut hi : Option Nat := none
  for c in cs do
    let d := "0123456789abcdef".toList.findIdx? (· = c.toLower)
    let some d := d | return none
    match hi with
    | none => hi := some d
    | some h => out := out ++ [h * 16 + d]; hi := none
  return some out

/-- `input` bytes from the optional hex argument (the `CallCtx.input` the state side would supply). -/
def prep (path exportName : String) (g0 : Nat) (inputHex : String := "") : IO Unit := do
  let code ← IO.FS.readBinFile path
  let cfg := pv86
  match prepare cfg code with
  | .ok p =>
    let nImp := p.m.imports.size
    let some (_, _, fi) := p.m.exports.find? (fun (n, k, _) => n = exportName && k = 0)
      | throw (IO.userError "export not found")
    let fn := fi - nImp
    match checkModuleH cfg p fn with
    | none => IO.println "{\"eligible\":false}"
    | some MH =>
      let M := MH.mod
      let ck := M.cks.getD 0 default
      let gas : Gas := { Gas.init g0 with g := g0 }
      let some inb := hexBytes inputHex | throw (IO.userError "bad input hex")
      match instantiate cfg p gas with
      | .error e => throw (IO.userError s!"instantiate: {e}")
      | .ok s =>
        let inBytes : ByteArray := ⟨inb.toArray.map UInt8.ofNat⟩
        let emptyStack : Array Val := #[]
        let emptyFrames : List Frame := []
        let newCtx : CallCtx := { s.ctx with input := inBytes }
        let s : St := { s with gas := gas, stack := emptyStack, frames := emptyFrames, ctx := newCtx }
        match enter p s fi with
        | .cont s1 =>
          let g1 := s1.gas.g
          let (n, r, hevs) := runStepsH cfg p 100000000 s1 0 []
          let (status, stack, gf) := match r with
            | .fin s => ("fin", s.stack.toList, s.gas.g)
            | .abort s e => (s!"abort {e}", s.stack.toList, s.gas.g)
            | .unmodeled w => (s!"unmodeled {w}", [], 0)
            | .cont _ => ("cont", [], 0)
          let vals := stack.map valLimbs
          let recs := M.records.toList.map natList
          let de := dataEnd s1
          let img := (List.range de).map fun a => (readByte s1 a).toNat
          let gls := s1.globals.toList.map valLimbs
          IO.println s!"\{\"eligible\":true,\"fn\":{fn},\"ncode\":{M.records.size},\"nfns\":{M.fns.length},\"localTags\":{natList ck.localTags},\"arity\":{ck.arity},\"resTag\":{ck.resTag},\"maxFee\":{M.maxFee},\"regularOpCost\":{cfg.regularOpCost},\"g0\":{g1},\"steps\":{n},\"status\":{jStr status},\"gFinal\":{gf},\"stack\":{jList (vals.map fun (t, l) => s!"\{\"tag\":{t},\"limbs\":{natList l}}")},\"heights\":{natList ck.heights.toList},\"records\":{jList recs},\"mem\":{memBytes s1},\"dataEnd\":{de},\"data\":{natList img},\"stackRem\":{s1.stackRem},\"funcs\":{jList (M.funcs.map natList)},\"hosts\":{jList (hevs.map hostEvJson)},\"hostTab\":{jList (MH.hostRows.map natList)},\"ngl\":{gls.length},\"globals\":{jList (gls.map fun (t, l) => s!"\{\"tag\":{t},\"limbs\":{natList l}}")}}"
        | _ => throw (IO.userError "enter failed")
  | .prepErr v w => IO.println s!"\{\"eligible\":false,\"prepare\":{jStr v},\"why\":{jStr w}}"
  | .compileErr _ _ => IO.println "{\"eligible\":false,\"prepare\":\"compile\"}"
  | .outOfDomain w => IO.println s!"\{\"eligible\":false,\"prepare\":{jStr w}}"
  | .unmodeled w => IO.println s!"\{\"eligible\":false,\"prepare\":{jStr w}}"

/-- `points` file: one point per line, `t sf sl st cur... | nxt... | pub...` as decimals. -/
def evalPoints (nloc ncode : Nat) (path : String) (which : Nat := 0) : IO Unit := do
  let A := match which with
    | 1 => wasmBaseHostAir nloc ncode
    | 2 => wasmBaseRegAir nloc ncode
    | 3 => Chips.wasmBaseHashAir nloc ncode
    | _ => wasmBaseAir nloc ncode
  let lines ← IO.FS.lines path
  for ln in lines do
    if ln.isEmpty then continue
    let parts := (ln.splitOn "|").map fun s => (s.splitOn " ").filter (· ≠ "") |>.map String.toNat!
    match parts with
    | [hd, cur, nxt, pub] =>
      let t := hd.getD 0 0
      let fe (n : Nat) : F := (n : F)
      let sf := fe (hd.getD 1 0); let sl := fe (hd.getD 2 0); let st := fe (hd.getD 3 0)
      let cf := fun i => fe (cur.getD i 0)
      let nf := fun i => fe (nxt.getD i 0)
      let pf := fun i => fe (pub.getD i 0)
      let T := A.tables.getD t default
      let ev := fun (e : WasmBase.Expr) => (e.evalG cf nf pf sf sl st).toNat
      let cs := T.constraints.map ev
      let is := T.inters.map fun i => natList ((ev i.count) :: i.msg.map ev)
      IO.println s!"\{\"t\":{t},\"constraints\":{natList cs},\"inters\":{jList is}}"
    | _ => throw (IO.userError "bad point line")

def main (args : List String) : IO Unit := do
  match args with
  | ["air", l, n] => IO.println (airJson (wasmBaseAir l.toNat! n.toNat!))
  | ["airH", l, n] => IO.println (airJson (wasmBaseHostAir l.toNat! n.toNat!))
  | ["airR", l, n] => IO.println (airJson (wasmBaseRegAir l.toNat! n.toNat!))
  | ["airX", l, n] => IO.println (airJson (Chips.wasmBaseHashAir l.toNat! n.toNat!))
  | ["prep", path, exportName, g0] => prep path exportName g0.toNat!
  | ["prep", path, exportName, g0, inp] => prep path exportName g0.toNat! inp
  | ["eval", l, n, path] => evalPoints l.toNat! n.toNat! path
  | ["evalH", l, n, path] => evalPoints l.toNat! n.toNat! path 1
  | ["evalR", l, n, path] => evalPoints l.toNat! n.toNat! path 2
  | ["evalX", l, n, path] => evalPoints l.toNat! n.toNat! path 3
  | _ => IO.eprintln "usage: wasmbase-tool air|airH|airR|airX <nloc> <ngl> | prep <wasm> <exportName> <g0> [inputHex] | eval|evalH|evalR|evalX <nloc> <ngl> <points>"
