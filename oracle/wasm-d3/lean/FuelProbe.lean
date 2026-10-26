import NearSpecV3.Wasm.Fuel
/-! `nearspec-v3-fuel-probe` (W02): measure the Wasm interpreter's step count against the fuel
budgets and check the potential-argument inequalities of `NearSpecV3/Wasm/Fuel.lean` on real runs.

    nearspec-v3-fuel-probe [--check-potential] [--legacy-check]   (stdin)

Each stdin line is `<label> <prepaid_gas> <wasm_file> [method]`. One JSON object is printed per line.

* `t`: `step` calls, the fuel a run needs. `tc` / `tf`: costly and free instructions executed.
* `charged`: Σ of the instrumentation points that passed. `F`: the largest per-function free count.
* `ineq_free`: `tf ≤ P₀ + F·tc` (O-W1 + O-W2 combined), `ineq_paid`: `tc · regular ≤ charged` (O-W4).
* `--check-potential` also recomputes `P` on every step and counts free steps that do not lower it
  (`p_viol`, O-W1) and the largest rise over one costly step (`p_rise`, ≤ `F` is O-W2). This costs
  O(depth) per step.
* `legacy_exhausted` / `wasm_exhausted`: `t > legacyFuel gas` / `t > wasmFuel gas`. By
  `Wasm.run_fuel_le` this is exactly whether the corresponding budget reports
  `unmodeled fuel exhausted`. `--legacy-check` re-runs the real `Wasm.outcome` under the legacy
  budget to confirm it.

The run mirrors `Wasm.runCall` (mock `External`, `floatPv86` with curve hosts and loading limits).
It is measurement code: the outcome a verdict depends on is `Wasm.runCall`'s. -/
open NearSpecV3.Wasm

structure Stats where
  t : Nat := 0
  tc : Nat := 0
  tf : Nat := 0
  charged : Nat := 0
  maxDepth : Nat := 0
  pViol : Nat := 0
  pRise : Nat := 0
  p0 : Nat := 0

def suffixFree (code : Array Instr) : Array Nat := Id.run do
  let mut out := Array.replicate (code.size + 1) 0
  let mut acc := 0
  for k in [0:code.size] do
    let i := code.size - 1 - k
    if isFreeInstr code[i]! then acc := acc + 1
    out := out.set! i acc
  out

def potential (suf : Array (Array Nat)) (s : St) : Nat :=
  s.frames.foldl (fun a f =>
    let row := suf[f.fn]?.getD #[]
    a + row[f.pc]?.getD 0) 0

/-- Classify the step about to run: `(free?, charged amount if the point passes)`. -/
def info (p : Prepared) (s : St) : Bool × Nat × Bool :=
  match s.frames with
  | [] => (false, 0, false)
  | f :: _ =>
    match p.funcs[f.fn]? with
    | none => (false, 0, false)
    | some pf =>
      let free := match pf.code[f.pc]? with
        | some i => isFreeInstr i
        | none => false
      match pf.gas[f.pc]? with
      | some (some (k, fee)) =>
        let amt := (if k = .linear then topCount s else 0) * fee.l + fee.c
        let ok := amt < u64Bound ∧ amt ≤ s.gas.g
        (free, if ok then amt else 0, ok)
      | _ => (free, 0, true)

def runC (cfg : NearCfg) (p : Prepared) (suf : Array (Array Nat)) (chk : Bool) :
    Nat → St → Stats → Res × Stats
  | 0, _, st => (.unmodeled "fuel exhausted", st)
  | n + 1, s, st =>
    let (free, amt, ok) := info p s
    let st := { st with t := st.t + 1, charged := st.charged + amt,
                        tc := st.tc + (if !free && ok then 1 else 0),
                        tf := st.tf + (if free then 1 else 0),
                        maxDepth := Nat.max st.maxDepth s.frames.length }
    match step cfg p s with
    | .cont s' =>
      let st := if chk then
          let a := potential suf s
          let b := potential suf s'
          if free then { st with pViol := st.pViol + (if b < a then 0 else 1) }
          else { st with pRise := Nat.max st.pRise (b - a) }
        else st
      runC cfg p suf chk n s' st
    | r => (r, st)

def entryC (cfg : NearCfg) (p : Prepared) (suf : Array (Array Nat)) (chk : Bool) (fuel : Nat)
    (s : St) (fi : Nat) (st : Stats) : Except String (St × Option String) × Stats :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  match enter p s fi with
  | .cont s =>
    let st := { st with p0 := Nat.max st.p0 (potential suf s) }
    let (r, st) := runC cfg p suf chk fuel s st
    let r := match r with
      | .fin s => (sync s).map (·, none)
      | .abort s e => (sync s).map (·, some e)
      | .unmodeled why => .error why
      | .cont _ => .error "cont"
    (r, st)
  | .fin s => ((sync s).map (·, none), st)
  | .abort s e => ((sync s).map (·, some e), st)
  | .unmodeled why => (.error why, st)

def jstr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

def probe (cfg : NearCfg) (label : String) (gas : Nat) (code : ByteArray) (method : String)
    (chk legacy : Bool) : IO String := do
  let t0 ← IO.monoMsNow
  let ctx : CallCtx := { prepaidGas := gas }
  let big := 1000000000000000000
  let res : String × Stats × Nat ← match prepare cfg code true with
    | .ok p =>
      let suf := p.funcs.map (fun pf => suffixFree pf.code)
      let F := p.funcs.foldl (fun a pf => Nat.max a (freeCount pf.code)) 0
      match link p, resolve p method with
      | .ok, .ok mi =>
        let gs : Gas := Gas.init ctx.prepaidGas
        let loaded := match payPer gs C.contractLoadingBytes code.size with
          | (gs, none) => payBase gs C.contractLoadingBase
          | r => r
        match loaded with
        | (gs, some e) => pure (s!"abort {gs.burnt} {e}", {}, F)
        | (gs, none) =>
          match instantiate cfg p gs with
          | .error e => pure (s!"abort {gs.burnt} {e}", {}, F)
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance, curveHosts := cfg.curveHosts }
            let (r1, st) := match p.m.start with
              | some sf => entryC cfg p suf chk big s sf {}
              | none => (.ok (s, none), {})
            match r1 with
            | .error why => pure (s!"unmodeled {why}", st, F)
            | .ok (s, some e) => pure (s!"abort {s.gas.burnt} {e}", st, F)
            | .ok (s, none) =>
              let (r2, st) := entryC cfg p suf chk big s mi st
              match r2 with
              | .error why => pure (s!"unmodeled {why}", st, F)
              | .ok (s, some e) => pure (s!"abort {s.gas.burnt} {e}", st, F)
              | .ok (s, none) => pure (s!"ok {s.gas.burnt}", st, F)
      | _, _ => pure ("link-or-resolve-failure", {}, F)
    | .prepErr v _ => pure (s!"prepare-error {v}", {}, 0)
    | .compileErr k _ => pure (s!"compile-error {k}", {}, 0)
    | .outOfDomain w => pure (s!"out-of-domain {w}", {}, 0)
    | .unmodeled w => pure (s!"unmodeled {w}", {}, 0)
  let (out, st, F) := res
  let t1 ← IO.monoMsNow
  let lf := legacyFuel gas
  let wf := wasmFuel cfg gas
  let legacyLine ← if legacy then
      let l := outcome cfg code method ctx lf true false
      pure s!", \"legacy_outcome\": {jstr l}"
    else pure ""
  pure ("{" ++ s!"\"label\": {jstr label}, \"gas\": {gas}, \"outcome\": {jstr out}, \"t\": {st.t}, " ++
    s!"\"tc\": {st.tc}, \"tf\": {st.tf}, \"F\": {F}, \"p0\": {st.p0}, \"charged\": {st.charged}, " ++
    s!"\"max_depth\": {st.maxDepth}, \"p_viol\": {st.pViol}, \"p_rise\": {st.pRise}, " ++
    s!"\"ineq_free\": {decide (st.tf ≤ st.p0 + F * st.tc)}, " ++
    s!"\"ineq_paid\": {decide (st.tc * cfg.regularOpCost ≤ st.charged)}, " ++
    s!"\"legacy_fuel\": {lf}, \"wasm_fuel\": {wf}, \"legacy_exhausted\": {decide (st.t > lf)}, " ++
    s!"\"wasm_exhausted\": {decide (st.t > wf)}, \"ms\": {t1 - t0}" ++ legacyLine ++ "}")

def main (args : List String) : IO UInt32 := do
  let chk := args.contains "--check-potential"
  let legacy := args.contains "--legacy-check"
  let cfg : NearCfg := { floatPv86 with loadingLimits := true, curveHosts := true }
  let stdin ← IO.getStdin
  let mut rc : UInt32 := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let toks := (line.trimRight.splitOn " ").filter (· ≠ "")
    match toks with
    | label :: g :: path :: rest =>
      let some gas := g.toNat? | IO.eprintln s!"bad gas {g}"; rc := 2; continue
      let code ← IO.FS.readBinFile path
      let out ← probe cfg label gas code (rest.headD "main") chk legacy
      IO.println out
      (← IO.getStdout).flush
    | _ => if !toks.isEmpty then IO.eprintln s!"bad line {line}"; rc := 2
  return rc
