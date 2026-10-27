import Lean
import NearSpecV3.Wasm.Exec
import NearSpecV3.Wasm.Fuel

/-!
# Arc prototype: bulk-skip zero-fee control runs, fused with the trailing `br`

For each function, precompute maximal runs of pcs whose gas-table entry is `none` and whose
instruction is `block`/`loop`/`end` (zero-fee `nop` too). Single-stepping through such a run has
exactly the net effect: `pc := next`, drop `pops` entry labels, push `pushes` labels with
`height := s.stack.size` (constant inside the run — no run instruction touches the value stack).

When the instruction after the run is a `br l` (charged or zero-fee), the arc is **fused** with
it: the pushed labels that the `br` discards are never materialized, so a loop-back branch
(`blocks4999`) costs O(1) per iteration instead of O(run length).

Guards (checked at runtime against the entry label depth):
* every `end` in the run pops a run label (never `doReturn`, never an entry pop that would
  underflow): `grd ≥ enP + 2 - |sim|` at each end;
* the fused `br l` is not a `doReturn`: `|E| ≥ pops + l + 2 - |pushes|`.

An arc consumes exactly as much fuel as the single steps it replaces. `runArc` therefore
reports `fuel exhausted` exactly when `run` does.
-/

open NearSpecV3.Wasm

namespace ArcProto

/-- A precomputed shortcut: free run `[pc0, runEnd)`, optionally fused with `br brL` at `runEnd`. -/
structure Arc where
  runEnd : Nat                          -- first pc after the free run
  pops : Nat                            -- entry labels removed (List.drop)
  pushes : List (Nat × Nat × Bool)      -- labels pushed (target, arity, isLoop); height = entry stack size
  guard : Nat                           -- required entry label depth
  brL : Option Nat                      -- fused `br l` at runEnd (if the instr there is a br)
  brCharged : Bool                      -- the fused br's pc carries a charge point
  deriving Repr

/-- Builder state. -/
structure AB where
  out : Array (Option Arc)
  cur : Option Nat                    -- run start pc
  sim : List (Nat × Nat × Bool)        -- in-run labels, top-first
  enP : Nat                            -- entry labels popped so far
  grd : Nat                            -- guard so far

def runKind (i : Instr) : Bool :=
  match i with
  | .block _ | .loop _ | .end_ | .nop => true
  | _ => false

def abClose (st : AB) (nxt : Nat) : AB :=
  match st.cur with
  | none => st
  | some s =>
    let out := if nxt - s ≥ 2 then st.out.set! s (some ⟨nxt, st.enP, st.sim, st.grd, none, false⟩) else st.out
    { st with out := out, cur := none, sim := [], enP := 0, grd := 0 }

/-- Close the run at the br pc `bpc`, fusing the br. -/
def abCloseBr (pf : PFunc) (st : AB) (bpc : Nat) (l : Nat) : AB :=
  match st.cur with
  | none => st
  | some s =>
    let np := st.sim.length
    let grdBr := st.enP + l + 2 - np
    let grd := Nat.max st.grd grdBr
    let charged := !(pf.gas[bpc]? == some none)
    let out := if bpc - s ≥ 1 then st.out.set! s (some ⟨bpc, st.enP, st.sim, grd, some l, charged⟩) else st.out
    { st with out := out, cur := none, sim := [], enP := 0, grd := 0 }

def abStep (pf : PFunc) (st : AB) (pc : Nat) : AB :=
  match pf.code[pc]? with
  | none => st
  | some i =>
    if !(pf.gas[pc]? == some none) || !runKind i then
      -- run ends here; if the instr is a br (charged or not) fuse it
      match i with
      | .br l => abCloseBr pf st pc l
      | _ => abClose st pc
    else
      let st := match st.cur with
        | none => { st with cur := some pc }
        | some _ => st
      match i with
      | .block bt =>
        { st with sim := ((pf.endOf[pc]?.getD 0) + 1, (btResults bt).size, false) :: st.sim }
      | .loop _ => { st with sim := (pc + 1, 0, true) :: st.sim }
      | .nop => st
      | .end_ =>
        let st := { st with grd := Nat.max st.grd (st.enP + 2 - st.sim.length) }
        match st.sim with
        | [] => { st with enP := st.enP + 1 }
        | _ :: t => { st with sim := t }
      | _ => st

def buildArcs (pf : PFunc) : Array (Option Arc) :=
  let st0 : AB := { out := Array.replicate pf.code.size none, cur := none, sim := [], enP := 0, grd := 0 }
  let st := (List.range pf.code.size).foldl (fun st pc => abStep pf st pc) st0
  (abClose st pf.code.size).out

/-! ## Fast stepping -/

def listLenGe : Nat → List Label → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, _ :: t => listLenGe n t

def listDrop {α : Type} : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, _ :: t => listDrop n t

def listIdx (l : Nat) (ls : List Label) : Label :=
  match ls with
  | [] => default
  | x :: t => if l = 0 then x else listIdx (l - 1) t

/-- Materialize the run's pushed labels (height = entry value-stack size). -/
def matPushes (H : Nat) : List (Nat × Nat × Bool) → List Label
  | [] => []
  | (t, ar, lp) :: rest =>
    ({ target := t, arity := ar, height := H, isLoop := lp } : Label) :: matPushes H rest

/-- The state exactly as it would be after single-stepping the free run (for the charge-fail path). -/
def afterRun (s : St) (f : Frame) (a : Arc) : St :=
  setFrame s { f with pc := a.runEnd, labels := matPushes s.stack.size a.pushes ++ listDrop a.pops f.labels }

/-- nth of a list of triples (top-first). -/
def listIdxT : List (Nat × Nat × Bool) → Nat → Nat × Nat × Bool
  | [], _ => (0, 0, false)
  | x :: _, 0 => x
  | _ :: t, n + 1 => listIdxT t n

/-- The fused `br l` on the post-run label layout `pushes ++ entry.drop pops`. -/
def fuseBr (s : St) (f : Frame) (a : Arc) : Frame × Array Val :=
  let np := a.pushes.length
  let l := a.brL.getD 0
  if l < np then
    -- target label is one of the run's pushes (top-first at list head)
    let (t, ar, lp) := listIdxT a.pushes l
    let lab : Label := { target := t, arity := ar, height := s.stack.size, isLoop := lp }
    let keep := if lp then l else l + 1
    let labs := matPushes s.stack.size (listDrop keep a.pushes) ++ listDrop a.pops f.labels
    let vals := s.stack.extract (s.stack.size - ar) s.stack.size
    let stk := s.stack.extract 0 lab.height ++ vals
    ({ fn := f.fn, pc := t, locals := f.locals, labels := labs, base := f.base }, stk)
  else
    -- target label is an entry label: E' = entry.drop pops, index idx = l - np
    let idx := l - np
    let lab := listIdx (a.pops + idx) f.labels
    let keepE := if lab.isLoop then idx else idx + 1
    let labs := listDrop (a.pops + keepE) f.labels
    let vals := s.stack.extract (s.stack.size - lab.arity) s.stack.size
    let stk := s.stack.extract 0 lab.height ++ vals
    let fr : Frame := { fn := f.fn, pc := lab.target, locals := f.locals, labels := labs, base := f.base }
    (fr, stk)

/-- One fast step. Returns (fuel consumed − 1, result). -/
def stepArc (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) (s : St) : Nat × Res :=
  match s.frames with
  | [] => (0, .fin s)
  | f :: _ =>
    match p.funcs[f.fn]? with
    | none => (0, .unmodeled "bad frame")
    | some pf =>
      match pf.code[f.pc]? with
      | none => (0, .unmodeled "pc out of range")
      | some i =>
        match pf.gas[f.pc]? with
        | none => (0, .unmodeled "invariant: gas table shorter than the code")
        | some none =>
          match arcs[f.fn]? with
          | none => (0, exec cfg p s f pf i)
          | some t =>
            match t[f.pc]? with
            | none => (0, exec cfg p s f pf i)
            | some none => (0, exec cfg p s f pf i)
            | some (some a) =>
              if listLenGe a.guard f.labels then
                if a.brL.isSome then
                  -- fused arc + br
                  let k := a.runEnd - f.pc     -- free steps replaced
                  if a.brCharged then
                    match pf.gas[a.runEnd]? with
                    | some (some (gk, fee)) =>
                      match charge s fee (if gk = .linear then topCount s else 0) with
                      | .cont s' =>
                        let (fr, stk) := fuseBr s' f a
                        (k, .cont { s' with stack := stk, frames := match s.frames with | _ :: fs => fr :: fs | [] => [fr] })
                      | r =>
                        -- exact parity: the real abort state has the run's labels pushed
                        let sFail := afterRun s f a
                        match charge sFail fee (if gk = .linear then topCount sFail else 0) with
                        | r' => (k, r')
                    | _ => (k, .cont (afterRun s f a))   -- gas entry missing; fall back
                  else
                    let (fr, stk) := fuseBr s f a
                    (k, .cont { s with stack := stk, frames := match s.frames with | _ :: fs => fr :: fs | [] => [fr] })
                else
                  (a.runEnd - f.pc - 1, .cont (afterRun s f a))
              else (0, exec cfg p s f pf i)
        | some (some (gk, fee)) =>
          match charge s fee (if gk = .linear then topCount s else 0) with
          | .cont s => (0, exec cfg p s f pf i)
          | r => (0, r)

def runArc (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) : Nat → St → Res
  | 0, _ => .unmodeled "fuel exhausted"
  | n + 1, s =>
    match stepArc cfg p arcs s with
    | (k, .cont s') =>
      -- consumed k + 1 fuel; k + 1 ≥ 1 always
      if k ≤ n then runArc cfg p arcs (n - k) s'
      else .unmodeled "fuel exhausted"
    | (_, r) => r
decreasing_by
  simp_wf
  omega

/-! ## `runCall` with arcs (verbatim copy of `Exec.runCall`, `run` → `runArc`) -/

def callEntryArc (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc)))
    (fuel : Nat) (s : St) (fi : Nat) : Except String (St × Option String) :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  let r := match enter p s fi with
    | .cont s => runArc cfg p arcs fuel s
    | r => r
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

def runCallArc (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) (real : Option TTN.RealStore := none) :
    NearSpecV3.Wasm.Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : NearSpecV3.Wasm.Run :=
    .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
  if method.isEmpty then nop "MethodResolveError(MethodEmptyName)" else
  match prepare cfg code blockLevel with
  | .outOfDomain why => .line s!"out-of-domain {why}"
  | .unmodeled why => .line s!"unmodeled {why}"
  | .prepErr v _ => nop s!"CompilationError(PrepareError({v}))"
  | .compileErr k _ =>
    nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })"
  | .ok p =>
    if !cfg.curveHosts && real.isNone && p.m.imports.any (fun i => curveHosts.contains i.name) then
      .line "out-of-domain curve host function" else
    let gs : Gas := Gas.init ctx.prepaidGas
    let loaded := match payPer gs C.contractLoadingBytes code.size with
      | (gs, none) => payBase gs C.contractLoadingBase
      | r => r
    match loaded with
    | (gs, some _) => .line (s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ ext (emptySt gs))
    | (gs, none) =>
      match link p with
      | .linkError msg => .line (s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ ext (emptySt gs))
      | .invariant why => .line s!"unmodeled invariant: {why}"
      | .ok =>
        match resolve p method with
        | .notFound => nop "MethodResolveError(MethodNotFound)"
        | .invalidSignature => nop "MethodResolveError(MethodInvalidSignature)"
        | .invariant why => .line s!"unmodeled invariant: {why}"
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => .line (s!"abort {gs.burnt} {gs.used} {e}" ++ ext (emptySt gs))
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                              storageUsage := ctx.storageUsage, real := real,
                              curveHosts := cfg.curveHosts }
            let arcs := p.funcs.map buildArcs
            let afterStart : Except String (St × Option String) :=
              match p.m.start with
              | some st => callEntryArc cfg p arcs fuel s st
              | none => .ok (s, none)
            match afterStart with
            | .error why => .line s!"unmodeled {why}"
            | .ok (s, some e) => .done s (some e)
            | .ok (s, none) =>
              match callEntryArc cfg p arcs fuel s mi with
              | .error why => .line s!"unmodeled {why}"
              | .ok (s, e) => .done s e

def outcomeArc (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) : String :=
  let ext (s : St) : String := if full then fullExtra s else ""
  match runCallArc cfg code method ctx fuel blockLevel full with
  | .line l => l
  | .done s (some e) => s!"abort {s.gas.burnt} {s.gas.used} {e}" ++ ext s
  | .done s none =>
    let ret := match s.ret with
      | some (.inl d) => hex d
      | some (.inr r) => s!"receipt{r}"
      | none => "-"
    s!"ok {s.gas.burnt} {s.gas.used} {ret} {s.balance}" ++ ext s

/-! ## Experiment + Driver -/
/-- Experiment: single-step vs arc on the same prepared module, honest wall-clock. -/
def runNoArcs (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) : Except String (St × Option String) :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  let r := match NearSpecV3.Wasm.enter p s fi with
    | .cont s => NearSpecV3.Wasm.run pv86 p fuel s
    | r => r
  match r with
  | .fin s => (NearSpecV3.Wasm.sync s).map (·, none)
  | .abort s e => (NearSpecV3.Wasm.sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

def expMain (file : String) (gas fuel : Nat) : IO UInt32 := do
  let code ← IO.FS.readBinFile file
  match prepare pv86 code true with
  | .ok p =>
    match link p with
    | .ok =>
      match resolve p "run" with
      | .ok mi =>
        match instantiate pv86 p (Gas.init gas) with
        | .ok s =>
          let arcs := p.funcs.map buildArcs
          let t0 ← IO.monoMsNow
          let r1 := runNoArcs p fuel s mi
          let d1 := match r1 with | .ok (s', e) => s!"ok burnt={s'.gas.burnt} {e}" | .error m => s!"err {m}"
          let t1 ← IO.monoMsNow
          IO.println s!"no-arcs ({t1 - t0} ms): {d1}"
          (← IO.getStdout).flush
          let t2 ← IO.monoMsNow
          let r2 := callEntryArc pv86 p arcs fuel s mi
          let d2 := match r2 with | .ok (s', e) => s!"ok burnt={s'.gas.burnt} {e}" | .error m => s!"err {m}"
          let t3 ← IO.monoMsNow
          IO.println s!"arcs    ({t3 - t2} ms): {d2}"
          pure 0
        | .error e => IO.println s!"instantiate: {e}"; pure 1
      | _ => IO.println "resolve failed"; pure 1
    | _ => IO.println "link failed"; pure 1
  | _ => IO.println "prepare failed"; pure 1

/-! ## Driver -/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--exp", file, g, f] => expMain file (g.toNat?.getD 0) (f.toNat?.getD 0)
  | ["--build-cost", file] => do
    let code ← IO.FS.readBinFile file
    let t0 ← IO.monoMsNow
    match prepare pv86 code true with
    | .ok p => do
      let arcs := p.funcs.map buildArcs
      let mut n := 0
      for fn in [0:arcs.size] do
        match arcs[fn]? with
        | some t => for e in t do if e.isSome then n := n + 1
        | none => pure ()
      let t1 ← IO.monoMsNow
      IO.println s!"prepare+buildArcs: {t1 - t0} ms (arcs={n})"
      pure 0
    | _ => IO.println "prepare failed"; pure 1
  | ["--ab", gasStr, file] => do
    let gas := (gasStr.toNat?.getD 0)
    let code ← IO.FS.readBinFile file
    let ctx : CallCtx := { prepaidGas := gas }
    let fuel := wasmFuel pv86 gas
    let old := NearSpecV3.Wasm.outcome pv86 code "run" ctx fuel
    let fast := outcomeArc pv86 code "run" ctx fuel
    if old == fast then IO.println s!"PARITY {file} {old}" else IO.println s!"MISMATCH {file} old={old} fast={fast}"
    pure (if old == fast then 0 else 1)
  | ["--fast-only", file, g] => do
    let gas := (g.toNat?.getD 0) * 1000000000000
    let code ← IO.FS.readBinFile file
    let ctx : CallCtx := { prepaidGas := gas }
    let fuel := wasmFuel pv86 gas
    let t0 ← IO.monoMsNow
    let r := outcomeArc pv86 code "run" ctx fuel
    IO.println s!"fast-only 300T-class: {r}"
    let t1 ← IO.monoMsNow
    IO.println s!"fast-only time: {t1 - t0} ms"
    pure 0
  | file :: gasStr :: rest => do
    let gas := (gasStr.toNat?.getD 0) * 1000000000000
    let code ← IO.FS.readBinFile file
    let ctx : CallCtx := { prepaidGas := gas }
    let fuel := match rest with
      | f :: _ => f.toNat?.getD (wasmFuel pv86 gas)
      | [] => wasmFuel pv86 gas
    IO.println s!"file={file} gas={gas} fuel={fuel}"
    match prepare pv86 code true with
    | .ok p => do
      let arcs := p.funcs.map buildArcs
      for fn in [0:arcs.size] do
        match arcs[fn]? with
        | some t => do
          let mut n := 0
          let mut fused := 0
          for pc in [0:t.size] do
            match t[pc]? with
            | some (some a) =>
              n := n + 1
              if a.brL.isSome then fused := fused + 1
              IO.println s!"  fn{fn} pc{pc}: run={a.runEnd} pops={a.pops} pushes={a.pushes.length} guard={a.guard} br={a.brL} ch={a.brCharged}"
            | _ => pure ()
          IO.println s!"  fn{fn}: arcs={n} fused={fused}"
        | none => pure ()
    | _ => IO.println "prepare failed"
    let t0 ← IO.monoMsNow
    let old := NearSpecV3.Wasm.outcome pv86 code "run" ctx fuel
    IO.println s!"old  : {old}"     -- forces the old path inside this IO step
    let t1 ← IO.monoMsNow
    let fast := outcomeArc pv86 code "run" ctx fuel
    IO.println s!"fast : {fast}"
    let t2 ← IO.monoMsNow
    let ok := old == fast
    IO.println s!"old={t1 - t0} ms fast={t2 - t1} ms parity: {ok}"
    pure (if ok then 0 else 1)
  | _ => do
    IO.eprintln "usage: arc-proto FILE GAS_TGAS [FUEL]"
    pure 2


end ArcProto

def main (args : List String) : IO UInt32 := ArcProto.main args
