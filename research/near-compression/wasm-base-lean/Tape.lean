import Lean
import NearSpecV3.Successor.Config
import NearSpecV3.Successor.SchemaVersion
import NearSpecV3.Successor.TierO4NS
import WasmBase.ToolCore
/-!
# `wasmbase-tape` — the chunk's own host tape (E2E milestone M3)

`docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` M3: the Wasm trace generator must take its host answers
(status, result word, `g_after`, register fills) from **the chunk's own checker run**, not from the
default context `wasmbase-tool prepIf` uses.  Milestone 1 showed why: `d3tiny`'s `storage_write`
costs 5 × `read_cached_trie_node` less in the chunk than in an empty context (trie nodes cached by
earlier receipts), and T1's existing key takes the evicted-value path.

```
wasmbase-tape OUT.jsonl CASE_DIR...
```

runs the **unmodified** Lean checker `Schema.checkVersioned (Tier.cfg .allFeatures)` on each case,
exactly as `nearspec-v3-check-successor --tier allFeatures` does, and writes one JSON line per Wasm
call the checker makes, in order: the call's code hash, method, input and prepaid gas, the checker's
own result (burnt/used gas, return value, logs, abort error), and a `prep` object in the format of
`wasmbase-tool prepIf` whose `hosts` are the host answers of **this** run.

## How the calls are observed without changing the checker

The executable is linked with `-Wl,--wrap=lp_NearSpecV3_NearSpecV3_Wasm_runCallWithLimitsFast`
(`lakefile.toml`).  That is the compiled entry every checker call path reaches (`vmCall` →
`runCallWithLimits`, which `@[csimp]` replaces by `runCallWithLimitsFast`; it is defined in
`Wasm/Arcs.c` and called from other object files, so the linker redirects those calls).
The C shim `tape_shim.c` (`__wrap_…`) calls the real function (the linker's `__real_…`), **returns
its result unchanged**, and passes the arguments and the result to `hookE`, which replays the same
call from the same
initial state with `runStepsH` (the spec's own `step`, recording each host call's answer).  So:

* the checker's verdict and every value it computes are the unwrapped ones (`verdict` is printed and
  compared with `nearspec-v3-check-successor`);
* the tape is the spec's `step` run on the checker's own `CallCtx` and trie-backed `RealStore`
  (accounting cache, recorder, overlay), i.e. the call as the checker executed it;
* the replay's final state is compared with the real result (`replayMatches`): burnt and used gas,
  return value and logs must agree, or the line says so.  `preSync` is the replay's final gas before
  `ReturningFromWasm`: `sync` burns `remaining − g`, so `burnt = preSync.burnt + preSync.remaining −
  g_final`, which is how the trace's own final budget is turned into burnt gas.

The shim matches the original ABI: `code` and `method` are borrowed (as the boxed wrapper of
`runCallWithLimitsFast` shows), every other argument is owned; it takes one extra reference to each
argument for the hook (a Lean `@[export]` cannot have borrowed parameters).  `build-tape.sh`
compiles the shim before `lake build wasmbase-tape`.
-/
open NearSpec NearSpecV3 NearSpecV3.Successor NearSpecV3.Wasm WasmBase ZkFormal.Algebra

instance : Inhabited Run := ⟨.line ""⟩

def hexB (b : ByteArray) : String := hex b

/-- The prep JSON of `wasmbase-tool prepIf` for a call that starts at `s0` (the instantiated state
with the checker's context, store and budget), or an `eligible:false` object. -/
def tapePrep (cfg : NearCfg) (p : Prepared) (fi : Nat) (s0 : St) (fuel : Nat)
    (chk : NearCfg → Prepared → Nat → Option ModOutH := checkModuleM2) : String × Option St :=
  let nImp := p.m.imports.size
  let fn := fi - nImp
  match chk cfg p fn with
  | none => ("{\"eligible\":false}", none)
  | some MH =>
    let M := MH.mod
    let ck := M.cks.getD 0 default
    let nif := ((List.range M.records.size).filter fun j =>
      ((M.records[j]?.getD [])).getD 1 0 = Chips.IfC.opIf).length
    -- `callEntry`: `CallingWasm` (`g := remaining`), empty stack and frames, then `enter`
    let s := { s0 with gas := { s0.gas with g := s0.gas.remaining }, stack := #[], frames := [] }
    match enter p s fi with
    | .cont s1 =>
      let g1 := s1.gas.g
      let (n, r, hevs) := runStepsH cfg p fuel s1 0 []
      let (status, stack, gf, fs) := match r with
        | .fin s => ("fin", s.stack.toList, s.gas.g, some s)
        | .abort s e => (s!"abort {e}", s.stack.toList, s.gas.g, some s)
        | .unmodeled w => (s!"unmodeled {w}", [], 0, none)
        | .cont _ => ("cont", [], 0, none)
      let vals := stack.map valLimbs
      let recs := M.records.toList.map natList
      let de := dataEnd s1
      let img := (List.range de).map fun a => (readByte s1 a).toNat
      let gls := s1.globals.toList.map valLimbs
      (s!"\{\"eligible\":true,\"fn\":{fn},\"ncode\":{M.records.size},\"nfns\":{M.fns.length},\"nif\":{nif},\"localTags\":{natList ck.localTags},\"arity\":{ck.arity},\"resTag\":{ck.resTag},\"maxFee\":{M.maxFee},\"regularOpCost\":{cfg.regularOpCost},\"g0\":{g1},\"steps\":{n},\"status\":{jStr status},\"gFinal\":{gf},\"stack\":{jList (vals.map fun (t, l) => s!"\{\"tag\":{t},\"limbs\":{natList l}}")},\"heights\":{natList ck.heights.toList},\"records\":{jList recs},\"mem\":{memBytes s1},\"dataEnd\":{de},\"data\":{natList img},\"stackRem\":{s1.stackRem},\"funcs\":{jList (M.funcs.map natList)},\"hosts\":{jList (hevs.map hostEvJson)},\"hostTab\":{jList (MH.hostRows.map natList)},\"ngl\":{gls.length},\"globals\":{jList (gls.map fun (t, l) => s!"\{\"tag\":{t},\"limbs\":{natList l}}")}}",
        fs)
    | _ => ("{\"eligible\":false,\"why\":\"enter\"}", none)

/-- `runCall`'s set-up up to `callEntry` (`Wasm/Exec.lean`), on the same arguments, then `tapePrep`.
`none` when the call never reaches the method (preparation, loading, link or resolve outcome, or a
`start` function, which no corpus contract has). -/
def tapeOf (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool) (real : Option TTN.RealStore)
    (chk : NearCfg → Prepared → Nat → Option ModOutH := checkModuleM2) : Option (String × Option St) :=
  if method.isEmpty then none else
  match prepare cfg code blockLevel with
  | .ok p =>
    if cfg.loadingLimits && !instanceAllocationFits p.m then none else
    let gs : Gas := Gas.init ctx.prepaidGas
    let loaded := match payPer gs C.contractLoadingBytes code.size with
      | (gs, none) => payBase gs C.contractLoadingBase
      | r => r
    match loaded with
    | (gs, none) =>
      match link p with
      | .ok =>
        match resolve p method with
        | .ok mi =>
          match instantiate cfg p gs with
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                              storageUsage := ctx.storageUsage, real := real,
                              curveHosts := cfg.curveHosts }
            if p.m.start.isSome then none else some (tapePrep cfg p mi s fuel chk)
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

def logsJson (ls : Array ByteArray) : String := jList (ls.toList.map fun l => jStr (hexB l))

def retJson (r : Option (ByteArray ⊕ Nat)) : String :=
  match r with
  | some (.inl d) => jStr (hexB d)
  | some (.inr k) => jStr s!"receipt{k}"
  | none => "null"

/-- The checker's own result of the call. -/
def realJson : Run → String
  | .line l => s!"\{\"line\":{jStr l}}"
  | .done s e =>
    s!"\{\"burnt\":{s.gas.burnt},\"used\":{s.gas.used},\"ret\":{retJson s.ret},\"logs\":{logsJson s.logs},\"err\":{match e with | some e => jStr e | none => "null"}}"

def replayMatches (r : Run) (fs : Option St) : String :=
  match r, fs with
  | .done s _, some t =>
    if s.gas.burnt == t.gas.burnt && s.gas.used == t.gas.used && retJson s.ret == retJson t.ret &&
        logsJson s.logs == logsJson t.logs then "true" else "false"
  | _, _ => "null"

initialize tapeOut : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none
initialize tapeSeq : IO.Ref Nat ← IO.mkRef 0
/-- `WASMBASE_TAPE_CHECKER=M3`: preps for `wasmBaseM3Air` (`checkModuleM3`). -/
initialize tapeM3 : IO.Ref Bool ← IO.mkRef false

def hook (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool) (real : Option TTN.RealStore) (r : Run) : BaseIO Unit := do
  let some h ← tapeOut.get | return
  let k ← tapeSeq.modifyGet fun k => (k, k + 1)
  let chk := if (← tapeM3.get) then checkModuleM3 else checkModuleM2
  let (prep, pre) := match tapeOf cfg code method ctx fuel blockLevel real chk with
    | some (j, fs) => (j, fs)
    | none => ("null", none)
  -- the replay's final state before `ReturningFromWasm` (`sync`), and after it
  let fs := pre.bind fun s => (sync s).toOption
  let preJson := match pre with
    | some s => s!"\{\"burnt\":{s.gas.burnt},\"remaining\":{s.gas.remaining},\"g\":{s.gas.g}}"
    | none => "null"
  let line := s!"\{\"seq\":{k},\"code_sha256\":{jStr (hexB (Crypto.sha256 code))},\"code_len\":{code.size},\"method\":{jStr method},\"prepaid\":{ctx.prepaidGas},\"input\":{jStr (hexB ctx.input)},\"account\":{jStr ctx.currentAccount},\"real\":{realJson r},\"replayMatches\":{replayMatches r fs},\"preSync\":{preJson},\"prep\":{prep}}"
  let _ ← (h.putStrLn line).toBaseIO
  let _ ← h.flush.toBaseIO

/-- The hook the C shim (`tape_shim.c`) calls after the real `runCallWithLimitsFast` returned `r`:
records the call's tape.  Exported, so every argument is owned (the shim takes the references). -/
@[export wb_tape_hook]
def hookE (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool) (real : Option TTN.RealStore) (r : Run) : BaseIO Unit :=
  hook cfg code method ctx fuel blockLevel real r

def main (args : List String) : IO UInt32 := do
  let out :: dirs := args
    | IO.eprintln "usage: wasmbase-tape OUT.jsonl CASE_DIR..."; return 2
  -- append: a driver may split one shard over several invocations
  let h ← IO.FS.Handle.mk out .append
  tapeOut.set (some h)
  tapeM3.set ((← IO.getEnv "WASMBASE_TAPE_CHECKER") == some "M3")
  let cfg := Tier.cfg .allFeatures
  let mut failed := false
  for dir in dirs do
    try
      let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
      let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
      h.putStrLn s!"\{\"case\":{jStr dir}}"
      let (verdict, reason) := match checkVerdict (Schema.checkVersioned cfg) cb.toList wb.toList with
        | .accept => ("accept", "")
        | .reject e => ("reject", e)
        | .outOfDomain e => ("out_of_domain", e)
      h.putStrLn s!"\{\"case\":{jStr dir},\"verdict\":{jStr verdict},\"reason\":{jStr reason}}"
      h.flush
    catch e =>
      failed := true
      h.putStrLn s!"\{\"case\":{jStr dir},\"verdict\":\"io_error\",\"reason\":{jStr e.toString}}"
  return if failed then 2 else 0
