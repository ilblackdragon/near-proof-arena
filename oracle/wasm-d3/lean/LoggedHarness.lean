import NearSpecV3.Logged.WasmRun
import NearSpecV3.Wasm.ChunkStorage

/-! Untrusted differential driver adapters for the logged WASM execution path.
Mock storage preserves the original harness context; trie replay calls the same
`runCallL` used by the logged chunk checker. Neither adapter changes the trusted spec. -/
namespace NearSpecV3.Wasm.LoggedHarness

def mockRun (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) : Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : Run := .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
  if method.isEmpty then nop "MethodResolveError(MethodEmptyName)" else
  match prepare cfg code blockLevel with
  | .outOfDomain why => .line s!"out-of-domain {why}"
  | .unmodeled why => .line s!"unmodeled {why}"
  | .prepErr v _ => nop s!"CompilationError(PrepareError({v}))"
  | .compileErr k _ =>
    nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })"
  | .ok p =>
    -- the harness context: importing a curve host function is out of domain; under the
    -- trie-backed `External` (RuntimeD3) only *calling* one is (`callHost`: not modelled)
    if p.m.imports.any (fun i => curveHosts.contains i.name) then
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
                              storageUsage := ctx.storageUsage, real := none }
            match Logged.SM.run (fun _ => none)
                (Logged.W.afterStartL cfg p fuel s >>= Logged.W.mainL cfg p fuel mi) with
            | .ok r => r
            | .error e => .line s!"unmodeled logged store: {e}"

def mockOutcome (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) : String :=
  let ext (s : St) : String := if full then fullExtra s else ""
  match mockRun cfg code method ctx fuel blockLevel full with
  | .line l => l
  | .done s (some e) => s!"abort {s.gas.burnt} {s.gas.used} {e}" ++ ext s
  | .done s none =>
    let ret := match s.ret with
      | some (.inl d) => hex d
      | some (.inr r) => s!"receipt{r}"
      | none => "-"
    s!"ok {s.gas.burnt} {s.gas.used} {ret} {s.balance}" ++ ext s


open TTN

def replayChunk (cfg : NearCfg) (code : ByteArray) (store : TTN.Store) (root : ByteArray)
    (calls : List CallIn) (fuelOf : Nat → Nat) (ablate : String := "") (deltas : Bool := false) :
    List String := Id.run do
  let mut overlay : Std.HashMap ByteArray (Option ByteArray) := {}
  let mut acct : Acct := {}
  let mut recd : Recorder := {}
  let mut out := #[]
  for c in calls do
    -- receipt start: the runtime reads the receiver's account (`TrieKey::Account`, recorded, before
    -- `storage_proof_size_before_receipt` is taken); the overlay never holds it here (only
    -- contract data is tracked), and once recorded a node is not recorded again
    let accKey := ByteArray.mk #[0] ++ c.account.toUTF8
    recd := match lookup store root accKey with
      | .ok l =>
        let r := recd.recordNodes store l.nodes
        match l.value with
        | some (_, vh) => r.record vh ((store vh).map (·.size) |>.getD 0)
        | none => r
      | .error _ => recd
    let real : RealStore := { store, root, overlay, acct, pfx := contractDataPrefix c.account,
                              recd, recBefore := recd.size }
    let ctx : CallCtx := { currentAccount := c.account, input := c.input, prepaidGas := c.prepaid }
    let call := Logged.SM.run (fun h => (store ⟨h.toArray⟩).map (·.toList))
      (Logged.W.runCallL cfg code "run" ctx (fuelOf c.prepaid) true false (Logged.W.dr real))
    match call with
    | .error e => out := out.push s!"unmodeled logged store: {e}"
    | .ok (.line l) => out := out.push s!"line {l}"
    | .ok (.done s err) =>
      let d := match s.real with
        | some r => s!" d={r.recd.size - r.recBefore}"
        | none => ""
      out := out.push (profileLine s err ++ (if deltas then d else ""))
      match s.real with
      | some r =>
        recd := r.recd
        acct := if ablate == "cache" then {} else r.acct
        if err.isNone && ablate != "overlay" then overlay := r.overlay
      | none => out := out.push "unmodeled: real store lost"
  out.toList

end NearSpecV3.Wasm.LoggedHarness
