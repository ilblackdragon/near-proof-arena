import ReexecV3D3.Logged.Runtime.Dr

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

def callHostL (s : St) (name : String) : SM NearSpec.Bytes Res :=
  if s.real.isSome && realOodHosts.contains name then
    pure (.unmodeled s!"out-of-domain host function {name} called") else
  match sync s with
  | .error e => pure (.unmodeled e)
  | .ok s =>
    match hostCallL name with
    | none => pure (.unmodeled s!"host function {name} not modelled in D3α")
    | some h => do
      let p ← (h.run).run s
      match p.1 with
      | .ok _ => pure (.cont { p.2 with gas := { p.2.gas with g := p.2.gas.remaining } })
      | .error e => pure (if e.startsWith "unmodeled" then .unmodeled e else .abort p.2 e)


/-- The machine loop up to the next storage host call: `done r` (finished with `r`, no storage call)
or `host n s1 name` (the next step calls the storage host `name` from `s1`, `n` fuel left). Pure and
tail-recursive, so long runs need no stack. -/
inductive RU where
  | done (r : Res)
  | host (n : Nat) (s1 : St) (name : String)

def runUntil (cfg : NearCfg) (p : Prepared) : Nat → St → RU
  | 0, _ => .done (.unmodeled "fuel exhausted")
  | n + 1, s =>
    match stepPre p s with
    | some (s1, name) => .host n s1 name
    | none =>
      match step cfg p s with
      | .cont s' => runUntil cfg p n s'
      | r => .done r

theorem runUntil_lt {cfg : NearCfg} {p : Prepared} :
    ∀ {n : Nat} {s : St} {n' : Nat} {s1 : St} {name : String},
      runUntil cfg p n s = .host n' s1 name → n' < n
  | 0, _, _, _, _, h => by simp [runUntil] at h
  | n + 1, s, n', s1, name, h => by
    unfold runUntil at h
    split at h
    · cases h; omega
    · split at h
      · have := runUntil_lt h; omega
      · cases h

/-- `Exec.run` with the storage host calls read through `SM` (`callHostL`). -/
def runL (cfg : NearCfg) (p : Prepared) (n : Nat) (s : St) : SM NearSpec.Bytes Res :=
  match h : runUntil cfg p n s with
  | .done r => pure r
  | .host n' s1 name => callHostL s1 name >>= fun r =>
    match r with
    | .cont s => runL cfg p n' s
    | r => pure r
termination_by n
decreasing_by exact runUntil_lt h


def entrySt (s : St) : St := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }


def enterRunL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) : SM NearSpec.Bytes Res :=
  match enter p s fi with
  | .cont s => runL cfg p fuel s
  | r => pure r

def entryResult (r : Res) : Except String (St × Option String) :=
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

def callEntryL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    SM NearSpec.Bytes (Except String (St × Option String)) :=
  enterRunL cfg p fuel (entrySt s) fi >>= fun r => pure (entryResult r)


def afterStartL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) :
    SM NearSpec.Bytes (Except String (St × Option String)) :=
  match p.m.start with
  | some st => callEntryL cfg p fuel s st
  | none => pure (.ok (s, none))

def mainL (cfg : NearCfg) (p : Prepared) (fuel : Nat) (mi : Nat) :
    Except String (St × Option String) → SM NearSpec.Bytes Run
  | .error why => pure (.line s!"unmodeled {why}")
  | .ok (s, some e) => pure (.done s (some e))
  | .ok (s, none) => callEntryL cfg p fuel s mi >>= fun b => match b with
    | .error why => pure (.line s!"unmodeled {why}")
    | .ok (s, e) => pure (.done s e)

/-- The contract-loading charge of `runCall`. -/
def loadedOf (gs : Gas) (code : ByteArray) : Gas × Option String :=
  match payPer gs C.contractLoadingBytes code.size with
  | (gs, none) => payBase gs C.contractLoadingBase
  | r => r

/-- `Exec.runCall … (real := some real)`, with the machine run through `SM` (`callEntryL`). -/
def runCallL (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool) (full : Bool) (real : TTN.RealStore) : SM NearSpec.Bytes Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : Run := .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
  if method.isEmpty then pure (nop "MethodResolveError(MethodEmptyName)") else
  match prepare cfg code blockLevel with
  | .outOfDomain why => pure (.line s!"out-of-domain {why}")
  | .unmodeled why => pure (.line s!"unmodeled {why}")
  | .prepErr v _ => pure (nop s!"CompilationError(PrepareError({v}))")
  | .compileErr k _ =>
    pure (nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })")
  | .ok p =>
    match loadedOf (Gas.init ctx.prepaidGas) code with
    | (gs, some _) => pure (.line (s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ ext (emptySt gs)))
    | (gs, none) =>
      match link p with
      | .linkError msg =>
        pure (.line (s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ ext (emptySt gs)))
      | .invariant why => pure (.line s!"unmodeled invariant: {why}")
      | .ok =>
        match resolve p method with
        | .notFound => pure (nop "MethodResolveError(MethodNotFound)")
        | .invalidSignature => pure (nop "MethodResolveError(MethodInvalidSignature)")
        | .invariant why => pure (.line s!"unmodeled invariant: {why}")
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => pure (.line (s!"abort {gs.burnt} {gs.used} {e}" ++ ext (emptySt gs)))
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                              storageUsage := ctx.storageUsage, real := some real }
            afterStartL cfg p fuel s >>= mainL cfg p fuel mi


end ReexecV3D3.Logged.W
