/-
ArenaAudit: judge-owned inspection of a (candidate) Lean environment.

Runs as a fresh process that never loads candidate plugins and never enables
initializer execution: `importModules` only maps the `.olean` data. It is run
inside the sandbox because mapping a hostile `.olean` is itself an attack
surface; its JSON output is therefore *one* of several independent signals
(the Rust side re-derives the decisive facts from the lean4export NDJSON that
an independent kernel has checked).

Modes:
  arena-audit check <config.json>         -- audit; JSON report on stdout
  arena-audit list-trusted <config.json>  -- names of constants in trusted modules

Config (JSON):
  { "imports": [module...],              -- modules to import together
    "expectedDecl": "ArenaExpected.expectedType",
    "certificate": "Candidate.certificate",
    "candidateModules": [module...],
    "trustedModules": [module...],       -- judge-pinned modules (formal-core, spec, Expected)
    "toolchainPrefixes": ["Init", "Std", "Lean", "Lake"] }
-/
import Lean
open Lean

namespace ArenaAudit

structure Config where
  imports : Array String
  expectedDecl : String
  certificate : String
  candidateModules : Array String
  trustedModules : Array String
  toolchainPrefixes : Array String
  /-- native-lean route: candidate verifier model spliced into the statement
  (`""` = none). The expected decl is then `fun model => …`. -/
  modelDecl : String
  /-- Judge-generated `def inst : Prop := expectedDecl modelDecl` (`""` = none). -/
  instDecl : String
  deriving FromJson, Inhabited

/-- Plain dotted name parser (no «» escapes; arena names are plain identifiers). -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => if c.isEmpty then n else
    match c.toNat? with
    | some k => if c.all Char.isDigit then Name.mkNum n k else Name.mkStr n c
    | none => Name.mkStr n c) Name.anonymous

def nameStr (n : Name) : String := n.toString (escape := false)

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Direct constant dependencies (types, values, constructors, recursor rules). -/
def deps (ci : ConstantInfo) : Array Name :=
  let base := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => base ++ v.value.getUsedConstants
  | .thmInfo v => base ++ v.value.getUsedConstants
  | .opaqueInfo v => base ++ v.value.getUsedConstants
  | .inductInfo v => base ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => base.push v.induct
  | .recInfo v => base ++ v.all.toArray ++ (v.rules.toArray.flatMap fun r => r.rhs.getUsedConstants)
  | _ => base

/-- Transitive closure from `roots`; returns (present constants in DFS order, missing names). -/
def closure (env : Environment) (roots : Array Name) : Array Name × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
      order := order.push n
      for d in deps ci do
        if !seen.contains d then stack := stack.push d
  return (order, missing)

def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[(idx : Nat)]?
  | none => none

/-- Remove every `mdata` node (metadata never affects kernel meaning). -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

def truncate (s : String) (n : Nat := 4000) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ "…"

def isToolchainModule (cfg : Config) (m : Name) : Bool :=
  cfg.toolchainPrefixes.any fun p => (parseName p).isPrefixOf m

def readConfig (path : String) : IO Config := do
  let s ← IO.FS.readFile path
  match Json.parse s >>= fromJson? with
  | .ok c => pure c
  | .error e => throw <| IO.userError s!"bad config: {e}"

def setupSearchPath : IO Unit := do
  let sysroot ← match (← IO.getEnv "ARENA_LEAN_SYSROOT") with
    | some p => pure (System.FilePath.mk p)
    | none => findSysroot
  initSearchPath sysroot

def importEnv (mods : Array String) : IO Environment := do
  let imports : Array Import := mods.map fun m => { module := parseName m }
  -- No plugins, no extension initializers: candidate code is never executed.
  importModules imports {} (trustLevel := 0) (plugins := #[]) (loadExts := false)

def strArr (xs : Array Name) : Json := Json.arr (xs.map fun n => Json.str (nameStr n))

def listTrusted (cfg : Config) : IO UInt32 := do
  let env ← importEnv cfg.imports
  let trusted := cfg.trustedModules.map parseName
  let mut out : Array Json := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if trusted.contains m then
      for n in env.header.moduleData[i]!.constNames do
        -- escaped form: consumed by lean4export's name-literal decoder
        out := out.push (Json.str (toString n))
  IO.println (Json.compress (Json.mkObj [("constants", toJson (Json.arr out))]))
  return 0

/-- Full structural dump (kind, level params, type, value via `Expr.dbgToString`)
of every constant of the `trustedModules` modules, sorted by name. Used to
compare a judge-generated wrapper elaborated with the candidate model in scope
against the same wrapper elaborated against a judge stub. -/
def dumpModules (cfg : Config) : IO UInt32 := do
  let env ← importEnv cfg.imports
  let mods := cfg.trustedModules.map parseName
  let mut out : Array (String × Json) := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if mods.contains m then
      for n in env.header.moduleData[i]!.constNames do
        let some ci := env.find? n | continue
        let v := match ci.value? (allowOpaque := true) with
          | some e => toJson (toString e)
          | none => Json.null
        out := out.push (toString n, Json.mkObj [("kind", toJson (kindOf ci)),
          ("levelParams", toJson (ci.levelParams.map toString)),
          ("type", toJson (toString ci.type)), ("value", v),
          ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)])
  let sorted := out.qsort (fun a b => a.1 < b.1)
  IO.println (Json.compress (Json.mkObj (sorted.toList)))
  return 0

def check (cfg : Config) : IO UInt32 := do
  let env ← try importEnv cfg.imports catch e =>
    IO.println (Json.compress (Json.mkObj [("importOk", toJson (false)), ("importError", toJson (truncate (toString e)))]))
    return 0
  let trusted := cfg.trustedModules.map parseName
  let candMods := cfg.candidateModules.map parseName
  let expName := parseName cfg.expectedDecl
  let certName := parseName cfg.certificate
  let classify (n : Name) : String :=
    match moduleOf env n with
    | none => "unknown"
    | some m =>
      if trusted.contains m then "trusted"
      else if candMods.contains m then "candidate"
      else if isToolchainModule cfg m then "toolchain"
      else "other"
  -- Expected statement
  let some expCi := env.find? expName
    | IO.println (Json.compress (Json.mkObj [("importOk", toJson (true)), ("fatal", toJson (s!"expected decl {expName} missing"))]))
      return 0
  let some expVal := expCi.value? (allowOpaque := true)
    | IO.println (Json.compress (Json.mkObj [("importOk", toJson (true)), ("fatal", toJson ("expected decl has no value"))]))
      return 0
  let expVal := stripMData expVal
  let (expClosure, _) := closure env #[expName]
  let untrustedInStatement := expClosure.filter fun n =>
    let c := classify n; c != "trusted" && c != "toolchain"
  -- Certificate
  let mut fields : List (String × Json) := [("importOk", toJson (true))]
  fields := fields ++ [("expectedPreview", toJson (truncate (toString expVal))),
                       ("untrustedInStatement", toJson (strArr untrustedInStatement))]
  match env.find? certName with
  | none =>
    fields := fields ++ [("certificateFound", toJson (false))]
  | some certCi =>
    let lpsOk := certCi.levelParams.length == expCi.levelParams.length
    let certTy := stripMData <| certCi.type.instantiateLevelParams certCi.levelParams
      (expCi.levelParams.map mkLevelParam)
    let viaConst := certTy == mkConst expName (expCi.levelParams.map mkLevelParam)
    let typeEqual := lpsOk && (certTy == expVal || viaConst)
    -- native-lean: the statement is the expected lambda applied to the model.
    let modelName := parseName cfg.modelDecl
    let instName := parseName cfg.instDecl
    let applied := mkApp (mkConst expName) (mkConst modelName)
    let instOk := match env.find? instName with
      | some (.defnInfo v) => v.levelParams.isEmpty && stripMData v.value == applied
      | _ => false
    let typeEqual := if cfg.modelDecl.isEmpty then typeEqual else
      expCi.levelParams.isEmpty && certCi.levelParams.isEmpty &&
        (certTy == (mkApp expVal (mkConst modelName)).headBeta || certTy == applied ||
         (certTy == mkConst instName && instOk))
    let viaConst := if cfg.modelDecl.isEmpty then viaConst else certTy == applied || certTy == mkConst instName
    let (clo, missing) := closure env #[certName]
    let axioms := clo.filter fun n => match env.find? n with
      | some (.axiomInfo _) => true | _ => false
    let closureJson := clo.map fun n =>
      let ci := (env.find? n).get!
      Json.mkObj [("name", toJson (nameStr n)), ("kind", toJson (kindOf ci)),
        ("module", toJson (match moduleOf env n with | some m => nameStr m | none => ""))
        , ("origin", toJson (classify n)), ("unsafe", toJson (ci.isUnsafe)), ("partial", toJson (ci.isPartial))]
    fields := fields ++ [
      ("certificateFound", toJson (true)),
      ("certificateKind", toJson (kindOf certCi)),
      ("certificateModule", toJson (match moduleOf env certName with | some m => nameStr m | none => "")),
      ("certificateOrigin", toJson (classify certName)),
      ("levelParamsOk", toJson (lpsOk)),
      ("typeEqual", toJson (typeEqual)),
      ("typeViaExpectedConst", toJson (viaConst)),
      ("certificateTypePreview", toJson (truncate (toString certTy))),
      ("axioms", toJson (strArr axioms)),
      ("closure", toJson (Json.arr closureJson)),
      ("closureMissing", toJson (strArr missing))]
  -- native-lean: the candidate verifier model inside the statement.
  if !cfg.modelDecl.isEmpty then
    let modelName := parseName cfg.modelDecl
    match env.find? modelName with
    | none => fields := fields ++ [("modelFound", toJson false)]
    | some mci =>
      let (mclo, _) := closure env #[modelName]
      let maxioms := mclo.filter fun n => match env.find? n with
        | some (.axiomInfo _) => true | _ => false
      let mJson := mclo.map fun n =>
        let ci := (env.find? n).get!
        Json.mkObj [("name", toJson (nameStr n)), ("kind", toJson (kindOf ci)),
          ("module", toJson (match moduleOf env n with | some m => nameStr m | none => "")),
          ("origin", toJson (classify n)), ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)]
      fields := fields ++ [("modelFound", toJson true), ("modelKind", toJson (kindOf mci)),
        ("modelModule", toJson (match moduleOf env modelName with | some m => nameStr m | none => "")),
        ("modelOrigin", toJson (classify modelName)),
        ("modelAxioms", toJson (strArr maxioms)), ("modelClosure", Json.arr mJson)]
  -- Attribute / safety scan over every constant of every candidate module.
  let mut flagged : Array Json := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if candMods.contains m then
      for n in env.header.moduleData[i]!.constNames do
        let some ci := env.find? n | continue
        let implBy := Compiler.getImplementedBy? env n
        let ext := isExtern env n
        let init := hasInitAttr env n || isIOUnitInitFn env n
        let isOpaque := match ci with | .opaqueInfo _ => true | _ => false
        if implBy.isSome || ext || init || ci.isUnsafe || ci.isPartial || isOpaque then
          flagged := flagged.push <| Json.mkObj [("name", toJson (nameStr n)), ("module", toJson (nameStr m)),
            ("implementedBy", match implBy with | some t => toJson (nameStr t) | none => Json.null),
            ("extern", toJson (ext)), ("init", toJson (init)), ("unsafe", toJson (ci.isUnsafe)),
            ("partial", toJson (ci.isPartial)), ("opaque", toJson (isOpaque))]
  fields := fields ++ [("flagged", toJson (Json.arr flagged))]
  IO.println (Json.compress (Json.mkObj fields))
  return 0

def main (args : List String) : IO UInt32 := do
  setupSearchPath
  match args with
  | ["check", path] => check (← readConfig path)
  | ["list-trusted", path] => listTrusted (← readConfig path)
  | ["dump", path] => dumpModules (← readConfig path)
  | _ =>
    IO.eprintln "usage: arena-audit (check|list-trusted) <config.json>"
    return 2

end ArenaAudit
