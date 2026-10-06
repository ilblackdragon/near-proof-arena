import NearSpecV3.Wasm.Decode
import NearSpecV3.Wasm.FiniteWasm
import NearSpecV3.Wasm.HostSigs
import NearSpecV3.Wasm.InstrSize
/-!
# NEAR WASM (D3α): contract preparation as nearcore performs it at PV86

`prepare : Bytes → PrepResult` reproduces `prepare::prepare_contract(code, config, Wasmtime)`
(`prepare.rs:22-33` → `prepare/prepare_v3.rs:397-470`): one pass over the sections, in which
parsing, wasmparser validation and NEAR's limit checks are interleaved **in nearcore's order**, so
that the first failing check, and therefore the `PrepareError` variant, is the same. Then come
finite-wasm's analyses and the instrumentation limits. The result is not instrumented bytes but the
original module plus the data the instrumentation bakes in (gas table, stack charge, prologue gas),
as allowed by the requirements v0.2 §2.1.1.

Link-time behaviour (`instantiate_pre`, `wasmtime_runner/mod.rs:744-784`) and method resolution
(`:887-902`) are in `link`/`resolve`.
-/
namespace NearSpecV3.Wasm

/-! ## PV86 parameters (snapshot `…__85.json.snap`; no `86.yaml`) -/
structure NearCfg where
  regularOpCost : Nat := 822756
  linearOpBaseCost : Nat := 26328192
  linearOpUnitCost : Nat := 822756
  maxStackHeight : Nat := 262144
  initialMemoryPages : Nat := 1024
  maxMemoryPages : Nat := 2048
  maxTypes : Nat := 1024
  maxFunctions : Nat := 10000
  maxTables : Nat := 1
  maxTableElements : Nat := 10000
  maxFunctionBodySize : Nat := 196608
  maxLocals : Nat := 1000000
  maxParamsPerFunction : Nat := 64
  maxParamsPerContract : Nat := 50000
  maxBlocksPerFunction : Nat := 5000
  maxBlocksPerContract : Nat := 50000
  maxOperandStackBytes : Nat := 8192
  maxInstrumentedCodeSize : Nat := 16777216
  /-- wasmparser 0.228 `MAX_WASM_FUNCTION_LOCALS` (params + locals per function) -/
  wpMaxFunctionLocals : Nat := 50000

def pv86 : NearCfg := {}

def NearCfg.gas (c : NearCfg) : GasCfg := ⟨c.regularOpCost, c.linearOpBaseCost, c.linearOpUnitCost⟩

structure PFunc where
  type : FuncType
  locals : Array VT
  code : Array Instr
  endOf : Array Nat
  elseOf : Array Nat
  gas : Array (Option (IK × Fee))
  /-- operand-stack max + frame (`instrument_v3.rs:561`) -/
  stackCharge : Nat
  /-- `⌈frame/8⌉·regular_op_cost` (`instrument_v3.rs:568-572`) -/
  prologueGas : Nat
  deriving Inhabited

structure Prepared where
  m : Module
  ctx : Ctx
  /-- defined functions; absolute index = `m.imports.size + i` (all imports are functions) -/
  funcs : Array PFunc
  deriving Inhabited

inductive PrepResult where
  | ok (p : Prepared)
  /-- `CompilationError(PrepareError(<variant>))` -/
  | prepErr (variant : String) (why : String)
  /-- `CompilationError(WasmtimeCompileError { msg })`: the prepared module passes NEAR's checks
  but Wasmtime rejects it (`wasmtime_runner/mod.rs:571-580`), naming the instrumented function index -/
  | compileErr (fnIdx : Nat) (instrumentedSize : Nat)
  /-- the contract is outside `InD3α` (float types or operators) -/
  | outOfDomain (why : String)
  /-- a path this version of the spec does not decide (reported, never silently accepted) -/
  | unmodeled (why : String)

/-- Block matching for validated code. -/
def matchBlocks (code : Array Instr) : Array Nat × Array Nat := Id.run do
  let mut endOf := Array.replicate code.size 0
  let mut elseOf := Array.replicate code.size 0
  let mut open_ : List Nat := []
  for i in [0:code.size] do
    match code[i]! with
    | .block _ | .loop _ | .if_ _ => open_ := i :: open_
    | .else_ => match open_ with
      | o :: _ => elseOf := elseOf.set! o i
      | [] => pure ()
    | .end_ => match open_ with
      | o :: rest =>
        endOf := endOf.set! o i
        if elseOf[o]! = 0 then elseOf := elseOf.set! o i
        open_ := rest
      | [] => pure ()
    | _ => pure ()
  (endOf, elseOf)

/-! ## The early pass -/

inductive PE where
  | prep (variant why : String)
  | ood (why : String)
  | unmodeled (why : String)

/-- Preparation monad: parser state + module accumulator + NEAR budget counters. -/
structure PS where
  m : Module := {}
  funcBudget : Nat
  localBudget : Nat
  lastId : Nat := 0
  sawCode : Bool := false
  sawData : Bool := false

abbrev PM := StateT PS (ReaderT ByteArray (StateT Nat (Except PE)))

def liftP {α} (x : P α) : PM α := fun s b pos =>
  match (x.run b).run pos with
  | .ok (a, pos') => .ok ((a, s), pos')
  | .error (.invalid m) => .error (.prep "Deserialization" m)

def deser {α} (why : String) : PM α := throw (.prep "Deserialization" why)
def prepFail {α} (v why : String) : PM α := throw (.prep v why)

def anyFloatVT (ts : Array VT) : Bool := ts.any VT.isFloat

/-- Section ordering rank (wasmparser `Order`): data count sits between element and code. -/
def sectionRank (id : Nat) : Option Nat :=
  match id with
  | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4 | 5 => some 5 | 6 => some 6
  | 7 => some 7 | 8 => some 8 | 9 => some 9 | 12 => some 10 | 10 => some 11 | 11 => some 12
  | _ => none

/-- Module context for validation from what has been decoded so far. -/
def mkCtx (m : Module) : Ctx :=
  let fts := m.imports.filterMap (fun i => if i.kind = 0 then m.types[i.idx]? else none) ++
    m.funcTypes.map (fun t => m.types[t]!)
  let nf := fts.size
  let refs := Array.replicate nf false
  let mark (r : Array Bool) (e : ConstE) : Array Bool := match e with
    | .refFunc f => if f < r.size then r.set! f true else r
    | _ => r
  let refs := m.elems.foldl (fun r el => el.init.foldl mark r) refs
  let refs := m.globals.foldl (fun r g => mark r g.init) refs
  let refs := m.exports.foldl (fun r (_, k, i) => if k = 0 ∧ i < r.size then r.set! i true else r) refs
  { types := m.types, funcs := fts, tables := m.tables, memCount := m.memories.size,
    globals := m.globals.map (fun g => (g.type, g.mutable)),
    elems := m.elems.map (·.type), dataCount := m.dataCount, refs := refs }

def constOk (c : Ctx) (want : VT) (e : ConstE) : PM Unit := do
  match constType c e with
  | .ok t => if t = want then pure () else deser "constant expression type mismatch"
  | .error w => deser w

def sectionBody (cfg : NearCfg) (id sEnd : Nat) : PM Unit := do
  let s ← get
  let m := s.m
  match id with
  | 0 => do let _ ← liftP name; set (σ := Nat) sEnd   -- custom: discarded (`discard_custom_sections`)
  | 1 => do
    let n ← liftP u32
    if n > cfg.maxTypes then prepFail "TooManyTypes" "max_types_per_contract"
    let mut ts := #[]
    for _ in [0:n] do ts := ts.push (← liftP funcType)
    modify fun s => { s with m := { s.m with types := ts } }
  | 2 => do
    let is ← liftP (vecOf import_)
    -- validator.import_section
    for i in is do
      if i.kind = 0 ∧ i.idx ≥ m.types.size then deser "unknown type"
      if i.kind = 2 ∧ i.idx > 0 then pure ()
    -- transform_import_section (prepare_v3.rs:303-333)
    let mut fb := s.funcBudget
    for i in is do
      if i.module ≠ "env" then prepFail "Instantiate" "import from a module other than env"
      match i.kind with
      | 0 =>
        if fb = 0 then prepFail "TooManyFunctions" "imports"
        fb := fb - 1
      | 1 | 3 => prepFail "Instantiate" "table/global import"
      | 2 => prepFail "Memory" "memory import"
      | _ => deser "tag import"
    for i in is do
      match m.types[i.idx]? with
      | some ft => if anyFloatVT ft.params ∨ anyFloatVT ft.results then
          throw (.ood "float in an imported function type")
      | none => pure ()
    modify fun s => { s with m := { s.m with imports := is }, funcBudget := fb }
  | 3 => do
    let fs ← liftP (vecOf u32)
    for t in fs do if t ≥ m.types.size then deser "unknown type"
    modify fun s => { s with m := { s.m with funcTypes := fs } }
  | 4 => do
    let ts ← liftP (vecOf tableType)
    for t in ts do
      match t.lim.max with
      | some mx => if t.lim.min > mx then deser "table size minimum must not be greater than maximum"
      | none => pure ()
      if t.lim.min > 10000000 then deser "table too large"
    if ts.size > 100 then deser "tables count"
    if ts.size > cfg.maxTables then prepFail "TooManyTables" "max_tables_per_contract"
    for t in ts do
      if t.lim.min > cfg.maxTableElements then prepFail "TooManyTableElements" "initial size"
    modify fun s => { s with m := { s.m with tables := ts } }
  | 5 => do
    let ms ← liftP (vecOf (limits 65536))
    if ms.size > 1 then deser "multiple memories"
    for l in ms do
      match l.max with
      | some mx => if l.min > mx then deser "memory size minimum must not be greater than maximum"
      | none => pure ()
    modify fun s => { s with m := { s.m with memories := ms } }
  | 6 => do
    let gs ← liftP (vecOf global_)
    for g in gs do if g.type.isFloat then throw (.ood "float global")
    let c := mkCtx m
    for g in gs do constOk c g.type g.init
    modify fun s => { s with m := { s.m with globals := gs } }
  | 7 => do
    let es ← liftP (vecOf export_)
    let c := mkCtx m
    let mut names : Array String := #[]
    for (n, k, i) in es do
      if names.contains n then deser "duplicate export name"
      names := names.push n
      let bound := match k with
        | 0 => c.funcs.size | 1 => m.tables.size | 2 => m.memories.size | _ => m.globals.size
      if i ≥ bound then deser "unknown export index"
    modify fun s => { s with m := { s.m with exports := es } }
  | 8 => do
    let f ← liftP u32
    match (mkCtx m).funcs[f]? with
    | some ft => if ft.params.size ≠ 0 ∨ ft.results.size ≠ 0 then deser "invalid start function type"
    | none => deser "unknown function"
    modify fun s => { s with m := { s.m with start := some f } }
  | 9 => do
    let es ← liftP (vecOf elem)
    let m' := { m with elems := es }
    let c := mkCtx m'
    for e in es do
      match e.mode with
      | .active t off =>
        match m.tables[t]? with
        | some tt => if tt.elem ≠ e.type then deser "type mismatch: elem segment"
        | none => deser "unknown table"
        constOk c .i32 off
      | _ => pure ()
      for x in e.init do constOk c e.type x
    if es.size > 100000 then deser "element segments"
    modify fun s => { s with m := m' }
  | 12 => do
    let n ← liftP u32
    modify fun s => { s with m := { s.m with dataCount := some n } }
  | 10 => do
    let n ← liftP u32
    if n > s.funcBudget then prepFail "TooManyFunctions" "code section count"
    if n ≠ m.funcTypes.size then deser "function and code section have inconsistent lengths"
    modify fun s => { s with funcBudget := s.funcBudget - n, sawCode := true }
    let c := mkCtx m
    let mut fs := #[]
    for k in [0:n] do
      let sz ← liftP u32
      let st ← getThe Nat
      let bEnd := st + sz
      if bEnd > sEnd then deser "function body extends past section"
      if sz > cfg.maxFunctionBodySize then prepFail "FunctionBodyTooLarge" "max_function_body_size"
      let groups ← liftP localGroups
      let mut lb := (← get).localBudget
      for (cnt, _) in groups do
        if cnt > lb then prepFail "TooManyLocals" "max_locals_per_contract"
        lb := lb - cnt
      modify fun s => { s with localBudget := lb }
      let ft := m.types[m.funcTypes[k]!]!
      let nLocals := groups.foldl (fun a (cnt, _) => a + cnt) 0
      if ft.params.size + nLocals > cfg.wpMaxFunctionLocals then deser "too many locals"
      let (code, lens) ← liftP (operators bEnd)
      let f : Func := { type := m.funcTypes[k]!, localGroups := groups, code := code, bodySize := sz,
                        opLens := lens }
      if groups.any (·.2.isFloat) ∨ anyFloatVT ft.params ∨ anyFloatVT ft.results ∨
          code.any (fun i => match i with
            | .float _ => true
            | .select (some t) => t.isFloat
            | .block (some t) | .loop (some t) | .if_ (some t) => t.isFloat
            | _ => false) then
        throw (.ood "float type or operator in a function body")
      match validateBody c ft f.locals code with
      | .ok () => pure ()
      | .error e => deser e
      fs := fs.push f
    modify fun s => { s with m := { s.m with funcs := fs } }
  | 11 => do
    let ds ← liftP (vecOf data)
    match m.dataCount with
    | some n => if n ≠ ds.size then deser "data count and data section have inconsistent lengths"
    | none => pure ()
    let c := mkCtx m
    for d in ds do
      match d.active with
      | some (mi, off) =>
        if mi ≥ m.memories.size then deser "unknown memory"
        constOk c .i32 off
      | none => pure ()
    if ds.size > 100000 then deser "data segments"
    modify fun s => { s with m := { s.m with datas := ds }, sawData := true }
  | _ => deser "unknown section"

def earlyPass (cfg : NearCfg) : PM Unit := do
  for x in [0x00, 0x61, 0x73, 0x6D] do
    if (← liftP byte) ≠ x then deser "magic header not detected"
  for x in [0x01, 0x00, 0x00, 0x00] do
    if (← liftP byte) ≠ x then deser "unknown binary version"
  let b ← readThe ByteArray
  for _ in [0:b.size] do
    if (← getThe Nat) ≥ b.size then break
    let id ← liftP byte
    let len ← liftP u32
    let st ← getThe Nat
    if st + len > b.size then deser "section size mismatch: unexpected end"
    if id ≠ 0 then
      match sectionRank id with
      | some r =>
        if r ≤ (← get).lastId then deser "section out of order"
        modify fun s => { s with lastId := r }
      | none => deser "malformed section id"
    if id = 4 ∨ id = 11 ∨ id = 12 then
      modify fun s => { s with m := { s.m with rawSizes := s.m.rawSizes.push (id, len) } }
    -- section payloads are parsed with a reader bounded to the section
    let sub := b.extract 0 (st + len)
    let r := ((sectionBody cfg id (st + len)).run (← get)).run sub |>.run st
    match r with
    | .ok ((_, s'), pos') =>
      set s'
      if pos' ≠ st + len then deser "section size mismatch"
      set (σ := Nat) pos'
    | .error e => throw e
  -- validator.end
  let s ← get
  if s.m.funcTypes.size > 0 ∧ !s.sawCode then deser "function and code section have inconsistent lengths"
  match s.m.dataCount with
  | some n => if n > 0 ∧ !s.sawData then deser "data count and data section have inconsistent lengths"
  | none => pure ()

/-! ## Analysis + instrumentation limits (`prepare_v3.rs:418-468`, `instrument_v3.rs:482-692`) -/

/-- Exact length of nearcore's instrumented module (`InstrSize`). -/
def instrumentedSize (cfg : NearCfg) (m : Module) (pfs : Array PFunc) : Nat :=
  let G := m.globals.size
  let bodies := (m.funcs.zip pfs).map fun (f, pf) =>
    Size.body G pf.type f.localGroups f.code f.opLens pf.gas pf.stackCharge pf.prologueGas
  Size.moduleSize m bodies cfg.maxStackHeight

def prepare (cfg : NearCfg) (bytes : ByteArray) (blockLevel : Bool := true) : PrepResult :=
  let init : PS := { funcBudget := cfg.maxFunctions, localBudget := cfg.maxLocals }
  match ((earlyPass cfg).run init).run bytes |>.run 0 with
  | .error (.prep v w) => .prepErr v w
  | .error (.ood w) => .outOfDomain w
  | .error (.unmodeled w) => .unmodeled w
  | .ok ((_, s), _) => Id.run do
    let m := s.m
    let c := mkCtx m
    let nImp := m.imports.size
    let mut paramBudget := cfg.maxParamsPerContract
    let mut blockBudget := cfg.maxBlocksPerContract
    let mut pfs := #[]
    for f in m.funcs do
      let ft := m.types[f.type]!
      let locals := f.locals
      let all := ft.params ++ locals
      let opMax ← match maxStack c all f.code with
        | .ok v => pure v
        | .error e => return .prepErr "Deserialization" e
      if ft.params.size > cfg.maxParamsPerFunction then return .prepErr "TooManyParamsPerFunction" ""
      if ft.params.size > paramBudget then return .prepErr "TooManyParamsPerContract" ""
      paramBudget := paramBudget - ft.params.size
      if opMax > cfg.maxOperandStackBytes then return .prepErr "OperandStackTooLarge" ""
      let blocks := f.code.foldl (fun a i => match i with
        | .block _ | .loop _ | .if_ _ => a + 1
        | _ => a) 0
      if blocks > cfg.maxBlocksPerFunction then return .prepErr "TooManyBlocksPerFunction" ""
      if blocks > blockBudget then return .prepErr "TooManyBlocksPerContract" ""
      blockBudget := blockBudget - blocks
      let frame := 64 + all.foldl (fun a t => a + t.size) 0
      let (endOf, elseOf) := matchBlocks f.code
      pfs := pfs.push {
        type := ft, locals := locals, code := f.code, endOf := endOf, elseOf := elseOf,
        gas := gasTable cfg.gas f.code blockLevel, stackCharge := opMax + frame,
        prologueGas := (frame + 7) / 8 * cfg.regularOpCost }
    let _ := nImp
    let isz := instrumentedSize cfg m pfs
    if isz > cfg.maxInstrumentedCodeSize then
      return .prepErr "InstrumentedCodeTooLarge" ""
    -- Wasmtime re-validates the *instrumented* module with wasmparser 0.248
    -- (`MAX_WASM_FUNCTION_LOCALS` = 50,000, `MAX_WASM_FUNCTION_SIZE` = 7,654,321). Instrumentation
    -- adds two locals per function (`instrument_v3.rs:557-558`), so a function with
    -- `params + locals ∈ {49,999, 50,000}` passes NEAR's preparation and then fails to compile:
    -- an observed instance of hazard H1 (checkpoint-2 finding).
    let G := m.globals.size
    for k in [0:m.funcs.size] do
      let f := m.funcs[k]!
      let pf := pfs[k]!
      let nl := pf.type.params.size + pf.locals.size + 2
      let bodyLen := Size.bodyPayload G pf.type f.localGroups f.code f.opLens pf.gas pf.stackCharge
        pf.prologueGas
      if nl > 50000 ∨ bodyLen > 7654321 then
        return .compileErr (nImp + 3 + k) isz
    return .ok { m := m, ctx := c, funcs := pfs }

/-! ## Link and method resolution -/

inductive LinkResult where
  | ok
  /-- `FunctionCallError::LinkError { msg }`; unknown import has a fixed message; a signature
  mismatch carries wasmtime's text (compared modulo `msg` by the difftest) -/
  | linkError (msg : String)

def link (p : Prepared) : LinkResult := Id.run do
  for i in p.m.imports do
    match hostSig? i.name with
    | none => return .linkError "unknown or invalid import"
    | some sig => if sig != p.m.types[i.idx]! then return .linkError "*incompatible import type*"
  return .ok

inductive Resolve where
  | ok (fi : Nat)
  | notFound | invalidSignature

/-- `"\0" ++ method` must be an exported function of type `[] → []` (`wasmtime_runner/mod.rs:887-902`). -/
def resolve (p : Prepared) (method : String) : Resolve :=
  match p.m.exports.find? (fun (n, _, _) => n = method) with
  | some (_, 0, fi) =>
    let ft := p.ctx.funcs[fi]!
    if ft.params.size = 0 ∧ ft.results.size = 0 then .ok fi else .invalidSignature
  | _ => .notFound

end NearSpecV3.Wasm
