import WasmPoC.Decode
/-!
# Preparation: validation, finite-wasm analyses, instrumentation table

nearcore at PV86 (`prepare.rs:28-29` → `prepare_v3.rs:397-470`):
1. validates the *original* module with wasmparser under NEAR's feature set
   (`features.rs:71-109`), any failure → `PrepareError::Deserialization`;
2. replaces the memory by `(memory 1024 2048)` and exports it (`prepare_v3.rs:126-139, 371-379`);
3. runs finite-wasm's gas and max-stack analyses (`prepare_v3.rs:418-429`);
4. instruments every function (`instrument_v3.rs:482-692`): a prologue that
   subtracts `operand_stack_max + frame_size` from a stack budget
   (`max_stack_height` = 262144) and charges `⌈frame/8⌉·regular_op_cost`
   gas, plus one gas check per optimized instrumentation point.

This module computes, per function, exactly the data the instrumentation
bakes in: the stack charge, the prologue gas, and the table
`pc ↦ (kind, fee)` of instrumentation points (finite-wasm 0.6.1
`gas/mod.rs` visitor + `gas/optimize.rs`, ported operator by operator).
-/
namespace WasmPoC

/-! ## PV86 constants (core/parameters/src/snapshots/…__85.json.snap; no 86.yaml exists) -/
def regularOpCost : Nat := 822756
def linearOpBaseCost : Nat := 26328192
def linearOpUnitCost : Nat := 822756
def maxStackHeight : Nat := 262144
def initialMemoryPages : Nat := 1024
def maxMemoryPages : Nat := 2048

/-! ## Validation (typing) with finite-wasm's max operand stack -/

inductive CK where
  | block | loop | if_ | else_ | func
  deriving DecidableEq

structure Ctrl where
  kind : CK
  results : Array VT
  height : Nat
  unreach : Bool
  /-- finite-wasm's `stack_polymorphic`: unlike validation it is inherited by
  nested frames (`max_stack/mod.rs` `new_frame`), so pushes inside blocks in
  dead code are not counted. -/
  fwPoly : Bool

def Ctrl.labelTypes (c : Ctrl) : Array VT :=
  if c.kind = .loop then #[] else c.results

structure VS where
  stack : Array VT := #[]
  ctrls : List Ctrl := []
  bytes : Nat := 0       -- byte size of the reachable operand stack
  maxBytes : Nat := 0

abbrev V := StateT VS (Except String)

def stackBytes (s : Array VT) : Nat := s.foldl (fun a t => a + t.size) 0

def push (t : VT) : V Unit := modify fun s =>
  let unr := match s.ctrls with
    | c :: _ => c.fwPoly
    | [] => false
  let st := s.stack.push t
  if unr then { s with stack := st }
  else
    let b := stackBytes st
    { s with stack := st, bytes := b, maxBytes := max s.maxBytes b }

def pop (want : Option VT) : V (Option VT) := do
  let s ← get
  match s.ctrls with
  | [] => throw "no frame"
  | c :: _ =>
    if s.stack.size = c.height then
      if c.unreach then pure want else throw "stack underflow"
    else
      let t := s.stack.back!
      set { s with stack := s.stack.pop }
      match want with
      | some w => if t = w then pure (some t) else throw "type mismatch"
      | none => pure (some t)

def popVals (ts : Array VT) : V Unit := do
  for t in ts.reverse do
    let _ ← pop (some t)

def pushVals (ts : Array VT) : V Unit := do
  for t in ts do push t

def setUnreachable : V Unit := modify fun s =>
  match s.ctrls with
  | c :: cs => { s with stack := s.stack.extract 0 c.height,
                         ctrls := { c with unreach := true, fwPoly := true } :: cs }
  | [] => s

def pushCtrl (k : CK) (rs : Array VT) : V Unit := modify fun s =>
  let p := match s.ctrls with
    | c :: _ => c.fwPoly
    | [] => false
  { s with ctrls := { kind := k, results := rs, height := s.stack.size, unreach := false,
                      fwPoly := p } :: s.ctrls }

def popCtrl : V Ctrl := do
  let s ← get
  match s.ctrls with
  | [] => throw "control underflow"
  | c :: cs =>
    popVals c.results
    let s ← get
    if s.stack.size ≠ c.height then throw "values remain at end of block"
    set { s with ctrls := cs }
    pure c

def label (l : Nat) : V Ctrl := do
  match (← get).ctrls[l]? with
  | some c => pure c
  | none => throw "unknown label"

def btResults : Option VT → Array VT
  | none => #[]
  | some t => #[t]

structure Env where
  m : Module
  funcTypes : Array FuncType   -- imports first, then defined functions
  locals : Array VT            -- params ++ locals of the current function
  hasMem : Bool

def checkInstr (e : Env) : Instr → V Unit
  | .unreachable => setUnreachable
  | .nop => pure ()
  | .block bt => pushCtrl .block (btResults bt)
  | .loop bt => pushCtrl .loop (btResults bt)
  | .if_ bt => do
    let _ ← pop (some .i32)
    pushCtrl .if_ (btResults bt)
  | .else_ => do
    let c ← popCtrl
    if c.kind ≠ .if_ then throw "else without if"
    pushCtrl .else_ c.results
  | .end_ => do
    let c ← popCtrl
    if c.kind = .if_ ∧ c.results.size ≠ 0 then throw "if without else must be [] -> []"
    if c.kind ≠ .func then pushVals c.results
  | .br l => do
    let c ← label l
    popVals c.labelTypes
    setUnreachable
  | .brIf l => do
    let _ ← pop (some .i32)
    let c ← label l
    popVals c.labelTypes
    pushVals c.labelTypes
  | .brTable ls d => do
    let _ ← pop (some .i32)
    let cd ← label d
    for l in ls do
      let c ← label l
      if c.labelTypes.size ≠ cd.labelTypes.size then throw "br_table arity"
      if c.labelTypes != cd.labelTypes then throw "br_table types"
    popVals cd.labelTypes
    setUnreachable
  | .ret => do
    let s ← get
    match s.ctrls.getLast? with
    | some f => popVals f.results
    | none => throw "no function frame"
    setUnreachable
  | .call f => do
    match e.funcTypes[f]? with
    | some ft => popVals ft.params; pushVals ft.results
    | none => throw "unknown function"
  | .drop => do let _ ← pop none
  | .select => do
    let _ ← pop (some .i32)
    let t1 ← pop none
    let t2 ← pop t1
    match t1, t2 with
    | some a, _ => push a
    | none, some b => push b
    | none, none => push .i32  -- polymorphic; any numeric type is fine for this subset
  | .localGet i => do
    match e.locals[i]? with
    | some t => push t
    | none => throw "unknown local"
  | .localSet i => do
    match e.locals[i]? with
    | some t => let _ ← pop (some t)
    | none => throw "unknown local"
  | .localTee i => do
    match e.locals[i]? with
    | some t => let _ ← pop (some t); push t
    | none => throw "unknown local"
  | .load w a _ => do
    if !e.hasMem then throw "unknown memory 0"
    if 2 ^ a > w then throw "alignment"
    let _ ← pop (some .i32); push .i32
  | .store w a _ => do
    if !e.hasMem then throw "unknown memory 0"
    if 2 ^ a > w then throw "alignment"
    let _ ← pop (some .i32); let _ ← pop (some .i32)
  | .memSize => do
    if !e.hasMem then throw "unknown memory 0"
    push .i32
  | .memGrow => do
    if !e.hasMem then throw "unknown memory 0"
    let _ ← pop (some .i32); push .i32
  | .i32Const _ => push .i32
  | .i64Const _ => push .i64
  | .i32Eqz | .i32Un _ => do let _ ← pop (some .i32); push .i32
  | .i32Rel _ | .i32Bin _ => do let _ ← pop (some .i32); let _ ← pop (some .i32); push .i32
  | .i64ExtendU => do let _ ← pop (some .i32); push .i64

/-- Validate one function body; returns finite-wasm's max operand-stack bytes. -/
def checkFunc (e : Env) (ft : FuncType) (code : Array Instr) : Except String Nat := do
  let act : V Unit := do
    pushCtrl .func ft.results
    let mut done := false
    for i in code do
      if done then throw "code after final end"
      checkInstr e i
      if (← get).ctrls.isEmpty then done := true
    if !done then throw "missing end"
  let (_, s) ← act.run {}
  pure s.maxBytes

/-! ## finite-wasm gas analysis (gas/mod.rs, gas/optimize.rs) -/

inductive IK where
  | pure | unreach | pre | post | between | memGrow
  deriving DecidableEq, Repr, Inhabited

structure Fee where
  c : Nat
  l : Nat
  deriving DecidableEq, Repr, Inhabited

def Fee.zero : Fee := ⟨0, 0⟩
def Fee.const (c : Nat) : Fee := ⟨c, 0⟩
def Fee.add (a b : Fee) : Fee := ⟨a.c + b.c, a.l + b.l⟩

structure Pt where
  off : Nat
  k : IK
  fee : Fee
  deriving Inhabited

inductive BTK where
  | loop (pre post : Nat) | untaken | forward

structure GF where
  poly : Bool
  kind : BTK

structure GS where
  pts : Array Pt := #[]
  cur : GF := ⟨false, .untaken⟩
  stack : List GF := []          -- head = most recently pushed (frame_stack.last())
  sched : Option (IK × Fee) := none
  off : Nat := 0

def gBefore (k : IK) (f : Fee) : StateM GS Unit := modify fun s =>
  { s with pts := s.pts.push ⟨s.off, if s.cur.poly then .unreach else k, f⟩ }

def gAfter (k : IK) (f : Fee) : StateM GS Unit := modify fun s => { s with sched := some (k, f) }

def gPure (f : Fee) : StateM GS Unit := gBefore .pure f
def gSide (f : Fee) : StateM GS Unit := do gBefore .pre f; gAfter .post Fee.zero

def gNewFrame (k : BTK) : StateM GS Unit := modify fun s =>
  { s with stack := s.cur :: s.stack, cur := ⟨s.cur.poly, k⟩ }

def gEndFrame : StateM GS Unit := modify fun s =>
  match s.stack with
  | f :: rest => { s with cur := f, stack := rest }
  | [] => s

def gPoly : StateM GS Unit := modify fun s => { s with cur := { s.cur with poly := true } }

def adjustKind (s : GS) (k : BTK) : GS × BTK :=
  match k with
  | .forward => (s, .forward)
  | .untaken => (s, .forward)
  | .loop pre post =>
    let pts := s.pts.modify post (fun p => { p with k := .post })
    let pts := pts.modify pre (fun p => { p with k := .pre })
    ({ s with pts := pts }, .loop pre post)

def gAdjust (fi : Nat) : StateM GS Unit := modify fun s =>
  if fi = 0 then
    let (s', k) := adjustKind s s.cur.kind
    { s' with cur := { s'.cur with kind := k } }
  else
    match s.stack[fi - 1]? with
    | some f =>
      let (s', k) := adjustKind s f.kind
      { s' with stack := s'.stack.set (fi - 1) { f with kind := k } }
    | none => s  -- unreachable for validated code (InvalidBrTarget)

def reg : Fee := Fee.const regularOpCost

def gInstr : Instr → StateM GS Unit
  | .unreachable => do gBefore .pre reg; gAfter .unreach Fee.zero; gPoly
  | .loop _ => do
    let pre := (← get).pts.size
    gBefore .pure Fee.zero
    let post := (← get).pts.size
    gAfter .pure reg
    gNewFrame (.loop pre post)
  | .end_ => do
    match (← get).cur.kind with
    | .forward => gSide Fee.zero
    | _ => gPure Fee.zero
    gEndFrame
  | .if_ _ => do gSide reg; gNewFrame .forward
  | .else_ => do gEndFrame; gNewFrame .forward; gSide Fee.zero
  | .block _ => do gPure Fee.zero; gNewFrame .untaken
  | .br l => do gSide reg; gAdjust l; gPoly
  | .brIf l => do gSide reg; gAdjust l
  | .brTable ls d => do
    gSide reg
    for l in ls do gAdjust l
    gAdjust d
    gPoly
  | .ret => do gSide reg; gAdjust (← get).stack.length; gPoly
  | .memGrow => do gBefore .memGrow ⟨linearOpBaseCost, linearOpUnitCost⟩; gAfter .post Fee.zero
  | .load .. | .store .. | .call _ => gSide reg
  | .i32Bin op => if 0x6D ≤ op ∧ op ≤ 0x70 then gSide reg else gPure reg  -- div/rem are binop_partial
  | _ => gPure reg

def mergeSame : IK → IK → Option IK
  | .unreach, _ => some .unreach
  | _, .unreach => some .unreach
  | .memGrow, _ => none     -- `unreachable!()` in finite-wasm: never happens
  | _, .memGrow => some .memGrow
  | .pure, k => some k
  | .pre, .pre | .pre, .pure => some .pre
  | .pre, _ => some .between
  | .post, .post | .post, .pure => some .post
  | .post, _ => some .between
  | .between, _ => some .between

def mergeAcross : IK → IK → Option IK
  | .pure, .pure => some .pure
  | .unreach, .unreach => some .unreach
  | .post, .pre => some .between
  | .pure, .pre => some .pre
  | .post, .pure => some .post
  | _, _ => none

def optimizeWith (pts : Array Pt) (merge : Pt → Pt → Option Pt) : Array Pt := Id.run do
  match pts[0]? with
  | none => pts
  | some p0 =>
    let mut out := #[]
    let mut prev := p0
    for i in [1:pts.size] do
      let cur := pts[i]!
      match merge prev cur with
      | some m => prev := m
      | none => out := out.push prev; prev := cur
    out.push prev

/-- `blockLevel = false` is the *ablation* used in the strategy doc: only same-offset
merging, i.e. every operator is charged on its own (instruction-level metering).
nearcore uses `blockLevel = true`. -/
def optimize (pts : Array Pt) (blockLevel : Bool := true) : Array Pt :=
  let p1 := optimizeWith pts fun a b =>
    if a.off = b.off then (mergeSame a.k b.k).map fun k => ⟨a.off, k, a.fee.add b.fee⟩ else none
  if !blockLevel then p1 else
  optimizeWith p1 fun a b =>
    (mergeAcross a.k b.k).map fun k => ⟨min a.off b.off, k, a.fee.add b.fee⟩

/-- Instrumentation points of one function, as `pc ↦ (kind, fee)`; only points
that `instrument_v3.rs:609-620` / `call_gas_instrumentation` actually emit
(kind ≠ Unreachable, fee ≠ 0). -/
def gasTable (code : Array Instr) (blockLevel : Bool := true) : Array (Option (IK × Fee)) := Id.run do
  let act : StateM GS Unit := do
    for i in [0:code.size] do
      modify fun s => match s.sched with
        | some (k, f) => { s with pts := s.pts.push ⟨i, k, f⟩, sched := none, off := i }
        | none => { s with off := i }
      gInstr code[i]!
  let (_, s) := act.run {}
  let pts := optimize s.pts blockLevel
  let mut tbl : Array (Option (IK × Fee)) := Array.replicate code.size none
  for p in pts do
    if p.k ≠ .unreach ∧ p.fee ≠ Fee.zero ∧ p.off < code.size then
      tbl := tbl.set! p.off (some (p.k, p.fee))
  tbl

/-! ## Prepared module -/

structure PFunc where
  type : FuncType
  locals : Array VT          -- declared locals (params excluded)
  code : Array Instr
  /-- matching `end` for `block`/`loop`/`if`, matching `else` (or `end`) for `if` -/
  endOf : Array Nat
  elseOf : Array Nat
  gas : Array (Option (IK × Fee))
  stackCharge : Nat          -- operand_stack_max + frame_size  (instrument_v3.rs:561)
  prologueGas : Nat          -- ⌈frame/8⌉ · regular_op_cost    (instrument_v3.rs:568-572)
  deriving Inhabited

inductive Host where
  | valueReturn | panic
  deriving Inhabited

structure Prepared where
  hosts : Array Host
  funcs : Array PFunc        -- defined functions; index = func index − hosts.size
  main : Nat                 -- function index of export "main"
  deriving Inhabited

/-- Block matching (validated code is well nested). -/
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

inductive PrepResult where
  | ok (p : Prepared)
  /-- `CompilationError(PrepareError(Deserialization))` -/
  | prepareError (why : String)
  | unsupported (why : String)

def hostOf (i : Import) (ts : Array FuncType) : Except String Host := do
  let ft ← match ts[i.type]? with
    | some t => pure t
    | none => throw "bad import type"
  if i.module ≠ "env" then throw "unsupported import module"
  match i.name with
  | "value_return" =>
    if ft == { params := #[.i64, .i64], results := #[] } then pure .valueReturn else throw "link"
  | "panic" =>
    if ft == { params := #[], results := #[] } then pure .panic else throw "link"
  | n => throw s!"host function {n} not in the PoC"

def prepare (bytes : ByteArray) (blockLevel : Bool := true) : PrepResult :=
  match decode bytes with
  | .error (.unsupported m) => .unsupported m
  | .error (.invalid m) => .prepareError m
  | .ok m => Id.run do
    -- module-level validation
    let some memOk := (match m.memory with
      | none => some true
      | some (mn, mx) => some (mn ≤ 65536 && (match mx with | some x => mn ≤ x && x ≤ 65536 | none => true)))
      | .prepareError "?"
    if !memOk then return .prepareError "memory limits"
    let mut fts : Array FuncType := #[]
    for i in m.imports do
      match m.types[i.type]? with
      | some t => fts := fts.push t
      | none => return .prepareError "import type"
    for t in m.funcTypes do
      match m.types[t]? with
      | some ft => fts := fts.push ft
      | none => return .prepareError "func type"
    let hasMem := m.memory.isSome
    let mut pfs := #[]
    for f in m.funcs do
      let ft := m.types[f.type]!
      let env : Env := { m := m, funcTypes := fts, locals := ft.params ++ f.locals, hasMem := hasMem }
      match checkFunc env ft f.code with
      | .error e => return .prepareError e
      | .ok opMax =>
        let frame := 64 + (ft.params ++ f.locals).foldl (fun a t => a + t.size) 0
        let (endOf, elseOf) := matchBlocks f.code
        pfs := pfs.push {
          type := ft, locals := f.locals, code := f.code, endOf := endOf, elseOf := elseOf,
          gas := gasTable f.code blockLevel, stackCharge := opMax + frame,
          prologueGas := (frame + 7) / 8 * regularOpCost }
    -- exports: names unique (wasmparser), indices valid
    let mut names : List String := []
    let mut main := none
    for (n, k, i) in m.exports do
      if names.contains n then return .prepareError "duplicate export"
      names := n :: names
      match k with
      | 0 => if i ≥ fts.size then return .prepareError "export index"
             if n = "main" then main := some i
      | 2 => if !hasMem ∨ i ≠ 0 then return .prepareError "export memory"
      | _ => return .unsupported "export kind"
    -- link (wasmtime `instantiate_pre`): unknown imports would be a LinkError
    let mut hosts := #[]
    for i in m.imports do
      match hostOf i m.types with
      | .ok h => hosts := hosts.push h
      | .error e => return .unsupported e
    match main with
    | none => return .unsupported "no main export"
    | some mi =>
      if mi < hosts.size then return .unsupported "main is an import"
      if (fts[mi]!).params.size ≠ 0 ∨ (fts[mi]!).results.size ≠ 0 then
        return .unsupported "main signature"
      return .ok { hosts := hosts, funcs := pfs, main := mi }

end WasmPoC
