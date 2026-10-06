import NearSpecV3.Wasm.Syntax
/-!
# NEAR WASM (D3α): validation

WebAssembly 2.0 validation (spec §3, the algorithm of the spec appendix A.3) for NEAR's
feature set, as wasmparser 0.228 performs it inside `prepare_v3` (any failure →
`PrepareError::Deserialization`). Operand types are `Option VT` with `none` = the unknown type of
a polymorphic stack.
-/
namespace NearSpecV3.Wasm

inductive CK where
  | block | loop | if_ | else_ | func
  deriving DecidableEq

structure Ctrl where
  kind : CK
  results : Array VT
  height : Nat
  unreach : Bool

def Ctrl.labelTypes (c : Ctrl) : Array VT := if c.kind = .loop then #[] else c.results

/-- Module-level context for validating code (spec `C`). -/
structure Ctx where
  types : Array FuncType
  /-- types of all functions, imports first -/
  funcs : Array FuncType
  tables : Array TableType
  memCount : Nat
  globals : Array (VT × Bool)
  elems : Array VT
  dataCount : Option Nat
  /-- `C.refs`: functions referenced outside function bodies (elems, globals, exports) -/
  refs : Array Bool
  deriving Inhabited

structure VS where
  stack : Array (Option VT) := #[]
  ctrls : List Ctrl := []

abbrev V := StateT VS (Except String)

def vPush (t : Option VT) : V Unit := modify fun s => { s with stack := s.stack.push t }

def vPop : V (Option VT) := do
  let s ← get
  match s.ctrls with
  | [] => throw "no frame"
  | c :: _ =>
    if s.stack.size = c.height then
      if c.unreach then pure none else throw "type mismatch: operand stack empty"
    else
      set { s with stack := s.stack.pop }
      pure s.stack.back!

def vPopT (want : VT) : V Unit := do
  match ← vPop with
  | none => pure ()
  | some t => if t = want then pure () else throw "type mismatch"

def vPopVals (ts : Array VT) : V Unit := do
  for t in ts.reverse do vPopT t

def vPushVals (ts : Array VT) : V Unit := do
  for t in ts do vPush (some t)

def vUnreachable : V Unit := modify fun s =>
  match s.ctrls with
  | c :: cs => { s with stack := s.stack.extract 0 c.height, ctrls := { c with unreach := true } :: cs }
  | [] => s

def vPushCtrl (k : CK) (rs : Array VT) : V Unit := modify fun s =>
  { s with ctrls := { kind := k, results := rs, height := s.stack.size, unreach := false } :: s.ctrls }

def vPopCtrl : V Ctrl := do
  match (← get).ctrls with
  | [] => throw "control frames empty"
  | c :: _ =>
    vPopVals c.results
    let s ← get
    if s.stack.size ≠ c.height then throw "type mismatch: values remaining at end of block"
    set { s with ctrls := s.ctrls.tail }
    pure c

def vLabel (l : Nat) : V Ctrl := do
  match (← get).ctrls[l]? with
  | some c => pure c
  | none => throw "unknown label"

def btResults : BT → Array VT
  | none => #[]
  | some t => #[t]

def btOk : BT → Bool
  | some t => !t.isFloat || true
  | none => true

/-- Natural alignment (log2 of the access width) of integer loads/stores. -/
def memWidth (op : Nat) : Nat :=
  match op with
  | 0x28 | 0x36 | 0x34 | 0x35 | 0x3E => 4
  | 0x29 | 0x37 => 8
  | 0x2C | 0x2D | 0x30 | 0x31 | 0x3A | 0x3C => 1
  | _ => 2   -- 0x2E 0x2F 0x32 0x33 0x3B 0x3D

def loadResult (op : Nat) : VT := if op = 0x28 ∨ (0x2C ≤ op ∧ op ≤ 0x2F) then .i32 else .i64
def storeArg (op : Nat) : VT := if op = 0x36 ∨ op = 0x3A ∨ op = 0x3B then .i32 else .i64

/-- `(params, results)` of an integer `num` opcode. -/
def numSig (op : Nat) : Array VT × Array VT :=
  if op = 0x45 then (#[.i32], #[.i32])
  else if op ≤ 0x4F then (#[.i32, .i32], #[.i32])
  else if op = 0x50 then (#[.i64], #[.i32])
  else if op ≤ 0x5A then (#[.i64, .i64], #[.i32])
  else if op ≤ 0x69 then (#[.i32], #[.i32])
  else if op ≤ 0x78 then (#[.i32, .i32], #[.i32])
  else if op ≤ 0x7B then (#[.i64], #[.i64])
  else if op ≤ 0x8A then (#[.i64, .i64], #[.i64])
  else if op = 0xA7 then (#[.i64], #[.i32])
  else if op = 0xAC ∨ op = 0xAD then (#[.i32], #[.i64])
  else if op ≤ 0xC1 then (#[.i32], #[.i32])
  else (#[.i64], #[.i64])

def needMem (c : Ctx) : V Unit := if c.memCount = 0 then throw "unknown memory 0" else pure ()

def tableTy (c : Ctx) (t : Nat) : V VT := do
  match c.tables[t]? with
  | some tt => pure tt.elem
  | none => throw "unknown table"

def checkInstr (c : Ctx) (locals : Array VT) (fnResults : Array VT) : Instr → V Unit
  | .unreachable => vUnreachable
  | .nop => pure ()
  | .block bt => vPushCtrl .block (btResults bt)
  | .loop bt => vPushCtrl .loop (btResults bt)
  | .if_ bt => do vPopT .i32; vPushCtrl .if_ (btResults bt)
  | .else_ => do
    let f ← vPopCtrl
    if f.kind ≠ .if_ then throw "else found outside of an if block"
    vPushCtrl .else_ f.results
  | .end_ => do
    let f ← vPopCtrl
    if f.kind = .if_ ∧ f.results.size ≠ 0 then throw "type mismatch: if without else"
    if f.kind ≠ .func then vPushVals f.results
  | .br l => do
    let f ← vLabel l
    vPopVals f.labelTypes
    vUnreachable
  | .brIf l => do
    vPopT .i32
    let f ← vLabel l
    vPopVals f.labelTypes
    vPushVals f.labelTypes
  | .brTable ls d => do
    vPopT .i32
    let fd ← vLabel d
    let arity := fd.labelTypes.size
    for l in ls do
      let f ← vLabel l
      if f.labelTypes.size ≠ arity then throw "type mismatch: br_table arity"
      let saved ← get
      vPopVals f.labelTypes
      set saved
    vPopVals fd.labelTypes
    vUnreachable
  | .ret => do
    vPopVals fnResults
    vUnreachable
  | .call f => do
    match c.funcs[f]? with
    | some ft => vPopVals ft.params; vPushVals ft.results
    | none => throw "unknown function"
  | .callIndirect ty t => do
    if (← tableTy c t) ≠ .funcref then throw "indirect calls must go through a funcref table"
    match c.types[ty]? with
    | some ft => vPopT .i32; vPopVals ft.params; vPushVals ft.results
    | none => throw "unknown type"
  | .refNull t => vPush (some t)
  | .refIsNull => do
    match ← vPop with
    | some t => if !t.isRef then throw "type mismatch: ref.is_null"
    | none => pure ()
    vPush (some .i32)
  | .refFunc f => do
    if f ≥ c.funcs.size then throw "unknown function"
    if !(c.refs[f]?.getD false) then throw "undeclared function reference"
    vPush (some .funcref)
  | .drop => do let _ ← vPop
  | .select none => do
    vPopT .i32
    let t1 ← vPop
    let t2 ← vPop
    match t1, t2 with
    | some a, some b =>
      if a.isRef ∨ b.isRef then throw "type mismatch: select only takes integral types"
      if a ≠ b then throw "type mismatch: select operands"
      vPush (some a)
    | some a, none =>
      if a.isRef then throw "type mismatch: select only takes integral types"
      vPush (some a)
    | none, some b =>
      if b.isRef then throw "type mismatch: select only takes integral types"
      vPush (some b)
    | none, none => vPush none
  | .select (some t) => do vPopT .i32; vPopT t; vPopT t; vPush (some t)
  | .localGet i => do
    match locals[i]? with
    | some t => vPush (some t)
    | none => throw "unknown local"
  | .localSet i => do
    match locals[i]? with
    | some t => vPopT t
    | none => throw "unknown local"
  | .localTee i => do
    match locals[i]? with
    | some t => vPopT t; vPush (some t)
    | none => throw "unknown local"
  | .globalGet g => do
    match c.globals[g]? with
    | some (t, _) => vPush (some t)
    | none => throw "unknown global"
  | .globalSet g => do
    match c.globals[g]? with
    | some (t, m) => if !m then throw "global is immutable" else vPopT t
    | none => throw "unknown global"
  | .tableGet t => do let et ← tableTy c t; vPopT .i32; vPush (some et)
  | .tableSet t => do let et ← tableTy c t; vPopT et; vPopT .i32
  | .tableSize t => do let _ ← tableTy c t; vPush (some .i32)
  | .tableGrow t => do let et ← tableTy c t; vPopT .i32; vPopT et; vPush (some .i32)
  | .tableFill t => do let et ← tableTy c t; vPopT .i32; vPopT et; vPopT .i32
  | .tableCopy d s => do
    let dt ← tableTy c d
    let st ← tableTy c s
    if dt ≠ st then throw "type mismatch: table.copy"
    vPopT .i32; vPopT .i32; vPopT .i32
  | .tableInit e t => do
    let tt ← tableTy c t
    match c.elems[e]? with
    | some et => if et ≠ tt then throw "type mismatch: table.init"
    | none => throw "unknown elem segment"
    vPopT .i32; vPopT .i32; vPopT .i32
  | .elemDrop e => if e < c.elems.size then pure () else throw "unknown elem segment"
  | .load op a _ => do
    needMem c
    if 2 ^ a > memWidth op then throw "alignment must not be larger than natural"
    vPopT .i32; vPush (some (loadResult op))
  | .store op a _ => do
    needMem c
    if 2 ^ a > memWidth op then throw "alignment must not be larger than natural"
    vPopT (storeArg op); vPopT .i32
  | .memSize => do needMem c; vPush (some .i32)
  | .memGrow => do needMem c; vPopT .i32; vPush (some .i32)
  | .memCopy | .memFill => do needMem c; vPopT .i32; vPopT .i32; vPopT .i32
  | .memInit d => do
    needMem c
    match c.dataCount with
    | some n => if d ≥ n then throw "unknown data segment"
    | none => throw "data count section required"
    vPopT .i32; vPopT .i32; vPopT .i32
  | .dataDrop d => do
    match c.dataCount with
    | some n => if d ≥ n then throw "unknown data segment"
    | none => throw "data count section required"
  | .i32Const _ => vPush (some .i32)
  | .i64Const _ => vPush (some .i64)
  | .num op => do
    let (ps, rs) := numSig op
    vPopVals ps; vPushVals rs
  | .float _ => throw "float operator (out of domain in D3α; validation not modelled)"

/-- Validate one function body (operators, ending with the function's `end`). -/
def validateBody (c : Ctx) (ft : FuncType) (locals : Array VT) (code : Array Instr) :
    Except String Unit := do
  let act : V Unit := do
    vPushCtrl .func ft.results
    let mut done := false
    for i in code do
      if done then throw "operators remaining after end of function"
      checkInstr c (ft.params ++ locals) ft.results i
      if (← get).ctrls.isEmpty then done := true
    if !done then throw "function body without end"
  let _ ← act.run {}
  pure ()

/-- Type of a constant expression, given the module context. -/
def constType (c : Ctx) : ConstE → Except String VT
  | .i32 _ => .ok .i32
  | .i64 _ => .ok .i64
  | .refNull t => .ok t
  | .refFunc f => if f < c.funcs.size then .ok .funcref else .error "unknown function"
  | .globalGet _ => .error "constant expression required (no imported globals)"
  | .float _ => .error "float (out of domain)"

end NearSpecV3.Wasm
