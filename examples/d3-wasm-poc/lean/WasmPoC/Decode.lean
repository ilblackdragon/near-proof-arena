import WasmPoC.Syntax
/-!
# Binary decoder (WebAssembly 1.0 binary format, PoC subset)

`Err.invalid` = the bytes are not a valid module (nearcore: wasmparser fails →
`PrepareError::Deserialization`, `prepare_v3.rs:65-69`); `Err.unsupported` =
valid WebAssembly that is outside the PoC subset (the difftest counts it as a
disagreement, so the generator never emits it).
Every loop is bounded by the input length, so decoding is total.
-/
namespace WasmPoC

inductive Err where
  | invalid (msg : String)
  | unsupported (msg : String)
  deriving Repr, Inhabited

abbrev P := ReaderT ByteArray (StateT Nat (Except Err))

def fail {α} (m : String) : P α := throw (.invalid m)
def unsup {α} (m : String) : P α := throw (.unsupported m)

def byte : P Nat := do
  let b ← read
  let p ← get
  if h : p < b.size then
    set (p + 1)
    pure b[p].toNat
  else fail "unexpected end"

/-- Unsigned LEB128 of at most `bits` bits (spec §5.2.2). -/
def uleb (bits : Nat) : P Nat := do
  let mut acc := 0
  let mut shift := 0
  for _ in [0:(bits + 6) / 7] do
    let b ← byte
    acc := acc + (b % 128) * 2 ^ shift
    if b < 128 then
      if acc ≥ 2 ^ bits then fail "uleb overflow"
      return acc
    shift := shift + 7
  fail "uleb too long"

/-- Signed LEB128 of `bits` bits, returned as a two's-complement `Nat < 2^bits`. -/
def sleb (bits : Nat) : P Nat := do
  let mut acc := 0
  let mut shift := 0
  for _ in [0:(bits + 6) / 7] do
    let b ← byte
    acc := acc + (b % 128) * 2 ^ shift
    shift := shift + 7
    if b < 128 then
      let v : Int := if b ≥ 64 then (acc : Int) - 2 ^ shift else acc
      if v < -(2 ^ (bits - 1) : Int) ∨ v ≥ 2 ^ (bits - 1) then fail "sleb overflow"
      return (v % (2 ^ bits : Int)).toNat
  fail "sleb too long"

def u32 : P Nat := uleb 32

def name : P String := do
  let n ← u32
  let b ← read
  let p ← get
  if p + n > b.size then fail "name past end"
  set (p + n)
  match String.fromUTF8? (b.extract p (p + n)) with
  | some s => pure s
  | none => fail "name not utf8"

def valType : P VT := do
  match ← byte with
  | 0x7F => pure .i32
  | 0x7E => pure .i64
  | 0x7D | 0x7C => unsup "float value type"
  | _ => fail "bad value type"

def vecOf {α} (f : P α) : P (Array α) := do
  let n ← u32
  let b ← read
  if n > b.size then fail "vector too long"
  let mut out := #[]
  for _ in [0:n] do
    out := out.push (← f)
  pure out

def blockType : P (Option VT) := do
  let b ← read
  let p ← get
  if h : p < b.size then
    match b[p].toNat with
    | 0x40 => set (p + 1); pure none
    | 0x7F => set (p + 1); pure (some .i32)
    | 0x7E => set (p + 1); pure (some .i64)
    | _ => unsup "type-index block type"
  else fail "eof"

def memarg : P (Nat × Nat) := do
  let a ← u32
  let o ← u32
  pure (a, o)

def instr : P Instr := do
  match ← byte with
  | 0x00 => pure .unreachable
  | 0x01 => pure .nop
  | 0x02 => pure (.block (← blockType))
  | 0x03 => pure (.loop (← blockType))
  | 0x04 => pure (.if_ (← blockType))
  | 0x05 => pure .else_
  | 0x0B => pure .end_
  | 0x0C => pure (.br (← u32))
  | 0x0D => pure (.brIf (← u32))
  | 0x0E => do let ls ← vecOf u32; pure (.brTable ls (← u32))
  | 0x0F => pure .ret
  | 0x10 => pure (.call (← u32))
  | 0x1A => pure .drop
  | 0x1B => pure .select
  | 0x20 => pure (.localGet (← u32))
  | 0x21 => pure (.localSet (← u32))
  | 0x22 => pure (.localTee (← u32))
  | 0x28 => do let (a, o) ← memarg; pure (.load 4 a o)
  | 0x2D => do let (a, o) ← memarg; pure (.load 1 a o)
  | 0x36 => do let (a, o) ← memarg; pure (.store 4 a o)
  | 0x3A => do let (a, o) ← memarg; pure (.store 1 a o)
  | 0x3F => do
    if (← byte) ≠ 0 then fail "memidx"
    pure .memSize
  | 0x40 => do
    if (← byte) ≠ 0 then fail "memidx"
    pure .memGrow
  | 0x41 => pure (.i32Const (UInt32.ofNat (← sleb 32)))
  | 0x42 => pure (.i64Const (UInt64.ofNat (← sleb 64)))
  | 0x45 => pure .i32Eqz
  | 0xAD => pure .i64ExtendU
  | op =>
    if 0x46 ≤ op ∧ op ≤ 0x4F then pure (.i32Rel op)
    else if 0x67 ≤ op ∧ op ≤ 0x69 then pure (.i32Un op)
    else if 0x6A ≤ op ∧ op ≤ 0x78 then pure (.i32Bin op)
    else unsup s!"opcode {op}"

/-- A function body: locals, then operators up to the `end` closing the body. -/
def body (sizeEnd : Nat) : P (Array VT × Array Instr) := do
  let groups ← vecOf (do let n ← u32; let t ← valType; pure (n, t))
  let mut locals := #[]
  let mut total := 0
  for (n, t) in groups do
    total := total + n
    if total > 1000000 then fail "too many locals"
    for _ in [0:n] do locals := locals.push t
  let mut code := #[]
  let mut depth := 1
  let b ← read
  for _ in [0:b.size] do
    if depth = 0 then break
    let i ← instr
    match i with
    | .block _ | .loop _ | .if_ _ => depth := depth + 1
    | .end_ => depth := depth - 1
    | _ => pure ()
    code := code.push i
  if depth ≠ 0 then fail "unterminated body"
  if (← get) ≠ sizeEnd then fail "body size mismatch"
  pure (locals, code)

def limits : P (Nat × Option Nat) := do
  match ← byte with
  | 0 => pure (← u32, none)
  | 1 => do let mn ← u32; let mx ← u32; pure (mn, some mx)
  | _ => unsup "memory flags"

def sectionP (m : Module) (id : Nat) (sEnd : Nat) : P Module := do
  match id with
  | 0 => do  -- custom: name must decode; content discarded (`discard_custom_sections`)
    let _ ← name
    set sEnd
    pure m
  | 1 => do
    let ts ← vecOf (do
      if (← byte) ≠ 0x60 then fail "functype tag"
      let ps ← vecOf valType
      let rs ← vecOf valType
      if rs.size > 1 then fail "multi-value disabled"
      pure ({ params := ps, results := rs } : FuncType))
    pure { m with types := ts }
  | 2 => do
    let is ← vecOf (do
      let mo ← name
      let nm ← name
      match ← byte with
      | 0 => pure ({ module := mo, name := nm, type := ← u32 } : Import)
      | _ => unsup "non-function import")
    pure { m with imports := is }
  | 3 => pure { m with funcTypes := ← vecOf u32 }
  | 5 => do
    let ms ← vecOf limits
    if ms.size > 1 then fail "multi-memory disabled"
    pure { m with memory := ms[0]? }
  | 7 => do
    let es ← vecOf (do let n ← name; let k ← byte; let i ← u32; pure (n, k, i))
    pure { m with exports := es }
  | 10 => do
    let n ← u32
    if n ≠ m.funcTypes.size then fail "function/code count mismatch"
    let mut fs := #[]
    for i in [0:n] do
      let sz ← u32
      let st ← get
      let (ls, code) ← body (st + sz)
      fs := fs.push { type := m.funcTypes[i]!, locals := ls, code := code }
    pure { m with funcs := fs }
  | _ => unsup s!"section {id}"

def module : P Module := do
  for x in [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00] do
    if (← byte) ≠ x then fail "bad header"
  let b ← read
  let mut m : Module := {}
  let mut lastId := 0
  for _ in [0:b.size] do
    if (← get) ≥ b.size then break
    let id ← byte
    let len ← u32
    let st ← get
    if st + len > b.size then fail "section past end"
    if id ≠ 0 then
      if id ≤ lastId then fail "section order"
      lastId := id
    m ← sectionP m id (st + len)
    if (← get) ≠ st + len then fail "section size mismatch"
  if m.funcs.size ≠ m.funcTypes.size then fail "function/code count mismatch"
  pure m

def decode (b : ByteArray) : Except Err Module :=
  (module.run b).run' 0

end WasmPoC
