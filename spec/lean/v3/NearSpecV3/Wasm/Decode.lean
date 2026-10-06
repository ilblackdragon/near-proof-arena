import NearSpecV3.Wasm.Syntax
/-!
# NEAR WASM (D3α): binary decoder

WebAssembly binary format (spec §5) for the feature set of `Syntax`. Every loop is bounded by the
input size, so all parsers are total. A malformed input is `.invalid` (nearcore:
`PrepareError::Deserialization`, `prepare/prepare_v3.rs:65-69`). Section-level orchestration, limit
checks and validation are interleaved in `Prepare`, in nearcore's order.
-/
namespace NearSpecV3.Wasm

inductive DErr where
  | invalid (msg : String)
  deriving Repr, Inhabited

/-- Parser over a byte array with a position; `ReaderT` input, `StateT` position. -/
abbrev P := ReaderT ByteArray (StateT Nat (Except DErr))

def fail {α} (m : String) : P α := throw (.invalid m)

def byte : P Nat := do
  let b ← read
  let p ← get
  if h : p < b.size then
    set (p + 1)
    pure b[p].toNat
  else fail "unexpected end"

def peekByte : P (Option Nat) := do
  let b ← read
  let p ← get
  pure (if h : p < b.size then some b[p].toNat else none)

/-- Unsigned LEB128 of at most `bits` bits, ≤ ⌈bits/7⌉ bytes, unused high bits of the last byte zero. -/
def uleb (bits : Nat) : P Nat := do
  let mut acc := 0
  let mut shift := 0
  for _ in [0:(bits + 6) / 7] do
    let b ← byte
    acc := acc + (b % 128) * 2 ^ shift
    if b < 128 then
      if acc ≥ 2 ^ bits then fail "integer too large"
      return acc
    shift := shift + 7
  fail "integer representation too long"

/-- Signed LEB128 of `bits` bits as a two's-complement `Nat < 2^bits`. -/
def sleb (bits : Nat) : P Nat := do
  let mut acc := 0
  let mut shift := 0
  for _ in [0:(bits + 6) / 7] do
    let b ← byte
    acc := acc + (b % 128) * 2 ^ shift
    shift := shift + 7
    if b < 128 then
      let v : Int := if b ≥ 64 then (acc : Int) - 2 ^ shift else acc
      if v < -(2 ^ (bits - 1) : Int) ∨ v ≥ 2 ^ (bits - 1) then fail "integer too large"
      return (v % (2 ^ bits : Int)).toNat
  fail "integer representation too long"

def u32 : P Nat := uleb 32

def bytesN (n : Nat) : P ByteArray := do
  let b ← read
  let p ← get
  if p + n > b.size then fail "unexpected end"
  set (p + n)
  pure (b.extract p (p + n))

/-- Names: `MAX_WASM_STRING_SIZE` = 100,000 (wasmparser 0.228 `binary_reader.rs:757-770`), UTF-8. -/
def name : P String := do
  let n ← u32
  if n > 100000 then fail "string too long"
  match String.fromUTF8? (← bytesN n) with
  | some s => pure s
  | none => fail "malformed UTF-8"

def valType : P VT := do
  match ← byte with
  | 0x7F => pure .i32
  | 0x7E => pure .i64
  | 0x7D => pure .f32
  | 0x7C => pure .f64
  | 0x70 => pure .funcref
  | 0x6F => pure .externref
  | _ => fail "invalid value type"

def refType : P VT := do
  match ← byte with
  | 0x70 => pure .funcref
  | 0x6F => pure .externref
  | _ => fail "invalid reference type"

/-- Vector with element count bounded by the remaining input (each element ≥ 1 byte). -/
def vecOf {α} (f : P α) : P (Array α) := do
  let n ← u32
  let b ← read
  if n > b.size then fail "vector too long"
  let mut out := #[]
  for _ in [0:n] do
    out := out.push (← f)
  pure out

def blockType : P BT := do
  match ← peekByte with
  | some 0x40 => do let _ ← byte; pure none
  | some 0x7F | some 0x7E | some 0x7D | some 0x7C | some 0x70 | some 0x6F => pure (some (← valType))
  | some _ => fail "type-index block types need multi-value (disabled)"
  | none => fail "unexpected end"

def memarg : P (Nat × Nat) := do
  let a ← u32
  let o ← u32
  pure (a, o)

def zeroByte : P Unit := do
  if (← byte) ≠ 0 then fail "zero byte expected"

def isFloatOp (op : Nat) : Bool :=
  op = 0x2A || op = 0x2B || op = 0x38 || op = 0x39 || op = 0x43 || op = 0x44 ||
  (0x5B ≤ op && op ≤ 0x66) || (0x8B ≤ op && op ≤ 0xA6) || (0xA8 ≤ op && op ≤ 0xAB) ||
  (0xAE ≤ op && op ≤ 0xBF)

def isIntNumOp (op : Nat) : Bool :=
  (0x45 ≤ op && op ≤ 0x5A) || (0x67 ≤ op && op ≤ 0x8A) || op = 0xA7 || op = 0xAC || op = 0xAD ||
  (0xC0 ≤ op && op ≤ 0xC4)

def instr : P Instr := do
  let op ← byte
  match op with
  | 0x00 => pure .unreachable
  | 0x01 => pure .nop
  | 0x02 => pure (.block (← blockType))
  | 0x03 => pure (.loop (← blockType))
  | 0x04 => pure (.if_ (← blockType))
  | 0x05 => pure .else_
  | 0x0B => pure .end_
  | 0x0C => pure (.br (← u32))
  | 0x0D => pure (.brIf (← u32))
  | 0x0E => do
    let n ← u32
    if n > 128 * 1024 then fail "br_table size"   -- MAX_WASM_BR_TABLE_SIZE
    let mut ls := #[]
    for _ in [0:n] do ls := ls.push (← u32)
    pure (.brTable ls (← u32))
  | 0x0F => pure .ret
  | 0x10 => pure (.call (← u32))
  | 0x11 => do let ty ← u32; let t ← u32; pure (.callIndirect ty t)
  | 0x1A => pure .drop
  | 0x1B => pure (.select none)
  | 0x1C => do
    let ts ← vecOf valType
    if ts.size ≠ 1 then fail "invalid result arity for select"
    pure (.select (some ts[0]!))
  | 0x20 => pure (.localGet (← u32))
  | 0x21 => pure (.localSet (← u32))
  | 0x22 => pure (.localTee (← u32))
  | 0x23 => pure (.globalGet (← u32))
  | 0x24 => pure (.globalSet (← u32))
  | 0x25 => pure (.tableGet (← u32))
  | 0x26 => pure (.tableSet (← u32))
  | 0x3F => do zeroByte; pure .memSize
  | 0x40 => do zeroByte; pure .memGrow
  | 0x41 => pure (.i32Const (UInt32.ofNat (← sleb 32)))
  | 0x42 => pure (.i64Const (UInt64.ofNat (← sleb 64)))
  | 0x43 => do let _ ← bytesN 4; pure (.float op)
  | 0x44 => do let _ ← bytesN 8; pure (.float op)
  | 0xD0 => pure (.refNull (← refType))
  | 0xD1 => pure .refIsNull
  | 0xD2 => pure (.refFunc (← u32))
  | 0xFC => do
    match ← u32 with
    | 8 => do let d ← u32; zeroByte; pure (.memInit d)
    | 9 => pure (.dataDrop (← u32))
    | 10 => do zeroByte; zeroByte; pure .memCopy
    | 11 => do zeroByte; pure .memFill
    | 12 => do let e ← u32; let t ← u32; pure (.tableInit e t)
    | 13 => pure (.elemDrop (← u32))
    | 14 => do let d ← u32; let s ← u32; pure (.tableCopy d s)
    | 15 => pure (.tableGrow (← u32))
    | 16 => pure (.tableSize (← u32))
    | 17 => pure (.tableFill (← u32))
    | k => if k ≤ 7 then pure (.float (0xFC00 + k)) else fail s!"unknown 0xFC opcode {k}"
  | _ =>
    if 0x28 ≤ op ∧ op ≤ 0x35 ∧ op ≠ 0x2A ∧ op ≠ 0x2B then do
      let (a, o) ← memarg; pure (.load op a o)
    else if 0x36 ≤ op ∧ op ≤ 0x3E ∧ op ≠ 0x38 ∧ op ≠ 0x39 then do
      let (a, o) ← memarg; pure (.store op a o)
    else if op = 0x2A ∨ op = 0x2B ∨ op = 0x38 ∨ op = 0x39 then do
      let _ ← memarg; pure (.float op)
    else if isIntNumOp op then pure (.num op)
    else if isFloatOp op then pure (.float op)
    else fail s!"illegal opcode {op}"

/-- Constant expression terminated by `end` (single instruction: no extended-const). -/
def constExpr : P ConstE := do
  let e ← match ← byte with
    | 0x41 => pure (ConstE.i32 (UInt32.ofNat (← sleb 32)))
    | 0x42 => pure (ConstE.i64 (UInt64.ofNat (← sleb 64)))
    | 0x43 => do let b ← bytesN 4; pure (ConstE.float b.size)
    | 0x44 => do let b ← bytesN 8; pure (ConstE.float b.size)
    | 0xD0 => pure (ConstE.refNull (← refType))
    | 0xD2 => pure (ConstE.refFunc (← u32))
    | 0x23 => pure (ConstE.globalGet (← u32))
    | _ => fail "constant expression required"
  if (← byte) ≠ 0x0B then fail "constant expression required"
  pure e

def limits (maxPagesOk : Nat) : P Limits := do
  match ← byte with
  | 0 => do
    let mn ← u32
    if mn > maxPagesOk then fail "limit too large"
    pure ⟨mn, none⟩
  | 1 => do
    let mn ← u32
    let mx ← u32
    if mn > maxPagesOk ∨ mx > maxPagesOk then fail "limit too large"
    pure ⟨mn, some mx⟩
  | _ => fail "invalid limits flags (shared/memory64 disabled)"

def funcType : P FuncType := do
  if (← byte) ≠ 0x60 then fail "only function types (GC disabled)"
  let ps ← vecOf valType
  let rs ← vecOf valType
  if ps.size > 1000 then fail "too many params"
  if rs.size > 1 then fail "multi-value disabled"
  pure { params := ps, results := rs }

def import_ : P Import := do
  let mo ← name
  let nm ← name
  match ← byte with
  | 0 => pure { module := mo, name := nm, kind := 0, idx := ← u32 }
  | 1 => do let _ ← refType; let _ ← limits (2 ^ 32 - 1); pure { module := mo, name := nm, kind := 1, idx := 0 }
  | 2 => do let _ ← limits 65536; pure { module := mo, name := nm, kind := 2, idx := 0 }
  | 3 => do let _ ← valType; let _ ← byte; pure { module := mo, name := nm, kind := 3, idx := 0 }
  | _ => fail "tags/unknown import kind"

def tableType : P TableType := do
  let t ← refType
  let l ← limits (2 ^ 32 - 1)
  pure ⟨t, l⟩

def global_ : P Global := do
  let t ← valType
  let m ← match ← byte with
    | 0 => pure false
    | 1 => pure true
    | _ => fail "malformed mutability"
  pure { type := t, mutable := m, init := ← constExpr }

def export_ : P (String × Nat × Nat) := do
  let n ← name
  let k ← byte
  if k > 3 then fail "invalid export kind"
  pure (n, k, ← u32)

def elemKind : P Unit := do
  if (← byte) ≠ 0x00 then fail "malformed element kind"

/-- Element segments, all eight binary encodings (spec §5.5.12). -/
def elem : P Elem := do
  let flag ← u32
  let funcs : P (Array ConstE) := do
    let xs ← vecOf u32
    pure (xs.map ConstE.refFunc)
  match flag with
  | 0 => do
    let off ← constExpr
    pure { type := .funcref, mode := .active 0 off, init := ← funcs }
  | 1 => do elemKind; pure { type := .funcref, mode := .passive, init := ← funcs }
  | 2 => do
    let t ← u32
    let off ← constExpr
    elemKind
    pure { type := .funcref, mode := .active t off, init := ← funcs }
  | 3 => do elemKind; pure { type := .funcref, mode := .declarative, init := ← funcs }
  | 4 => do
    let off ← constExpr
    pure { type := .funcref, mode := .active 0 off, init := ← vecOf constExpr }
  | 5 => do let t ← refType; pure { type := t, mode := .passive, init := ← vecOf constExpr }
  | 6 => do
    let tab ← u32
    let off ← constExpr
    let t ← refType
    pure { type := t, mode := .active tab off, init := ← vecOf constExpr }
  | 7 => do let t ← refType; pure { type := t, mode := .declarative, init := ← vecOf constExpr }
  | _ => fail "malformed element segment flags"

def data : P Data := do
  match ← u32 with
  | 0 => do
    let off ← constExpr
    let n ← u32
    pure { active := some (0, off), bytes := ← bytesN n }
  | 1 => do let n ← u32; pure { active := none, bytes := ← bytesN n }
  | 2 => do
    let m ← u32
    let off ← constExpr
    let n ← u32
    pure { active := some (m, off), bytes := ← bytesN n }
  | _ => fail "malformed data segment flags"

/-- Local declarations of one body (groups), without limit checks. -/
def localGroups : P (Array (Nat × VT)) := vecOf (do let n ← u32; let t ← valType; pure (n, t))

/-- Operators of one body up to the matching final `end`, which must end exactly at `stop`. -/
def operators (stop : Nat) : P (Array Instr) := do
  let mut code := #[]
  let mut depth := 1
  let b ← read
  for _ in [0:b.size] do
    if depth = 0 then break
    if (← get) ≥ stop then fail "function body without end"
    let i ← instr
    match i with
    | .block _ | .loop _ | .if_ _ => depth := depth + 1
    | .end_ => depth := depth - 1
    | _ => pure ()
    code := code.push i
  if depth ≠ 0 then fail "function body without end"
  if (← get) ≠ stop then fail "operators remaining after end of function"
  pure code

end NearSpecV3.Wasm
