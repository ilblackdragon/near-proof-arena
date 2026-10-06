/-!
# NEAR WASM (D3α): abstract syntax

Part of the D3 executable specification (`docs/requirements/D3_WASM_REQUIREMENTS.md` v0.2 §2.1).
Target: what nearcore 2.13.4 accepts at PV86 (`docs/research/near-wasm-boundary.md` B4): WebAssembly
MVP + mutable globals + sign-extension + saturating float→int + reference types + bulk memory, one
memory, at most one table, no multi-value. **`externref` is rejected**: finite-wasm 0.6.1 passes
`gc_types = false` (`features.rs:102`), and wasmparser 0.228 then admits only `funcref`
(`validator.rs:286-290`). `VT.externref` exists only so the decoder can name what it rejects. Floats are **out of domain in D3α**: the decoder parses
float types/opcodes (`VT.f32/.f64`, `Instr.float`) only so that `InD3α` can recognise and reject them.

Function bodies are *flat* operator arrays (as wasmparser/finite-wasm see them): NEAR's gas
instrumentation is defined on operator positions, and the interpreter's `pc` indexes this array.
-/
namespace NearSpecV3.Wasm

inductive VT where
  | i32 | i64 | f32 | f64 | funcref | externref
  deriving DecidableEq, Repr, Inhabited, BEq

/-- finite-wasm `SimpleMaxStackCfg::size_of_value` (nearcore `prepare/prepare_v3.rs:476-485`). -/
def VT.size : VT → Nat
  | .i32 | .f32 => 4
  | .i64 | .f64 => 8
  | .funcref | .externref => 8

def VT.isRef : VT → Bool
  | .funcref | .externref => true
  | _ => false

def VT.isFloat : VT → Bool
  | .f32 | .f64 => true
  | _ => false

structure FuncType where
  params : Array VT
  results : Array VT
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Block types: multi-value is disabled, so only `[] → []` or `[] → [t]`. -/
abbrev BT := Option VT

inductive Instr where
  -- control
  | unreachable | nop
  | block (bt : BT) | loop (bt : BT) | if_ (bt : BT) | else_ | end_
  | br (l : Nat) | brIf (l : Nat) | brTable (ls : Array Nat) (d : Nat) | ret
  | call (f : Nat) | callIndirect (ty : Nat) (tab : Nat)
  -- reference
  | refNull (t : VT) | refIsNull | refFunc (f : Nat)
  -- parametric
  | drop | select (t : Option VT)
  -- variable
  | localGet (i : Nat) | localSet (i : Nat) | localTee (i : Nat)
  | globalGet (i : Nat) | globalSet (i : Nat)
  -- table
  | tableGet (t : Nat) | tableSet (t : Nat) | tableSize (t : Nat) | tableGrow (t : Nat)
  | tableFill (t : Nat) | tableCopy (dst src : Nat) | tableInit (e t : Nat) | elemDrop (e : Nat)
  -- memory: `op` is the opcode byte (0x28‥0x35 loads, 0x36‥0x3E stores; integer only)
  | load (op : Nat) (align off : Nat) | store (op : Nat) (align off : Nat)
  | memSize | memGrow | memCopy | memFill | memInit (d : Nat) | dataDrop (d : Nat)
  -- numeric (integer)
  | i32Const (v : UInt32) | i64Const (v : UInt64)
  /-- every integer numeric operator without immediates, by opcode byte:
  0x45‥0x5A (test/rel), 0x67‥0x8A (un/bin), 0xA7 (wrap), 0xAC/0xAD (extend), 0xC0‥0xC4 (sign-ext) -/
  | num (op : Nat)
  /-- any float operator (opcode byte, or `0xFC00 + k` for `trunc_sat`): out of domain in D3α -/
  | float (op : Nat)
  deriving Repr, Inhabited

structure Import where
  module : String
  name : String
  /-- `0` func (type index in `idx`), `1` table, `2` memory, `3` global, `4` tag -/
  kind : Nat
  idx : Nat
  deriving Repr, Inhabited

structure Limits where
  min : Nat
  max : Option Nat
  deriving Repr, Inhabited

structure TableType where
  elem : VT
  lim : Limits
  deriving Repr, Inhabited

/-- Constant expressions allowed at PV86 (no extended-const, no imported globals). -/
inductive ConstE where
  | i32 (v : UInt32) | i64 (v : UInt64) | refNull (t : VT) | refFunc (f : Nat) | globalGet (g : Nat)
  | float (bits : Nat)
  deriving Repr, Inhabited

structure Global where
  type : VT
  mutable : Bool
  init : ConstE
  deriving Repr, Inhabited

inductive SegMode where
  | passive | declarative | active (table : Nat) (offset : ConstE)
  deriving Repr, Inhabited

structure Elem where
  /-- binary encoding form 0‥7 (re-encoding preserves it, `wasm-encoder` `ElementSection::segment`) -/
  flag : Nat := 0
  type : VT
  mode : SegMode
  init : Array ConstE
  deriving Repr, Inhabited

structure Data where
  /-- `none` = passive, `some (mem, offset)` = active -/
  active : Option (Nat × ConstE)
  bytes : ByteArray
  deriving Inhabited

structure Func where
  type : Nat
  /-- declared locals, run-length groups as in the binary (count, type) -/
  localGroups : Array (Nat × VT)
  code : Array Instr
  /-- byte size of the code-section entry (for `max_function_body_size`) -/
  bodySize : Nat
  /-- original encoded length of each operator (instrumentation copies most operators verbatim) -/
  opLens : Array Nat := #[]
  deriving Inhabited

structure Module where
  types : Array FuncType := #[]
  imports : Array Import := #[]
  funcTypes : Array Nat := #[]
  tables : Array TableType := #[]
  memories : Array Limits := #[]
  globals : Array Global := #[]
  /-- `(name, kind, index)`; kind `0` func, `1` table, `2` memory, `3` global -/
  exports : Array (String × Nat × Nat) := #[]
  start : Option Nat := none
  elems : Array Elem := #[]
  dataCount : Option Nat := none
  funcs : Array Func := #[]
  datas : Array Data := #[]
  /-- payload sizes of the sections nearcore's instrumentation copies verbatim
  (table 4, data count 12, data 11), `instrument_v3.rs:344-359, 400-407, 422-433` -/
  rawSizes : Array (Nat × Nat) := #[]
  deriving Inhabited

def Func.locals (f : Func) : Array VT :=
  f.localGroups.foldl (fun acc (n, t) => acc ++ Array.replicate n t) #[]

end NearSpecV3.Wasm
