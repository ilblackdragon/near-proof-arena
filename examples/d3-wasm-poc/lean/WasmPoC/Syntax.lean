/-!
# Abstract syntax of the PoC subset

The subset (one memory, i32 values, i64 only as host-call arguments) is listed
in `../README.md`. Instructions are kept *flat* (a function body is an array
of operators including `else`/`end`), exactly as wasmparser/finite-wasm see
them: NEAR's gas instrumentation is defined on operator offsets, and the
interpreter's program counter is an index into this array.
-/
namespace WasmPoC

inductive VT where
  | i32 | i64
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Byte size used by finite-wasm's `SimpleMaxStackCfg::size_of_value`
(nearcore `prepare_v3.rs:476-485`). -/
def VT.size : VT → Nat
  | .i32 => 4
  | .i64 => 8

inductive Val where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  deriving Repr, Inhabited

inductive Instr where
  | unreachable | nop
  | block (bt : Option VT) | loop (bt : Option VT) | if_ (bt : Option VT)
  | else_ | end_
  | br (l : Nat) | brIf (l : Nat) | brTable (ls : Array Nat) (d : Nat) | ret
  | call (f : Nat)
  | drop | select
  | localGet (i : Nat) | localSet (i : Nat) | localTee (i : Nat)
  /-- `w = 4`: `i32.load`; `w = 1`: `i32.load8_u`. -/
  | load (w : Nat) (align off : Nat)
  /-- `w = 4`: `i32.store`; `w = 1`: `i32.store8`. -/
  | store (w : Nat) (align off : Nat)
  | memSize | memGrow
  | i32Const (v : UInt32) | i64Const (v : UInt64)
  | i32Eqz
  | i32Rel (op : Nat) | i32Un (op : Nat) | i32Bin (op : Nat)
  | i64ExtendU
  deriving Repr, Inhabited

structure FuncType where
  params : Array VT
  results : Array VT
  deriving Repr, Inhabited, BEq

structure Import where
  module : String
  name : String
  type : Nat
  deriving Repr, Inhabited

structure Func where
  type : Nat
  locals : Array VT
  code : Array Instr
  deriving Repr, Inhabited

structure Module where
  types : Array FuncType := #[]
  imports : Array Import := #[]
  funcTypes : Array Nat := #[]
  funcs : Array Func := #[]
  memory : Option (Nat × Option Nat) := none
  /-- `(name, kind, index)` -/
  exports : Array (String × Nat × Nat) := #[]
  deriving Repr, Inhabited

end WasmPoC
