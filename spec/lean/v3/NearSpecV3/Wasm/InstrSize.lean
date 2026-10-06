import NearSpecV3.Wasm.FiniteWasm
/-!
# NEAR WASM (D3α): exact byte size of nearcore's instrumented module

`PrepareError::InstrumentedCodeTooLarge` fires when the output of `InstrumentContext::run`
(`prepare/instrument_v3.rs:278-480`) is longer than `max_instrumented_code_size` = 16 MiB
(`prepare_v3.rs:463-468`). This module computes that length exactly. It does not build the bytes:
it adds up, section by section, what `wasm_encoder` 0.236 emits:

* **Re-encoded with canonical LEB128:** types (plus 2 added), imports (3 added from `internal`),
  functions, globals (plus 2), exports (`"\0"`-prefixed by `prepare_v3`, plus `memory`,
  `remaining_gas`, `start`), elements (function indices + 3), and function locals (plus `i64` and
  `i32`).
* **Copied verbatim:** the table, data-count and data sections, and every operator except `call`,
  `ref.func`, `return` and the final `end`.
* **Injected:** the prologue, gas points (constant and linear form), and stack epilogues. Byte
  counts come from the instruction sequences in `instrument_v3.rs:178-231, 560-593, 788-880`.
  Wide-arithmetic ops (`i64.add128`, `i64.sub128`, `i64.mul_wide_u`) take 2 bytes each
  (`0xFC` + LEB).
-/
namespace NearSpecV3.Wasm.Size

def uleb : Nat → Nat
  | n => if n < 128 then 1 else 1 + uleb (n / 128)
decreasing_by omega

/-- signed LEB128 length of a non-negative value (all constants here are `< 2^63`) -/
def slebPos : Nat → Nat
  | n => if n < 64 then 1 else 1 + slebPos (n / 128)
decreasing_by omega

/-- signed LEB128 length of an i32/i64 bit pattern of width `w` -/
def slebW (w v : Nat) : Nat :=
  if v ≥ 2 ^ (w - 1) then
    -- negative: magnitude m = 2^w − v; sleb length of −m is that of m−1 in the positive scheme
    slebPos (2 ^ w - v - 1)
  else slebPos v

def name (s : String) : Nat := uleb s.utf8ByteSize + s.utf8ByteSize
def sect (payload : Nat) : Nat := 1 + uleb payload + payload
def vecSize (items : List Nat) : Nat := uleb items.length + items.foldl (· + ·) 0

def vt (_ : VT) : Nat := 1

def funcType (ft : FuncType) : Nat := 1 + vecSize (ft.params.toList.map vt) + vecSize (ft.results.toList.map vt)

def constE : ConstE → Nat
  | .i32 v => 1 + slebW 32 v.toNat + 1
  | .i64 v => 1 + slebW 64 v.toNat + 1
  | .refNull _ => 2 + 1
  | .refFunc f => 1 + uleb (f + 3) + 1
  | .globalGet g => 1 + uleb g + 1
  | .float b => 1 + b + 1

/-- `checked_{add,sub,mul}_i64`: wide op (2) + eqz + if + else + call f + unreachable + end -/
def checkedOp (f : Nat) : Nat := 2 + 1 + 2 + 1 + (1 + uleb f) + 1 + 1

/-- constant-fee point (`call_gas_instrumentation`, `linear = 0`) -/
def constPoint (G c : Nat) : Nat :=
  let gg := 1 + uleb G
  let ic := 1 + slebPos c
  gg + ic + 1 + 2 + ic + (1 + uleb 2) + 1 + 1 + gg + ic + 1 + gg + 1

/-- linear-fee point; `L` = index of the injected i64 local, `L+1` the injected i32 local -/
def linearPoint (G L : Nat) (fee : Fee) : Nat :=
  let gg := 1 + uleb G
  let lt := 1 + uleb L
  let lc := 1 + uleb (L + 1)
  lc + 1 + (1 + slebPos fee.l) + checkedOp 0 + 2 + (1 + slebPos fee.c) + 2 + checkedOp 0 +
    lt + gg + 1 + 2 + lt + (1 + uleb 2) + 1 + 1 + gg + lt + 1 + gg + 1 + lc

def point (G L : Nat) (_k : IK) (fee : Fee) : Nat :=
  if fee.l = 0 then constPoint G fee.c else linearPoint G L fee

/-- stack epilogue (`call_unstack_instrumentation`) -/
def unstack (G charge : Nat) : Nat :=
  let gs := 1 + uleb (G + 1)
  gs + 2 + (1 + slebPos charge) + 2 + checkedOp 1 + gs

/-- One instrumented code-section entry (size-prefixed). -/
def body (G : Nat) (ft : FuncType) (groups : Array (Nat × VT)) (code : Array Instr) (lens : Array Nat)
    (gas : Array (Option (IK × Fee))) (stackCharge prologueGas : Nat) : Nat :=
  let L := ft.params.size + groups.foldl (fun a (n, _) => a + n) 0
  let localsSz := uleb (groups.size + 2) + groups.foldl (fun a (n, _) => a + uleb n + 1) 0 + 2 + 2
  let gs := 1 + uleb (G + 1)
  let prologue := 2 + gs + 2 + (1 + slebPos stackCharge) + 2 + checkedOp 1 + gs +
    (if prologueGas = 0 then 0 else constPoint G prologueGas)
  let ops := Id.run do
    let mut tot := 0
    for i in [0:code.size] do
      match gas[i]! with
      | some (k, fee) => tot := tot + point G L k fee
      | none => pure ()
      let isLast := i + 1 = code.size
      tot := tot + match code[i]! with
        | .call f => 1 + uleb (f + 3)
        | .refFunc f => 1 + uleb (f + 3)
        | .ret => unstack G stackCharge + 1
        | .end_ => if isLast then 1 + unstack G stackCharge + 1 else lens[i]!
        | _ => lens[i]!
    tot
  let b := localsSz + prologue + ops
  uleb b + b

def elemSeg (e : Elem) (tableExplicit : Bool) (exprs : Bool) : Nat :=
  let items := if exprs then vecSize (e.init.toList.map constE)
    else vecSize (e.init.toList.map fun x => match x with
      | .refFunc f => uleb (f + 3)
      | _ => 1)
  match e.mode with
  | .passive => 1 + 1 + items
  | .declarative => 1 + 1 + items
  | .active t off =>
    if tableExplicit then 1 + uleb t + constE off + 1 + items
    else 1 + constE off + items

end NearSpecV3.Wasm.Size

namespace NearSpecV3.Wasm.Size

def elemSize (e : Elem) : Nat :=
  let funcsV := vecSize (e.init.toList.map fun x => match x with
    | .refFunc f => uleb (f + 3)
    | _ => 1)
  let exprsV := vecSize (e.init.toList.map constE)
  match e.flag, e.mode with
  | 0, .active _ off => 1 + constE off + funcsV
  | 1, _ => 1 + 1 + funcsV
  | 2, .active t off => 1 + uleb t + constE off + 1 + funcsV
  | 3, _ => 1 + 1 + funcsV
  | 4, .active _ off => 1 + constE off + exprsV
  | 5, _ => 1 + 1 + exprsV
  | 6, .active t off => 1 + uleb t + constE off + 1 + exprsV
  | _, _ => 1 + 1 + exprsV

def rawSize (m : Module) (id : Nat) : Option Nat := (m.rawSizes.find? (·.1 = id)).map (·.2)

/-- Exact length of `InstrumentContext::run`'s output, given the instrumented code-section entries
(`bodies`, each including its size prefix). -/
def moduleSize (m : Module) (bodies : Array Nat) (maxStackHeight : Nat) : Nat :=
  let hasCode := m.funcs.size > 0
  let addImports := m.imports.size > 0 ∨ hasCode
  let addGlobals := m.globals.size > 0 ∨ hasCode
  let T := m.types.size
  let G := m.globals.size
  let types :=
    let items := m.types.toList.map funcType ++ (if addImports then [3, 4] else [])
    if items.isEmpty then 0 else sect (vecSize items)
  let imports :=
    let internal := name "internal"
    let added := if addImports then
      [internal + name "finite_wasm_gas_exhausted" + 1 + uleb T,
       internal + name "finite_wasm_stack_exhausted" + 1 + uleb T,
       internal + name "finite_wasm_gas" + 1 + uleb (T + 1)] else []
    let items := added ++ m.imports.toList.map (fun i => name i.module + name i.name + 1 + uleb i.idx)
    if items.isEmpty then 0 else sect (vecSize items)
  let funcs := if m.funcTypes.isEmpty then 0 else sect (vecSize (m.funcTypes.toList.map uleb))
  let table := match rawSize m 4 with | some n => sect n | none => 0
  let memory := sect 6
  let globals :=
    let items := m.globals.toList.map (fun g => 1 + 1 + constE g.init) ++
      (if addGlobals then [1 + 1 + (1 + slebPos 0 + 1), 1 + 1 + (1 + slebPos maxStackHeight + 1)] else [])
    if items.isEmpty then 0 else sect (vecSize items)
  let exports :=
    let orig := m.exports.toList.filterMap (fun (n, k, i) =>
      if k = 2 then none
      else some (uleb (n.utf8ByteSize + 1) + n.utf8ByteSize + 1 + 1 + uleb (if k = 0 then i + 3 else i)))
    let items := orig ++ [name "memory" + 1 + 1] ++
      (if addGlobals then [name "remaining_gas" + 1 + uleb G] else []) ++
      (match m.start with | some s => [name "start" + 1 + uleb (s + 3)] | none => [])
    sect (vecSize items)
  let elems := if m.elems.isEmpty then 0 else sect (vecSize (m.elems.toList.map elemSize))
  let dcount := match rawSize m 12 with | some n => sect n | none => 0
  let code := if bodies.isEmpty then 0 else sect (uleb bodies.size + bodies.foldl (· + ·) 0)
  let data := match rawSize m 11 with | some n => sect n | none => 0
  8 + types + imports + funcs + table + memory + globals + exports + elems + dcount + code + data

end NearSpecV3.Wasm.Size
