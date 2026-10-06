import NearSpecV3.Wasm.Prepare
import NearSpecV3.Wasm.Numerics
/-!
# NEAR WASM (D3α): execution under nearcore's PV86 runtime

A small-step machine over the flat operator arrays of `Prepared`. Everything NEAR-specific
follows `docs/research/near-wasm-boundary.md` §§2–5:

* **Gas.** The instrumented module's `remaining_gas` global (`g`) is decremented at finite-wasm
  points. When `charge > g`, `finite_wasm_gas(charge)` fails in `GasCounter::burn_gas`. Wasmtime call
  hooks synchronise `g` with the host counter: `CallingHost`/`ReturningFromWasm` burn `remaining − g`,
  and `CallingWasm`/`ReturningFromHost` set `g := remaining` (`wasmtime_runner/mod.rs:1042-1072`).
  `ReturningFromWasm` also fires on a trap (wasmtime `func.rs:1481`).
* **Stack budget.** Entry subtracts `stackCharge` from 262,144; exhaustion is
  `HostError(MemoryAccessViolation)` (`instrument_v3.rs:576-585`, `logic.rs:290-292`).
* **Memory.** `(memory 1024 2048)` whatever the contract declares, stored as 64 KiB pages that share
  one zero page until first written.
* **Traps** are named as nearcore's `FunctionCallError::WasmTrap` variants (`mod.rs:385-394`):
  table out of bounds is reported as `MemoryOutOfBounds`.

Totality: `run` is structurally recursive on an explicit step budget `fuel`. A run that exhausts the
fuel reports `unmodeled` and never a guessed outcome.
-/
namespace NearSpecV3.Wasm

def maxGasBurnt : Nat := 1000000000000000
def maxLengthReturnedData : Nat := 4194304
def costBase : Nat := 264768111
def costReadMemoryBase : Nat := 2609863200
def costReadMemoryByte : Nat := 3801333
def costContractLoadingBase : Nat := 35445963
def costContractLoadingBytes : Nat := 1089295
def u64Bound : Nat := 2 ^ 64
def pageSize : Nat := 65536
def maxTableElementsStore : Nat := 10000

inductive Val where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  | ref (r : Option Nat)
  deriving Repr, Inhabited

def Val.default : VT → Val
  | .i64 => .i64 0
  | .funcref | .externref => .ref none
  | _ => .i32 0

structure Gas where
  burnt : Nat
  prepaid : Nat
  g : Nat
  deriving Inhabited

def Gas.remaining (gs : Gas) : Nat := gs.prepaid - gs.burnt

def errGasExceeded : String := "HostError(GasExceeded)"
def errGasLimitExceeded : String := "HostError(GasLimitExceeded)"
def errIntOverflow : String := "HostError(IntegerOverflow)"
def errMAV : String := "HostError(MemoryAccessViolation)"
def trapStr (t : String) : String := s!"WasmTrap({t})"
def trapMem : String := trapStr "MemoryOutOfBounds"

/-- `GasCounter::burn_gas` / `process_gas_limit` (no promises yet: `used = burnt`). -/
def burn (gs : Gas) (x : Nat) : Gas × Option String :=
  let nb := gs.burnt + x
  if nb ≥ u64Bound then (gs, some errIntOverflow)
  else if nb ≤ Nat.min maxGasBurnt gs.prepaid then ({ gs with burnt := nb }, none)
  else
    ({ gs with burnt := Nat.min nb (Nat.min gs.prepaid maxGasBurnt) },
     some (if nb > maxGasBurnt then errGasLimitExceeded else errGasExceeded))

def payPer (gs : Gas) (cost n : Nat) : Gas × Option String :=
  if cost * n ≥ u64Bound then (gs, some errIntOverflow) else burn gs (cost * n)

structure Label where
  target : Nat
  arity : Nat
  height : Nat
  isLoop : Bool
  deriving Inhabited

structure Frame where
  fn : Nat              -- index into `Prepared.funcs`
  pc : Nat
  locals : Array Val
  labels : List Label
  base : Nat
  deriving Inhabited

structure St where
  stack : Array Val := #[]
  frames : List Frame := []
  pages : Array ByteArray
  globals : Array Val
  table : Array (Option Nat)
  tableMax : Nat
  elems : Array (Array (Option Nat))
  datas : Array ByteArray
  stackRem : Nat
  gas : Gas
  ret : Option ByteArray := none

inductive Res where
  | cont (s : St)
  | fin (s : St)
  | abort (s : St) (err : String)
  | unmodeled (why : String)

/-! ## Memory -/

def zeroPage : ByteArray := ⟨Array.replicate pageSize 0⟩

def memBytes (s : St) : Nat := s.pages.size * pageSize

def readByte (s : St) (a : Nat) : UInt8 :=
  match s.pages[a / pageSize]? with
  | some p => p.get! (a % pageSize)
  | none => 0

def writeByte (s : St) (a : Nat) (v : UInt8) : St :=
  { s with pages := s.pages.modify (a / pageSize) (fun p => p.set! (a % pageSize) v) }

def readLE (s : St) (a w : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:w] do
    v := v + (readByte s (a + i)).toNat * 256 ^ i
  v

def writeLE (s : St) (a w v : Nat) : St := Id.run do
  let mut s := s
  for i in [0:w] do
    s := writeByte s (a + i) (UInt8.ofNat ((v / 256 ^ i) % 256))
  s

def readBytes (s : St) (a n : Nat) : ByteArray := Id.run do
  let mut d := ByteArray.empty
  for i in [0:n] do d := d.push (readByte s (a + i))
  d

def writeBytes (s : St) (a : Nat) (d : ByteArray) : St := Id.run do
  let mut s := s
  for i in [0:d.size] do s := writeByte s (a + i) d[i]!
  s

/-! ## Stack helpers -/

def popV (s : St) : Val × St := (s.stack.back?.getD (.i32 0), { s with stack := s.stack.pop })

def popN (s : St) : Nat × St :=
  match popV s with
  | (.i32 v, s') => (v.toNat, s')
  | (.i64 v, s') => (v.toNat, s')
  | (.ref _, s') => (0, s')

def popRef (s : St) : Option Nat × St :=
  match popV s with
  | (.ref r, s') => (r, s')
  | (_, s') => (none, s')

def pushV (s : St) (v : Val) : St := { s with stack := s.stack.push v }
def pushI32 (s : St) (v : Nat) : St := pushV s (.i32 (UInt32.ofNat v))
def pushI64 (s : St) (v : Nat) : St := pushV s (.i64 (UInt64.ofNat v))

def setFrame (s : St) (f : Frame) : St :=
  match s.frames with
  | _ :: fs => { s with frames := f :: fs }
  | [] => s

/-! ## Gas hooks -/

/-- `CallingHost` / `ReturningFromWasm`. A failure here would be a `LinkError` (`mod.rs:369-420`),
impossible while `prepaid ≤ max_gas_burnt` (requirement H5); it is reported as unmodeled. -/
def sync (s : St) : Except String St :=
  let burned := s.gas.remaining - s.gas.g
  if burned = 0 then .ok s
  else match burn s.gas burned with
    | (gs, none) => .ok { s with gas := gs }
    | (_, some _) => .error "gas hook failure (LinkError path, H5)"

/-- One instrumentation point; `count` is the top operand for linear fees. -/
def charge (s : St) (fee : Fee) (count : Nat) : Res :=
  let amt := count * fee.l + fee.c
  if amt ≥ u64Bound then
    -- 128-bit overflow check → finite_wasm_gas_exhausted: burn all remaining, IntegerOverflow
    match sync s with
    | .error e => .unmodeled e
    | .ok s =>
      match burn s.gas s.gas.remaining with
      | (gs, none) => .abort { s with gas := gs } errIntOverflow
      | (gs, some e) => .abort { s with gas := gs } e
  else if amt > s.gas.g then
    match sync s with
    | .error e => .unmodeled e
    | .ok s =>
      match burn s.gas amt with
      | (gs, some e) => .abort { s with gas := gs } e
      | (gs, none) => .unmodeled s!"finite_wasm_gas({amt}) did not fail ({gs.burnt})"
  else .cont { s with gas := { s.gas with g := s.gas.g - amt } }

/-! ## Calls -/

def enter (p : Prepared) (s : St) (fi : Nat) : Res :=
  let nImp := p.m.imports.size
  match p.funcs[fi - nImp]? with
  | none => .unmodeled "bad function index"
  | some pf =>
    if s.stackRem < pf.stackCharge then
      match sync s with
      | .error e => .unmodeled e
      | .ok s => .abort s errMAV
    else
      let s := { s with stackRem := s.stackRem - pf.stackCharge }
      match charge s (Fee.const pf.prologueGas) 0 with
      | .cont s =>
        let np := pf.type.params.size
        let base := s.stack.size - np
        let args := s.stack.extract base s.stack.size
        let fr : Frame := { fn := fi - nImp, pc := 0, locals := args ++ pf.locals.map Val.default,
                            labels := [{ target := pf.code.size, arity := pf.type.results.size,
                                         height := base, isLoop := false }],
                            base := base }
        .cont { s with stack := s.stack.extract 0 base, frames := fr :: s.frames }
      | r => r

def doReturn (p : Prepared) (s : St) : Res :=
  match s.frames with
  | [] => .fin s
  | f :: fs =>
    let pf := p.funcs[f.fn]!
    let ar := pf.type.results.size
    let vals := s.stack.extract (s.stack.size - ar) s.stack.size
    let s := { s with stack := s.stack.extract 0 f.base ++ vals, frames := fs,
                      stackRem := s.stackRem + pf.stackCharge }
    if fs.isEmpty then .fin s else .cont s

def doBr (p : Prepared) (s : St) (f : Frame) (l : Nat) : Res :=
  if l + 1 ≥ f.labels.length then doReturn p s
  else
    let lab := f.labels[l]!
    let vals := s.stack.extract (s.stack.size - lab.arity) s.stack.size
    let s := { s with stack := s.stack.extract 0 lab.height ++ vals }
    let labels := if lab.isLoop then f.labels.drop l else f.labels.drop (l + 1)
    .cont (setFrame s { f with pc := lab.target, labels := labels })

/-! ## Host functions (checkpoint 2 subset: `value_return`, `panic`, `gas`; the rest: checkpoint 3) -/

def hostValueReturn (s : St) (len ptr : Nat) : Res :=
  let fail (gs : Gas) (e : String) : Res := .abort { s with gas := gs } e
  match burn s.gas costBase with
  | (gs, some e) => fail gs e
  | (gs, none) =>
    if len = u64Bound - 1 then fail gs s!"HostError(InvalidRegisterId \{ register_id: {ptr} })"
    else
      match burn gs costReadMemoryBase with
      | (gs, some e) => fail gs e
      | (gs, none) =>
        match payPer gs costReadMemoryByte len with
        | (gs, some e) => fail gs e
        | (gs, none) =>
          if ptr + len ≥ u64Bound ∨ ptr + len > memBytes s then fail gs errMAV
          else if len > maxLengthReturnedData then
            fail gs s!"HostError(ReturnedValueLengthExceeded \{ length: {len}, limit: {maxLengthReturnedData} })"
          else .cont { s with gas := gs, ret := some (readBytes s ptr len) }

def callHost (cfg : NearCfg) (s : St) (name : String) : Res :=
  match sync s with
  | .error e => .unmodeled e
  | .ok s =>
    let r : Res := match name with
      | "panic" =>
        match burn s.gas costBase with
        | (gs, some e) => .abort { s with gas := gs } e
        | (gs, none) => .abort { s with gas := gs }
            "HostError(GuestPanic { panic_msg: \"explicit guest panic\" })"
      | "value_return" =>
        let (ptr, s) := popN s
        let (len, s) := popN s
        hostValueReturn s len ptr
      | "gas" =>   -- gas_seen_from_wasm: opcodes × regular_op_cost (logic.rs:1963-1968, 1982-1984)
        let (n, s) := popN s
        match burn s.gas (n * cfg.regularOpCost) with
        | (gs, none) => .cont { s with gas := gs }
        | (gs, some e) => .abort { s with gas := gs } e
      | n => .unmodeled s!"host function {n} (checkpoint 3)"
    match r with
    | .cont s => .cont { s with gas := { s.gas with g := s.gas.remaining } }
    | r => r

def callFunc (cfg : NearCfg) (p : Prepared) (s : St) (fi : Nat) : Res :=
  if h : fi < p.m.imports.size then callHost cfg s p.m.imports[fi].name else enter p s fi

/-! ## Bulk operations (bulk-memory proposal: bounds are checked before any write) -/

def memCopy (s : St) (d src n : Nat) : Res :=
  if src + n > memBytes s ∨ d + n > memBytes s then .abort s trapMem
  else .cont (writeBytes s d (readBytes s src n))

def memFill (s : St) (d v n : Nat) : Res :=
  if d + n > memBytes s then .abort s trapMem
  else Id.run do
    let mut s := s
    for i in [0:n] do s := writeByte s (d + i) (UInt8.ofNat v)
    return .cont s

def memInit (s : St) (seg d src n : Nat) : Res :=
  let data := s.datas[seg]?.getD ByteArray.empty
  if src + n > data.size ∨ d + n > memBytes s then .abort s trapMem
  else .cont (writeBytes s d (data.extract src (src + n)))

def tableInit (s : St) (seg d src n : Nat) : Res :=
  let es := s.elems[seg]?.getD #[]
  if src + n > es.size ∨ d + n > s.table.size then .abort s trapMem
  else Id.run do
    let mut t := s.table
    for i in [0:n] do t := t.set! (d + i) es[src + i]!
    return .cont { s with table := t }

/-! ## One instruction -/

def loadSpec (op : Nat) : Nat × Bool × Bool :=   -- (bytes, signed, is64)
  match op with
  | 0x28 => (4, false, false) | 0x29 => (8, false, true)
  | 0x2C => (1, true, false) | 0x2D => (1, false, false)
  | 0x2E => (2, true, false) | 0x2F => (2, false, false)
  | 0x30 => (1, true, true) | 0x31 => (1, false, true)
  | 0x32 => (2, true, true) | 0x33 => (2, false, true)
  | 0x34 => (4, true, true) | _ => (4, false, true)

def storeWidth (op : Nat) : Nat :=
  match op with
  | 0x36 => 4 | 0x37 => 8 | 0x3A => 1 | 0x3B => 2 | 0x3C => 1 | 0x3D => 2 | _ => 4

def execNum (s : St) (op : Nat) : Except String St := do
  let un (w : Nat) (f : Nat → Nat) : St :=
    let (a, s) := popN s
    if w = 32 then pushI32 s (f a) else pushI64 s (f a)
  if op = 0x45 then return un 32 (fun a => Num.b2 (a = 0))
  if op = 0x50 then
    let (a, s) := popN s
    return pushI32 s (Num.b2 (a = 0))
  if (0x46 ≤ op ∧ op ≤ 0x4F) ∨ (0x51 ≤ op ∧ op ≤ 0x5A) then
    let (w, k) := if op ≤ 0x4F then (32, op - 0x46) else (64, op - 0x51)
    let (b, s) := popN s
    let (a, s) := popN s
    return pushI32 s (Num.b2 (Num.relop w k a b))
  if 0x67 ≤ op ∧ op ≤ 0x69 then return un 32 (Num.unop 32 (op - 0x67))
  if 0x79 ≤ op ∧ op ≤ 0x7B then return un 64 (Num.unop 64 (op - 0x79))
  if (0x6A ≤ op ∧ op ≤ 0x78) ∨ (0x7C ≤ op ∧ op ≤ 0x8A) then
    let (w, k) := if op ≤ 0x78 then (32, op - 0x6A) else (64, op - 0x7C)
    let (b, s) := popN s
    let (a, s) := popN s
    match Num.binop w k a b with
    | some r => return (if w = 32 then pushI32 s r else pushI64 s r)
    | none => throw (trapStr "IllegalArithmetic")
  match op with
  | 0xA7 => let (a, s) := popN s; return pushI32 s (a % 2 ^ 32)
  | 0xAC => let (a, s) := popN s; return pushI64 s (Num.extendS 64 32 a)
  | 0xAD => let (a, s) := popN s; return pushI64 s a
  | 0xC0 => return un 32 (Num.extendS 32 8)
  | 0xC1 => return un 32 (Num.extendS 32 16)
  | 0xC2 => return un 64 (Num.extendS 64 8)
  | 0xC3 => return un 64 (Num.extendS 64 16)
  | 0xC4 => return un 64 (Num.extendS 64 32)
  | _ => throw "unmodeled numeric opcode"

def exec (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr) : Res :=
  let next (s : St) : Res := .cont (setFrame s { f with pc := f.pc + 1 })
  let advance (s : St) : St := setFrame s { f with pc := f.pc + 1 }
  match i with
  | .unreachable => .abort s (trapStr "Unreachable")
  | .nop => next s
  | .block bt =>
    let lab : Label := { target := pf.endOf[f.pc]! + 1, arity := (btResults bt).size,
                         height := s.stack.size, isLoop := false }
    .cont (setFrame s { f with pc := f.pc + 1, labels := lab :: f.labels })
  | .loop _ =>
    let lab : Label := { target := f.pc + 1, arity := 0, height := s.stack.size, isLoop := true }
    .cont (setFrame s { f with pc := f.pc + 1, labels := lab :: f.labels })
  | .if_ bt =>
    let (c, s) := popN s
    let e := pf.endOf[f.pc]!
    let el := pf.elseOf[f.pc]!
    let lab : Label := { target := e + 1, arity := (btResults bt).size,
                         height := s.stack.size, isLoop := false }
    if c ≠ 0 then .cont (setFrame s { f with pc := f.pc + 1, labels := lab :: f.labels })
    else if el ≠ e then .cont (setFrame s { f with pc := el + 1, labels := lab :: f.labels })
    else .cont (setFrame s { f with pc := e + 1 })
  | .else_ =>
    match f.labels with
    | lab :: ls => .cont (setFrame s { f with pc := lab.target, labels := ls })
    | [] => .unmodeled "else without label"
  | .end_ =>
    match f.labels with
    | [_] | [] => doReturn p s
    | _ :: ls => .cont (setFrame s { f with pc := f.pc + 1, labels := ls })
  | .br l => doBr p s f l
  | .brIf l => let (c, s) := popN s; if c ≠ 0 then doBr p s f l else next s
  | .brTable ls d => let (c, s) := popN s; doBr p s f (ls[c]?.getD d)
  | .ret => doReturn p s
  | .call fi => callFunc cfg p (advance s) fi
  | .callIndirect ty _ =>
    let (i, s) := popN s
    match s.table[i]? with
    | none => .abort s trapMem   -- TableOutOfBounds ↦ MemoryOutOfBounds (mod.rs:388)
    | some none => .abort s (trapStr "IndirectCallToNull")
    | some (some fi) =>
      if p.ctx.funcs[fi]! != p.m.types[ty]! then .abort s (trapStr "IncorrectCallIndirectSignature")
      else callFunc cfg p (advance s) fi
  | .refNull _ => next (pushV s (.ref none))
  | .refIsNull => let (r, s) := popRef s; next (pushI32 s (Num.b2 r.isNone))
  | .refFunc x => next (pushV s (.ref (some x)))
  | .drop => next (popV s).2
  | .select _ =>
    let (c, s) := popN s
    let (v2, s) := popV s
    let (v1, s) := popV s
    next (pushV s (if c ≠ 0 then v1 else v2))
  | .localGet x => next (pushV s (f.locals[x]?.getD (.i32 0)))
  | .localSet x =>
    let (v, s) := popV s
    .cont (setFrame s { f with pc := f.pc + 1, locals := f.locals.set! x v })
  | .localTee x =>
    let v := s.stack.back?.getD (.i32 0)
    .cont (setFrame s { f with pc := f.pc + 1, locals := f.locals.set! x v })
  | .globalGet x => next (pushV s (s.globals[x]?.getD (.i32 0)))
  | .globalSet x => let (v, s) := popV s; next { s with globals := s.globals.set! x v }
  | .tableGet _ =>
    let (i, s) := popN s
    match s.table[i]? with
    | some r => next (pushV s (.ref r))
    | none => .abort s trapMem
  | .tableSet _ =>
    let (r, s) := popRef s
    let (i, s) := popN s
    if i < s.table.size then next { s with table := s.table.set! i r } else .abort s trapMem
  | .tableSize _ => next (pushI32 s s.table.size)
  | .tableGrow _ =>
    let (n, s) := popN s
    let (r, s) := popRef s
    let sz := s.table.size
    if sz + n ≤ Nat.min s.tableMax maxTableElementsStore then
      next (pushI32 { s with table := s.table ++ Array.replicate n r } sz)
    else next (pushI32 s (2 ^ 32 - 1))
  | .tableFill _ =>
    let (n, s) := popN s
    let (r, s) := popRef s
    let (d, s) := popN s
    if d + n > s.table.size then .abort s trapMem
    else Id.run do
      let mut t := s.table
      for k in [0:n] do t := t.set! (d + k) r
      return next { s with table := t }
  | .tableCopy _ _ =>
    let (n, s) := popN s
    let (src, s) := popN s
    let (d, s) := popN s
    if src + n > s.table.size ∨ d + n > s.table.size then .abort s trapMem
    else
      let chunk := s.table.extract src (src + n)
      Id.run do
        let mut t := s.table
        for k in [0:n] do t := t.set! (d + k) chunk[k]!
        return next { s with table := t }
  | .tableInit e _ =>
    let (n, s) := popN s
    let (src, s) := popN s
    let (d, s) := popN s
    match tableInit s e d src n with
    | .cont s => next s
    | r => r
  | .elemDrop e => next { s with elems := s.elems.set! e #[] }
  | .load op _ off =>
    let (a, s) := popN s
    let (w, sgn, is64) := loadSpec op
    let ea := a + off
    if ea + w > memBytes s then .abort s trapMem
    else
      let v := readLE s ea w
      let v := if sgn then Num.extendS (if is64 then 64 else 32) (8 * w) v else v
      next (if is64 then pushI64 s v else pushI32 s v)
  | .store op _ off =>
    let (v, s) := popN s
    let (a, s) := popN s
    let w := storeWidth op
    let ea := a + off
    if ea + w > memBytes s then .abort s trapMem
    else next (writeLE s ea w (v % 256 ^ w))
  | .memSize => next (pushI32 s s.pages.size)
  | .memGrow =>
    let (n, s) := popN s
    let old := s.pages.size
    if old + n ≤ cfg.maxMemoryPages then
      next (pushI32 { s with pages := s.pages ++ Array.replicate n zeroPage } old)
    else next (pushI32 s (2 ^ 32 - 1))
  | .memCopy =>
    let (n, s) := popN s
    let (src, s) := popN s
    let (d, s) := popN s
    match memCopy s d src n with
    | .cont s => next s
    | r => r
  | .memFill =>
    let (n, s) := popN s
    let (v, s) := popN s
    let (d, s) := popN s
    match memFill s d v n with
    | .cont s => next s
    | r => r
  | .memInit seg =>
    let (n, s) := popN s
    let (src, s) := popN s
    let (d, s) := popN s
    match memInit s seg d src n with
    | .cont s => next s
    | r => r
  | .dataDrop d => next { s with datas := s.datas.set! d ByteArray.empty }
  | .i32Const v => next (pushV s (.i32 v))
  | .i64Const v => next (pushV s (.i64 v))
  | .num op =>
    match execNum s op with
    | .ok s => next s
    | .error e => if e.startsWith "WasmTrap" then .abort s e else .unmodeled e
  | .float _ => .unmodeled "float (out of domain)"

def topCount (s : St) : Nat :=
  match s.stack.back? with
  | some (.i32 v) => v.toNat
  | some (.i64 v) => v.toNat
  | _ => 0

def step (cfg : NearCfg) (p : Prepared) (s : St) : Res :=
  match s.frames with
  | [] => .fin s
  | f :: _ =>
    match p.funcs[f.fn]? with
    | none => .unmodeled "bad frame"
    | some pf =>
      match pf.code[f.pc]? with
      | none => .unmodeled "pc out of range"
      | some i =>
        match pf.gas[f.pc]! with
        | none => exec cfg p s f pf i
        | some (k, fee) =>
          match charge s fee (if k = .linear then topCount s else 0) with
          | .cont s => exec cfg p s f pf i
          | r => r

def run (cfg : NearCfg) (p : Prepared) : Nat → St → Res
  | 0, _ => .unmodeled "fuel exhausted"
  | n + 1, s =>
    match step cfg p s with
    | .cont s => run cfg p n s
    | r => r

/-! ## Instantiation (Wasm 2.0 §4.5.4, as wasmtime performs it) -/

def evalConst (gs : Array Val) : ConstE → Val
  | .i32 v => .i32 v
  | .i64 v => .i64 v
  | .refNull _ => .ref none
  | .refFunc f => .ref (some f)
  | .globalGet g => gs[g]?.getD (.i32 0)
  | .float _ => .i32 0

def constNat (gs : Array Val) (e : ConstE) : Nat :=
  match evalConst gs e with
  | .i32 v => v.toNat
  | .i64 v => v.toNat
  | .ref _ => 0

def constRef (gs : Array Val) (e : ConstE) : Option Nat :=
  match evalConst gs e with
  | .ref r => r
  | _ => none

/-- Returns the initial state, or the instantiation trap. -/
def instantiate (cfg : NearCfg) (p : Prepared) (gas : Gas) : Except String St := do
  let m := p.m
  let gs := m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[]
  let (tsize, tmax) := match m.tables[0]? with
    | some t => (t.lim.min, t.lim.max.getD (2 ^ 32 - 1))
    | none => (0, 0)
  let elems := m.elems.map (fun e => e.init.map (constRef gs))
  let mut s : St := {
    pages := Array.replicate cfg.initialMemoryPages zeroPage, globals := gs,
    table := Array.replicate tsize none, tableMax := tmax, elems := elems,
    datas := m.datas.map (·.bytes), stackRem := cfg.maxStackHeight, gas := gas }
  for k in [0:m.elems.size] do
    match m.elems[k]!.mode with
    | .active _ off =>
      let n := elems[k]!.size
      match tableInit s k (constNat gs off) 0 n with
      | .cont s' => s := { s' with elems := s'.elems.set! k #[] }
      | _ => throw trapMem
    | .declarative => s := { s with elems := s.elems.set! k #[] }
    | .passive => pure ()
  for k in [0:m.datas.size] do
    match m.datas[k]!.active with
    | some (_, off) =>
      match memInit s k (constNat gs off) 0 m.datas[k]!.bytes.size with
      | .cont s' => s := { s' with datas := s'.datas.set! k ByteArray.empty }
      | _ => throw trapMem
    | none => pure ()
  return s

/-! ## Top level: the observable `VMOutcome` of one function call -/

def hex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList
  b.foldl (fun acc x => acc.push (d[x.toNat / 16]!) |>.push (d[x.toNat % 16]!)) ""

/-- Run one wasm entry (`start` or the method) from host context: `CallingWasm` (`g := remaining`),
execute, `ReturningFromWasm` (sync, also after a trap). -/
def callEntry (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    Except String (St × Option String) :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  let r := match enter p s fi with
    | .cont s => run cfg p fuel s
    | r => r
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

/-- One line in the harness format (`oracle/wasm-d3/src/main.rs`):
`ok <burnt> <used> <ret|->`, `abort <burnt> <used> <error>` (the zero-gas no-op outcome of a
missing method prints as `abort 0 0 …`, as the harness does),
or `out-of-domain …` / `unmodeled …` (never silently equal to nearcore). -/
def outcome (cfg : NearCfg) (code : ByteArray) (method : String) (prepaid fuel : Nat)
    (blockLevel : Bool := true) : String :=
  if method.isEmpty then "abort 0 0 MethodResolveError(MethodEmptyName)" else
  match prepare cfg code blockLevel with
  | .outOfDomain why => s!"out-of-domain {why}"
  | .unmodeled why => s!"unmodeled {why}"
  | .prepErr v _ => s!"abort 0 0 CompilationError(PrepareError({v}))"
  | .ok p =>
    let gs : Gas := { burnt := 0, prepaid := prepaid, g := 0 }
    let loaded := match payPer gs costContractLoadingBytes code.size with
      | (gs, none) => burn gs costContractLoadingBase
      | r => r
    match loaded with
    | (gs, some _) => s!"abort {gs.burnt} {gs.burnt} {errGasExceeded}"
    | (gs, none) =>
      match link p with
      | .linkError msg => s!"abort {gs.burnt} {gs.burnt} LinkError \{ msg: \"{msg}\" }"
      | .ok =>
        match resolve p method with
        | .notFound => "abort 0 0 MethodResolveError(MethodNotFound)"
        | .invalidSignature => "abort 0 0 MethodResolveError(MethodInvalidSignature)"
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => s!"abort {gs.burnt} {gs.burnt} {e}"
          | .ok s =>
            let afterStart : Except String (St × Option String) :=
              match p.m.start with
              | some st => callEntry cfg p fuel s st
              | none => .ok (s, none)
            match afterStart with
            | .error why => s!"unmodeled {why}"
            | .ok (s, some e) => s!"abort {s.gas.burnt} {s.gas.burnt} {e}"
            | .ok (s, none) =>
              match callEntry cfg p fuel s mi with
              | .error why => s!"unmodeled {why}"
              | .ok (s, some e) => s!"abort {s.gas.burnt} {s.gas.burnt} {e}"
              | .ok (s, none) =>
                let ret := match s.ret with
                  | some d => hex d
                  | none => "-"
                s!"ok {s.gas.burnt} {s.gas.burnt} {ret}"

end NearSpecV3.Wasm

namespace NearSpecV3.Wasm

/-- Diagnostic for the difftest: the exact instrumented size, or the preparation error. -/
def preparedSizeLine (cfg : NearCfg) (code : ByteArray) : String :=
  match prepare cfg code with
  | .ok p => toString (instrumentedSize cfg p.m p.funcs)
  | .prepErr v _ => s!"prepare-error {v}"
  | .outOfDomain w => s!"out-of-domain {w}"
  | .unmodeled w => s!"unmodeled {w}"

end NearSpecV3.Wasm
