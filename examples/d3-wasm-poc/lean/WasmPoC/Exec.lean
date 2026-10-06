import WasmPoC.Prepare
import Std.Data.HashMap
/-!
# Execution of a prepared module under NEAR's PV86 runtime

Small-step interpreter over the flat operator arrays of `Prepared`. The gas
model is *nearcore's*, not an idealised per-instruction one:

* a wasm-side counter `g` (the exported `remaining_gas` global of the
  instrumented module) is decremented at the finite-wasm instrumentation points
  (`instrument_v3.rs:800-880`); when a point's charge exceeds `g` the
  instrumentation calls `internal.finite_wasm_gas(charge)`
  (`wasmtime_runner/logic.rs:182-184`), which fails in `GasCounter::burn_gas`;
* `g` is synchronised with the host `GasCounter` by Wasmtime call hooks
  (`wasmtime_runner/mod.rs:1042-1072`): `CallingHost`/`ReturningFromWasm` burn
  `remaining − g`, `ReturningFromHost`/`CallingWasm` reset `g := remaining`.
  `ReturningFromWasm` also fires when wasm traps (wasmtime `func.rs:1481`);
* `GasCounter::burn_gas`/`process_gas_limit` (`logic/gas_counter.rs:147-201`)
  clamp `burnt` to `min(prepaid, max_gas_burnt)` and report
  `GasLimitExceeded` iff the attempted total exceeds `max_gas_burnt`.

Termination: every function here is structurally recursive; the driver takes
an explicit step budget (`fuel`) and reports `fuel exhausted` (counted as a
disagreement by the difftest) if gas did not stop execution first.
-/
namespace WasmPoC

def maxGasBurnt : Nat := 1000000000000000          -- limit_config.max_gas_burnt (83.yaml)
def maxLengthReturnedData : Nat := 4194304
-- ext_costs (PV85 snapshot = PV86)
def costBase : Nat := 264768111
def costReadMemoryBase : Nat := 2609863200
def costReadMemoryByte : Nat := 3801333
def costContractLoadingBase : Nat := 35445963
def costContractLoadingBytes : Nat := 1089295
def u64Bound : Nat := 2 ^ 64

structure Gas where
  burnt : Nat
  prepaid : Nat
  /-- the instrumented module's `remaining_gas` global -/
  g : Nat
  deriving Inhabited

def Gas.remaining (gs : Gas) : Nat := gs.prepaid - gs.burnt

def errGasExceeded : String := "HostError(GasExceeded)"
def errGasLimitExceeded : String := "HostError(GasLimitExceeded)"
def errIntOverflow : String := "HostError(IntegerOverflow)"
def errMAV : String := "HostError(MemoryAccessViolation)"

/-- `GasCounter::burn_gas` (no promises in the PoC, so `used = burnt`). -/
def burn (gs : Gas) (x : Nat) : Gas × Option String :=
  let nb := gs.burnt + x
  if nb ≥ u64Bound then (gs, some errIntOverflow)
  else if nb ≤ min maxGasBurnt gs.prepaid then ({ gs with burnt := nb }, none)
  else
    ({ gs with burnt := min nb (min gs.prepaid maxGasBurnt) },
     some (if nb > maxGasBurnt then errGasLimitExceeded else errGasExceeded))

/-- `pay_per`: `checked_mul` then `burn_gas`. -/
def payPer (gs : Gas) (cost n : Nat) : Gas × Option String :=
  if cost * n ≥ u64Bound then (gs, some errIntOverflow) else burn gs (cost * n)

structure Label where
  target : Nat
  arity : Nat
  height : Nat
  isLoop : Bool
  deriving Inhabited

structure Frame where
  fn : Nat
  pc : Nat
  locals : Array Val
  labels : List Label      -- head = innermost; the last one is the function label
  base : Nat

structure St where
  stack : Array Val := #[]
  frames : List Frame := []
  mem : Std.HashMap Nat UInt8 := {}
  pages : Nat := initialMemoryPages
  stackRem : Nat := maxStackHeight
  gas : Gas
  ret : Option ByteArray := none

inductive Res where
  | cont (s : St)
  | fin (s : St)
  | abort (s : St) (err : String)
  /-- a path the PoC deliberately does not model (difftest: disagreement) -/
  | unmodeled (why : String)

/-! ## i32 numerics (WebAssembly 1.0 §4.3.2) -/

def toS (x : UInt32) : Int := if x.toNat ≥ 2 ^ 31 then (x.toNat : Int) - 2 ^ 32 else x.toNat
def ofI (i : Int) : UInt32 := UInt32.ofNat (i % (2 ^ 32 : Int)).toNat
def b2 (b : Bool) : UInt32 := if b then 1 else 0

def clz (x : UInt32) : UInt32 := Id.run do
  let mut n := 0
  for i in [0:32] do
    if (x.toNat / 2 ^ (31 - i)) % 2 = 1 then return UInt32.ofNat n
    n := n + 1
  return 32

def ctz (x : UInt32) : UInt32 := Id.run do
  let mut n := 0
  for i in [0:32] do
    if (x.toNat / 2 ^ i) % 2 = 1 then return UInt32.ofNat n
    n := n + 1
  return 32

def popcnt (x : UInt32) : UInt32 := Id.run do
  let mut n := 0
  for i in [0:32] do
    if (x.toNat / 2 ^ i) % 2 = 1 then n := n + 1
  return UInt32.ofNat n

def shl (a b : UInt32) : UInt32 := UInt32.ofNat (a.toNat * 2 ^ (b.toNat % 32))
def shrU (a b : UInt32) : UInt32 := UInt32.ofNat (a.toNat / 2 ^ (b.toNat % 32))
def shrS (a b : UInt32) : UInt32 := ofI (toS a / (2 ^ (b.toNat % 32) : Int))  -- Int `/` floors for positive divisors
def rotl (a b : UInt32) : UInt32 :=
  let k := b.toNat % 32
  UInt32.ofNat ((a.toNat * 2 ^ k) % 2 ^ 32 + a.toNat / 2 ^ (32 - k))
def rotr (a b : UInt32) : UInt32 := rotl a (UInt32.ofNat ((32 - b.toNat % 32) % 32))

def unop (op : Nat) (a : UInt32) : UInt32 :=
  match op with
  | 0x67 => clz a
  | 0x68 => ctz a
  | _ => popcnt a

def relop (op : Nat) (a b : UInt32) : UInt32 :=
  match op with
  | 0x46 => b2 (a == b)
  | 0x47 => b2 (a != b)
  | 0x48 => b2 (toS a < toS b)
  | 0x49 => b2 (a.toNat < b.toNat)
  | 0x4A => b2 (toS a > toS b)
  | 0x4B => b2 (a.toNat > b.toNat)
  | 0x4C => b2 (toS a ≤ toS b)
  | 0x4D => b2 (a.toNat ≤ b.toNat)
  | 0x4E => b2 (toS a ≥ toS b)
  | _ => b2 (a.toNat ≥ b.toNat)

/-- `none` = trap; nearcore maps wasmtime's IntegerDivisionByZero and
IntegerOverflow both to `WasmTrap::IllegalArithmetic` (`wasmtime_runner/mod.rs:391-392`). -/
def binop (op : Nat) (a b : UInt32) : Option UInt32 :=
  match op with
  | 0x6A => some (a + b)
  | 0x6B => some (a - b)
  | 0x6C => some (a * b)
  | 0x6D => if b = 0 then none else if toS a = -(2 ^ 31) ∧ toS b = -1 then none
            else some (ofI (Int.tdiv (toS a) (toS b)))
  | 0x6E => if b = 0 then none else some (UInt32.ofNat (a.toNat / b.toNat))
  | 0x6F => if b = 0 then none else some (ofI (Int.tmod (toS a) (toS b)))
  | 0x70 => if b = 0 then none else some (UInt32.ofNat (a.toNat % b.toNat))
  | 0x71 => some (a &&& b)
  | 0x72 => some (a ||| b)
  | 0x73 => some (a ^^^ b)
  | 0x74 => some (shl a b)
  | 0x75 => some (shrS a b)
  | 0x76 => some (shrU a b)
  | 0x77 => some (rotl a b)
  | _ => some (rotr a b)

/-! ## Machine helpers -/

def trapStr (t : String) : String := s!"WasmTrap({t})"

def memBytes (s : St) : Nat := s.pages * 65536

def readByte (s : St) (a : Nat) : UInt8 := s.mem.getD a 0

def readLE (s : St) (a w : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:w] do
    v := v + (readByte s (a + i)).toNat * 256 ^ i
  v

def writeLE (s : St) (a w v : Nat) : St := Id.run do
  let mut m := s.mem
  for i in [0:w] do
    m := m.insert (a + i) (UInt8.ofNat ((v / 256 ^ i) % 256))
  { s with mem := m }

def popV (s : St) : Val × St :=
  (s.stack.back?.getD (.i32 0), { s with stack := s.stack.pop })

def popI32 (s : St) : UInt32 × St :=
  match popV s with
  | (.i32 v, s') => (v, s')
  | (.i64 v, s') => (v.toUInt32, s')   -- excluded by validation

def popI64 (s : St) : UInt64 × St :=
  match popV s with
  | (.i64 v, s') => (v, s')
  | (.i32 v, s') => (v.toUInt64, s')

def pushV (s : St) (v : Val) : St := { s with stack := s.stack.push v }

def setFrame (s : St) (f : Frame) : St :=
  match s.frames with
  | _ :: fs => { s with frames := f :: fs }
  | [] => s

/-- Wasmtime `CallingHost` / `ReturningFromWasm` hook: burn `remaining − g`.
A failure here would surface as a `LinkError` (the hook's error is not wrapped
in `ErrorContainer`, `wasmtime_runner/mod.rs:1060,369-420`); it is impossible
while `prepaid ≤ max_gas_burnt` (true for every PV86 function call) and is not
modelled. -/
def sync (s : St) : Except String St :=
  let burned := s.gas.remaining - s.gas.g
  if burned = 0 then .ok s
  else match burn s.gas burned with
    | (gs, none) => .ok { s with gas := gs }
    | (_, some _) => .error "gas hook failure (LinkError path)"

/-- One instrumentation point (`call_gas_instrumentation`). `count` is the
operand of `memory.grow` for linear fees. -/
def charge (s : St) (fee : Fee) (count : Nat) : Res :=
  let amt := count * fee.l + fee.c
  if amt > s.gas.g then
    match sync s with
    | .error e => .unmodeled e
    | .ok s =>
      match burn s.gas amt with
      | (gs, some e) => .abort { s with gas := gs } e
      | (gs, none) => .unmodeled s!"finite_wasm_gas({amt}) did not fail ({gs.burnt})"
  else .cont { s with gas := { s.gas with g := s.gas.g - amt } }

/-- Enter defined function `fi` (absolute index), arguments on the stack. -/
def enter (p : Prepared) (s : St) (fi : Nat) : Res :=
  let pf := p.funcs[fi - p.hosts.size]!
  -- prologue (instrument_v3.rs:576-592): stack budget first, then frame gas
  if s.stackRem < pf.stackCharge then
    match sync s with   -- finite_wasm_stack_exhausted is a host call
    | .error e => .unmodeled e
    | .ok s => .abort s errMAV   -- logic.rs:290-292: stack exhaustion is MemoryAccessViolation
  else
    let s := { s with stackRem := s.stackRem - pf.stackCharge }
    match charge s (Fee.const pf.prologueGas) 0 with
    | .cont s =>
      let np := pf.type.params.size
      let base := s.stack.size - np
      let args := s.stack.extract base s.stack.size
      let zeros := pf.locals.map fun t => match t with
        | .i32 => Val.i32 0
        | .i64 => Val.i64 0
      let fr : Frame := { fn := fi - p.hosts.size, pc := 0, locals := args ++ zeros,
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

/-! ## Host functions (wasmtime_runner/logic.rs) -/

/-- `value_return` (logic.rs:4170-4220) with no output data receivers. -/
def hostValueReturn (s : St) (len ptr : Nat) : Res :=
  let fail (s : St) (gs : Gas) (e : String) : Res := .abort { s with gas := gs } e
  match burn s.gas costBase with
  | (gs, some e) => fail s gs e
  | (gs, none) =>
    if len = u64Bound - 1 then
      -- register path: no register was ever written (registers.get, vmstate.rs:137-150)
      fail s gs s!"HostError(InvalidRegisterId \{ register_id: {ptr} })"
    else
      match burn gs costReadMemoryBase with
      | (gs, some e) => fail s gs e
      | (gs, none) =>
        match payPer gs costReadMemoryByte len with
        | (gs, some e) => fail s gs e
        | (gs, none) =>
          if ptr + len ≥ u64Bound ∨ ptr + len > memBytes s then fail s gs errMAV
          else if len > maxLengthReturnedData then
            fail s gs s!"HostError(ReturnedValueLengthExceeded \{ length: {len}, limit: {maxLengthReturnedData} })"
          else
            let data := Id.run do
              let mut d := ByteArray.empty
              for i in [0:len] do d := d.push (readByte s (ptr + i))
              d
            .cont { s with gas := gs, ret := some data }

def callHost (s : St) (h : Host) : Res :=
  match sync s with
  | .error e => .unmodeled e
  | .ok s =>
    let r : Res := match h with
      | .panic =>
        match burn s.gas costBase with
        | (gs, some e) => .abort { s with gas := gs } e
        | (gs, none) => .abort { s with gas := gs }
            "HostError(GuestPanic { panic_msg: \"explicit guest panic\" })"
      | .valueReturn =>
        let (ptr, s) := popI64 s
        let (len, s) := popI64 s
        hostValueReturn s len.toNat ptr.toNat
    match r with
    | .cont s => .cont { s with gas := { s.gas with g := s.gas.remaining } }  -- ReturningFromHost
    | r => r

/-! ## One step -/

def exec (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr) : Res :=
  let next (s : St) : Res := .cont (setFrame s { f with pc := f.pc + 1 })
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
    let (c, s) := popI32 s
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
  | .brIf l =>
    let (c, s) := popI32 s
    if c ≠ 0 then doBr p s f l else next s
  | .brTable ls d =>
    let (c, s) := popI32 s
    doBr p s f (ls[c.toNat]?.getD d)
  | .ret => doReturn p s
  | .call fi =>
    let s := setFrame s { f with pc := f.pc + 1 }   -- return address
    if h : fi < p.hosts.size then callHost s p.hosts[fi]
    else enter p s fi
  | .drop => next (popV s).2
  | .select =>
    let (c, s) := popI32 s
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
  | .load w _ off =>
    let (a, s) := popI32 s
    let ea := a.toNat + off
    if ea + w > memBytes s then .abort s (trapStr "MemoryOutOfBounds")
    else next (pushV s (.i32 (UInt32.ofNat (readLE s ea w))))
  | .store w _ off =>
    let (v, s) := popI32 s
    let (a, s) := popI32 s
    let ea := a.toNat + off
    if ea + w > memBytes s then .abort s (trapStr "MemoryOutOfBounds")
    else next (writeLE s ea w (v.toNat % 256 ^ w))
  | .memSize => next (pushV s (.i32 (UInt32.ofNat s.pages)))
  | .memGrow =>
    let (n, s) := popI32 s
    if s.pages + n.toNat ≤ maxMemoryPages then
      next (pushV { s with pages := s.pages + n.toNat } (.i32 (UInt32.ofNat s.pages)))
    else next (pushV s (.i32 0xFFFFFFFF))
  | .i32Const v => next (pushV s (.i32 v))
  | .i64Const v => next (pushV s (.i64 v))
  | .i32Eqz => let (a, s) := popI32 s; next (pushV s (.i32 (b2 (a = 0))))
  | .i32Un op => let (a, s) := popI32 s; next (pushV s (.i32 (unop op a)))
  | .i32Rel op =>
    let (b, s) := popI32 s
    let (a, s) := popI32 s
    next (pushV s (.i32 (relop op a b)))
  | .i32Bin op =>
    let (b, s) := popI32 s
    let (a, s) := popI32 s
    match binop op a b with
    | some r => next (pushV s (.i32 r))
    | none => .abort s (trapStr "IllegalArithmetic")
  | .i64ExtendU => let (a, s) := popI32 s; next (pushV s (.i64 a.toUInt64))

def step (p : Prepared) (s : St) : Res :=
  match s.frames with
  | [] => .fin s
  | f :: _ =>
    let pf := p.funcs[f.fn]!
    match pf.code[f.pc]? with
    | none => .unmodeled "pc out of range"
    | some i =>
      -- instrumentation point placed before operator `pc`
      match pf.gas[f.pc]! with
      | none => exec p s f pf i
      | some (k, fee) =>
        let cnt := if k = .memGrow then (match s.stack.back? with
          | some (.i32 v) => v.toNat
          | _ => 0) else 0
        match charge s fee cnt with
        | .cont s => exec p s f pf i
        | r => r

def run (p : Prepared) : Nat → St → Res
  | 0, _ => .unmodeled "fuel exhausted"
  | n + 1, s =>
    match step p s with
    | .cont s => run p n s
    | r => r

/-! ## Top level: the observable `VMOutcome` -/

def hex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList
  b.foldl (fun acc x => acc.push (d[x.toNat / 16]!) |>.push (d[x.toNat % 16]!)) ""

/-- One line in the harness format (`oracle/wasm-d3/src/main.rs`). -/
def outcome (code : ByteArray) (prepaid : Nat) (fuel : Nat) (blockLevel : Bool := true) : String :=
  match prepare code blockLevel with
  | .unsupported why => s!"unsupported {why}"
  | .prepareError _ =>
    -- with fix_contract_loading_cost = false the loading fee is only charged
    -- after a successful compile (gas_counter.rs:235-270, wasmtime_runner/mod.rs:797-816)
    "abort 0 0 CompilationError(PrepareError(Deserialization))"
  | .ok p =>
    let gs : Gas := { burnt := 0, prepaid := prepaid, g := 0 }
    let loaded := match payPer gs costContractLoadingBytes code.size with
      | (gs, none) => burn gs costContractLoadingBase
      | r => r
    match loaded with
    | (gs, some _) => s!"abort {gs.burnt} {gs.burnt} {errGasExceeded}"
    | (gs, none) =>
      let s0 : St := { gas := { gs with g := gs.remaining } }   -- CallingWasm hook
      let r := match enter p s0 p.main with
        | .cont s => run p fuel s
        | r => r
      let finish (s : St) : Except String St := sync s     -- ReturningFromWasm hook
      match r with
      | .fin s =>
        match finish s with
        | .ok s =>
          let ret := match s.ret with
            | some d => hex d
            | none => "-"
          s!"ok {s.gas.burnt} {s.gas.burnt} {ret}"
        | .error e => s!"unmodeled {e}"
      | .abort s e =>
        match finish s with
        | .ok s => s!"abort {s.gas.burnt} {s.gas.burnt} {e}"
        | .error e => s!"unmodeled {e}"
      | .unmodeled why => s!"unmodeled {why}"
      | .cont _ => "unmodeled cont"

end WasmPoC
