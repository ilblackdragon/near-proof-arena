import NearSpecV3.Wasm.Host
/-!
# NEAR WASM (D3α): instruction execution, instantiation, and the observable outcome

See `Machine` for the execution model (gas hooks, stack budget, memory) and `Host` for host functions.
-/
namespace NearSpecV3.Wasm

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

/-- A host call: `CallingHost` sync, the host function, `ReturningFromHost` (`g := remaining`). -/
def callHost (s : St) (name : String) : Res :=
  match sync s with
  | .error e => .unmodeled e
  | .ok s =>
    match hostCall name with
    | none => .unmodeled s!"host function {name} not modelled in D3α"
    | some h =>
      match h.run s with
      | .ok _ s => .cont { s with gas := { s.gas with g := s.gas.remaining } }
      | .error e s => if e.startsWith "unmodeled" then .unmodeled e else .abort s e

def callFunc (_cfg : NearCfg) (p : Prepared) (s : St) (fi : Nat) : Res :=
  if h : fi < p.m.imports.size then callHost s p.m.imports[fi].name else enter p s fi

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

/-- Host functions outside D3α (curve arithmetic: D3γ/δ). Importing one puts the contract out of
domain. `ed25519_verify` is D3α but waits for D1's Ed25519 (unmodeled until then). -/
def curveHosts : List String := ["alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check",
  "bls12381_p1_sum", "bls12381_p2_sum", "bls12381_g1_multiexp", "bls12381_g2_multiexp",
  "bls12381_map_fp_to_g1", "bls12381_map_fp2_to_g2", "bls12381_pairing_check",
  "bls12381_p1_decompress", "bls12381_p2_decompress", "ecrecover", "p256_verify"]

/-- The rest of `VMOutcome` beyond status/gas/return (`|| compute … || logs … || actions … || trie …`). -/
def fullExtra (s : St) : String :=
  let trie := (s.trie.toList.map (fun (k, v) => s!"{hex k}={hex v}")).toArray.qsort (· < ·)
  s!" || compute {s.gas.computeUsage} || logs {",".intercalate (s.logs.toList.map hex)} || actions {";".intercalate (s.actions.toList.map (·.text))} || trie {",".intercalate trie.toList}"

/-- One line in the harness format (`oracle/wasm-d3/src/main.rs`):
`ok <burnt> <used> <ret|-|receiptN> <balance>`, `abort <burnt> <used> <error>` (the zero-gas no-op
outcome of a missing method prints as `abort 0 0 …`, as the harness does), or `out-of-domain …` /
`unmodeled …` (never silently equal to nearcore). `full` appends `fullExtra` (harness mode `full`). -/
def outcome (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) : String :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : String := s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas))
  if method.isEmpty then nop "MethodResolveError(MethodEmptyName)" else
  match prepare cfg code blockLevel with
  | .outOfDomain why => s!"out-of-domain {why}"
  | .unmodeled why => s!"unmodeled {why}"
  | .prepErr v _ => nop s!"CompilationError(PrepareError({v}))"
  | .compileErr k _ =>
    nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })"
  | .ok p =>
    if p.m.imports.any (fun i => curveHosts.contains i.name) then "out-of-domain curve host function" else
    let gs : Gas := Gas.init ctx.prepaidGas
    let loaded := match payPer gs C.contractLoadingBytes code.size with
      | (gs, none) => payBase gs C.contractLoadingBase
      | r => r
    match loaded with
    | (gs, some _) => s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ ext (emptySt gs)
    | (gs, none) =>
      match link p with
      | .linkError msg => s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ ext (emptySt gs)
      | .ok =>
        match resolve p method with
        | .notFound => nop "MethodResolveError(MethodNotFound)"
        | .invalidSignature => nop "MethodResolveError(MethodInvalidSignature)"
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => s!"abort {gs.burnt} {gs.used} {e}" ++ ext (emptySt gs)
          | .ok s =>
            let s := { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                              storageUsage := ctx.storageUsage }
            let afterStart : Except String (St × Option String) :=
              match p.m.start with
              | some st => callEntry cfg p fuel s st
              | none => .ok (s, none)
            match afterStart with
            | .error why => s!"unmodeled {why}"
            | .ok (s, some e) => s!"abort {s.gas.burnt} {s.gas.used} {e}" ++ ext s
            | .ok (s, none) =>
              match callEntry cfg p fuel s mi with
              | .error why => s!"unmodeled {why}"
              | .ok (s, some e) => s!"abort {s.gas.burnt} {s.gas.used} {e}" ++ ext s
              | .ok (s, none) =>
                let ret := match s.ret with
                  | some (.inl d) => hex d
                  | some (.inr r) => s!"receipt{r}"
                  | none => "-"
                s!"ok {s.gas.burnt} {s.gas.used} {ret} {s.balance}" ++ ext s

end NearSpecV3.Wasm

namespace NearSpecV3.Wasm

/-- Diagnostic for the difftest: the exact instrumented size, or the preparation error. -/
def preparedSizeLine (cfg : NearCfg) (code : ByteArray) : String :=
  match prepare cfg code with
  | .ok p => toString (instrumentedSize cfg p.m p.funcs)
  | .prepErr v _ => s!"prepare-error {v}"
  | .compileErr _ sz => toString sz   -- prepare succeeds; Wasmtime compilation then fails
  | .outOfDomain w => s!"out-of-domain {w}"
  | .unmodeled w => s!"unmodeled {w}"

end NearSpecV3.Wasm
