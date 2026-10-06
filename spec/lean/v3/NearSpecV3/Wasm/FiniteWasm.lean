import NearSpecV3.Wasm.Validate
/-!
# NEAR WASM (D3α): the finite-wasm 0.6.1 analyses used by nearcore's instrumentation

nearcore runs `finite_wasm_6::Analysis` with `SimpleMaxStackCfg` and `SimpleGasCostCfg`
(`prepare/prepare_v3.rs:418-546`) and bakes its results into the instrumented module
(`prepare/instrument_v3.rs`). These are *literal ports*, operator by operator, because NEAR's gas
and stack semantics are defined by them:

* `maxStack`: `finite-wasm/src/max_stack/{mod,instruction_visit}.rs`. This is a stack *simulation*,
  not the typed maximum. For example `call_indirect` does not pop its table-index operand
  (`instruction_visit.rs:362-364`), so the simulated height stays 4 bytes higher until the frame ends.
* `gasPoints`: `finite-wasm/src/gas/mod.rs` (visitor) and `gas/optimize.rs` (two merge passes).
-/
namespace NearSpecV3.Wasm

/-! ## Max operand stack (bytes) -/

structure MSFrame where
  height : Nat
  results : Array VT
  poly : Bool

structure MS where
  ops : Array Nat := #[]      -- operand sizes
  size : Nat := 0
  max : Nat := 0
  cur : MSFrame := ⟨0, #[], false⟩
  frames : List MSFrame := []

abbrev MSM := StateT MS (Except String)

def msPush (t : VT) : MSM Unit := modify fun s =>
  if s.cur.poly then s
  else
    let sz := s.size + t.size
    { s with ops := s.ops.push t.size, size := sz, max := Nat.max s.max sz }

def msPop : MSM Unit := do
  let s ← get
  if s.cur.poly then return
  match s.ops.back? with
  | some v => set { s with ops := s.ops.pop, size := s.size - v }
  | none => throw "finite-wasm: empty stack"

def msPopMany (n : Nat) : MSM Unit := do
  if n = 0 then return
  let s ← get
  if s.cur.poly then return
  if s.ops.size < n then throw "finite-wasm: empty stack"
  let keep := s.ops.size - n
  let dropped := (s.ops.extract keep s.ops.size).foldl (· + ·) 0
  set { s with ops := s.ops.extract 0 keep, size := s.size - dropped }

def msNewFrame (rs : Array VT) (shift : Nat) : MSM Unit := do
  let s ← get
  let h ← if s.cur.poly then pure s.ops.size
    else if s.ops.size < shift then throw "finite-wasm: empty stack" else pure (s.ops.size - shift)
  set { s with frames := s.cur :: s.frames, cur := ⟨h, rs, s.cur.poly⟩ }

/-- `end_frame`: restore the outer frame, then truncate to the inner frame's height (the pop uses
the *outer* frame's polymorphism flag, `max_stack/mod.rs:223-238`). -/
def msEndFrame : MSM (Option MSFrame) := do
  let s ← get
  match s.frames with
  | [] => pure none
  | f :: fs =>
    let inner := s.cur
    set { s with cur := f, frames := fs }
    let s ← get
    if s.ops.size < inner.height then throw "finite-wasm: truncated operand stack"
    msPopMany (s.ops.size - inner.height)
    pure (some inner)

def msPoly : MSM Unit := modify fun s => { s with cur := { s.cur with poly := true } }

def msInstr (c : Ctx) (locals : Array VT) : Instr → MSM Unit
  | .unreachable => msPoly
  | .nop => pure ()
  | .block bt | .loop bt => msNewFrame (btResults bt) 0
  | .if_ bt => do msPop; msNewFrame (btResults bt) 0
  | .else_ => do
    match ← msEndFrame with
    | some f => msNewFrame f.results 0
    | none => throw "finite-wasm: truncated frame stack"
  | .end_ => do
    match ← msEndFrame with
    | some f => for r in f.results do msPush r
    | none => pure ()
  | .br _ | .brTable _ _ | .ret => msPoly
  | .brIf _ => msPop
  | .call f => do
    match c.funcs[f]? with
    | some ft => msPopMany ft.params.size; for r in ft.results do msPush r
    | none => throw "finite-wasm: function index"
  | .callIndirect ty _ => do   -- NB: the table index operand is not popped
    match c.types[ty]? with
    | some ft => msPopMany ft.params.size; for r in ft.results do msPush r
    | none => throw "finite-wasm: type index"
  | .refNull _ | .refFunc _ => msPush .funcref   -- refs are 8 bytes either way
  | .refIsNull => do msPop; msPush .i32
  | .drop => msPop
  | .select _ => msPopMany 2
  | .localGet i => match locals[i]? with
    | some t => msPush t
    | none => throw "finite-wasm: local index"
  | .localSet _ => msPop
  | .localTee _ => pure ()
  | .globalGet g => match c.globals[g]? with
    | some (t, _) => msPush t
    | none => throw "finite-wasm: global index"
  | .globalSet _ => msPop
  | .tableGet _ => do msPop; msPush .funcref
  | .tableSet _ => msPopMany 2
  | .tableSize _ => msPush .i32
  | .tableGrow _ => do msPopMany 2; msPush .i32
  | .tableFill _ | .tableCopy _ _ | .tableInit _ _ => msPopMany 3
  | .elemDrop _ | .dataDrop _ => pure ()
  | .load op _ _ => do msPop; msPush (loadResult op)
  | .store _ _ _ => msPopMany 2
  | .memSize => msPush .i32
  | .memGrow => pure ()
  | .memCopy | .memFill | .memInit _ => msPopMany 3
  | .i32Const _ => msPush .i32
  | .i64Const _ => msPush .i64
  | .num op =>
    let (ps, rs) := numSig op
    -- unop: no-op; binop: pop 1; testop/relop/cvtop: pop all, push result
    if ps.size = 1 ∧ rs = ps then pure ()
    else if ps.size = 2 ∧ rs.size = 1 ∧ rs[0]! = ps[0]! then msPop
    else do msPopMany ps.size; for r in rs do msPush r
  | .float _ => throw "float (out of domain)"

/-- finite-wasm's `function_operand_stack_sizes` entry for one body. -/
def maxStack (c : Ctx) (locals : Array VT) (code : Array Instr) : Except String Nat := do
  let act : MSM Unit := for i in code do msInstr c locals i
  let (_, s) ← act.run {}
  pure s.max

/-! ## Gas analysis -/

inductive IK where
  | pure | unreach | pre | post | between | linear
  deriving DecidableEq, Repr, Inhabited

/-- `a + b·count`; `count` is the top operand of a bulk/grow operator. -/
structure Fee where
  c : Nat
  l : Nat
  deriving DecidableEq, Repr, Inhabited

def Fee.zero : Fee := ⟨0, 0⟩
def Fee.const (c : Nat) : Fee := ⟨c, 0⟩
def Fee.add (a b : Fee) : Fee := ⟨a.c + b.c, a.l + b.l⟩

structure GasCfg where
  regular : Nat
  linearBase : Nat
  linearUnit : Nat

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
  stack : List GF := []
  sched : Option (IK × Fee) := none
  off : Nat := 0

def gBefore (k : IK) (f : Fee) : StateM GS Unit := modify fun s =>
  { s with pts := s.pts.push ⟨s.off, if s.cur.poly then .unreach else k, f⟩ }

def gAfter (k : IK) (f : Fee) : StateM GS Unit := modify fun s => { s with sched := some (k, f) }
def gPure (f : Fee) : StateM GS Unit := gBefore .pure f
def gSide (f : Fee) : StateM GS Unit := do gBefore .pre f; gAfter .post Fee.zero
def gLinear (f : Fee) : StateM GS Unit := do gBefore .linear f; gAfter .post Fee.zero

def gNewFrame (k : BTK) : StateM GS Unit := modify fun s =>
  { s with stack := s.cur :: s.stack, cur := ⟨s.cur.poly, k⟩ }

def gEndFrame : StateM GS Unit := modify fun s =>
  match s.stack with
  | f :: rest => { s with cur := f, stack := rest }
  | [] => s

def gPoly : StateM GS Unit := modify fun s => { s with cur := { s.cur with poly := true } }

def adjustKind (s : GS) (k : BTK) : GS × BTK :=
  match k with
  | .forward | .untaken => (s, .forward)
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
    | none => s

/-- Operators that finite-wasm classifies as `binop_partial` (may trap): integer div/rem. -/
def partialNum (op : Nat) : Bool := (0x6D ≤ op && op ≤ 0x70) || (0x7F ≤ op && op ≤ 0x82)

def gInstr (g : GasCfg) : Instr → StateM GS Unit
  | .unreachable => do gBefore .pre (.const g.regular); gAfter .unreach Fee.zero; gPoly
  | .loop _ => do
    let pre := (← get).pts.size
    gBefore .pure Fee.zero
    let post := (← get).pts.size
    gAfter .pure (.const g.regular)
    gNewFrame (.loop pre post)
  | .end_ => do
    match (← get).cur.kind with
    | .forward => gSide Fee.zero
    | _ => gPure Fee.zero
    gEndFrame
  | .if_ _ => do gSide (.const g.regular); gNewFrame .forward
  | .else_ => do gEndFrame; gNewFrame .forward; gSide Fee.zero
  | .block _ => do gPure Fee.zero; gNewFrame .untaken
  | .br l => do gSide (.const g.regular); gAdjust l; gPoly
  | .brIf l => do gSide (.const g.regular); gAdjust l
  | .brTable ls d => do
    gSide (.const g.regular)
    for l in ls do gAdjust l
    gAdjust d
    gPoly
  | .ret => do gSide (.const g.regular); gAdjust (← get).stack.length; gPoly
  | .memGrow | .memCopy | .memFill | .memInit _
  | .tableGrow _ | .tableFill _ | .tableCopy _ _ | .tableInit _ _ => gLinear ⟨g.linearBase, g.linearUnit⟩
  | .load .. | .store .. | .call _ | .callIndirect .. | .tableGet _ | .tableSet _ =>
    gSide (.const g.regular)
  | .num op => if partialNum op then gSide (.const g.regular) else gPure (.const g.regular)
  | _ => gPure (.const g.regular)

def mergeSame : IK → IK → Option IK
  | .unreach, _ => some .unreach
  | _, .unreach => some .unreach
  | .linear, _ => none          -- `unreachable!()` in finite-wasm
  | _, .linear => some .linear
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

/-- `blockLevel = false` is an ablation (instruction-level metering); nearcore is `true`. -/
def optimize (pts : Array Pt) (blockLevel : Bool := true) : Array Pt :=
  let p1 := optimizeWith pts fun a b =>
    if a.off = b.off then (mergeSame a.k b.k).map fun k => ⟨a.off, k, a.fee.add b.fee⟩ else none
  if !blockLevel then p1 else
  optimizeWith p1 fun a b =>
    (mergeAcross a.k b.k).map fun k => ⟨Nat.min a.off b.off, k, a.fee.add b.fee⟩

/-- Emitted instrumentation points of one body as `pc ↦ (kind, fee)`: kind ≠ Unreachable and
fee ≠ 0 (`instrument_v3.rs:609-620, 800-830`). -/
def gasTable (g : GasCfg) (code : Array Instr) (blockLevel : Bool := true) :
    Array (Option (IK × Fee)) := Id.run do
  let act : StateM GS Unit := do
    for i in [0:code.size] do
      modify fun s => match s.sched with
        | some (k, f) => { s with pts := s.pts.push ⟨i, k, f⟩, sched := none, off := i }
        | none => { s with off := i }
      gInstr g code[i]!
  let (_, s) := act.run {}
  let pts := optimize s.pts blockLevel
  let mut tbl : Array (Option (IK × Fee)) := Array.replicate code.size none
  for p in pts do
    if p.k ≠ .unreach ∧ p.fee ≠ Fee.zero ∧ p.off < code.size then
      tbl := tbl.set! p.off (some (p.k, p.fee))
  tbl

end NearSpecV3.Wasm
