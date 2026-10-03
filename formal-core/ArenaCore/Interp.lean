import ArenaCore.SHA256

/-!
# ArenaCore.Interp — the approved verifier interpreter (NPAI v1)

A tiny deterministic register VM.  This Lean definition **is** the semantics
of the judge-owned interpreter used by the "approved interpreter"
implementation-connection route: a candidate ships verifier *bytecode*; the
arena executes that exact bytecode (whose SHA-256 is pinned in the admission
statement) with a judge-owned Rust interpreter that is differentially tested
against `exec` below.  See `docs/INTERP_SPEC.md` for the normative
byte-level specification; this file and that document must agree.

Design points:

* 16 registers of 64-bit unsigned words (all arithmetic wraps mod 2^64).
* A byte-addressed memory of `memSize` bytes, initialised from the program's
  data segment and zero elsewhere.  Every access is bounds-checked; an
  out-of-bounds access *traps*.
* Three read-only input tapes: public artifacts, claim, proof.
* Two append-only output buffers (used by reduction programs, ignored for
  verifiers).
* A `SHA256` opcode.  The hash is a *parameter* of the semantics
  (`HashOracle σ`), so the same bytecode can be run against the real SHA-256
  (`shaOracle`, the deployed semantics) or against a lazily-sampled random
  oracle in the ROM security game (`ArenaCore.Security.ROM`).
* Fuel: every instruction has a cost `1 + len/64` (len = bytes touched by
  bulk instructions, 0 otherwise); execution with insufficient fuel stops
  with `outOfFuel`.  Fuel therefore bounds both running time and the number
  of hash-oracle queries.
* Outcomes: `accept`, `reject` (from `HALT`), `trap`, `outOfFuel`.  Only
  `accept` counts as acceptance.
-/

namespace ArenaCore
namespace Interp

/-- 2^64 -/
def wordMod : Nat := 18446744073709551616

/-! ## Syntax -/

/-- Input tapes. Encoded as 0 = public, 1 = claim, 2 = proof. -/
inductive TapeId where
  | pub
  | claim
  | proof
  deriving DecidableEq, Repr

/-- Binary register operations. -/
inductive BinOp where
  | add | sub | mul | and | or | xor | shl | shr | eq | ltu
  deriving DecidableEq, Repr

/-- Instructions.  Register operands are indices `< 16` (enforced by the
decoder); `imm` is an unsigned 32-bit immediate. -/
inductive Instr where
  | halt (a : Nat)
  | const (a : Nat) (imm : Nat)
  | mov (a b : Nat)
  | bin (op : BinOp) (a b c : Nat)
  | addi (a b : Nat) (imm : Nat)
  | jmp (t : Nat)
  | jz (a : Nat) (t : Nat)
  | jnz (a : Nat) (t : Nat)
  | tlen (a : Nat) (t : TapeId)
  | tload (a b : Nat) (t : TapeId)
  | tcopy (a b c : Nat) (t : TapeId)
  | ld8 (a b : Nat)
  | st8 (a b : Nat)
  | sha256 (a b c : Nat)
  | memeq (a b c d : Nat)
  | out (k : Nat) (a b : Nat)
  deriving DecidableEq, Repr

/-- A decoded program. -/
structure Program where
  memSize : Nat
  data : Bytes
  code : List Instr
  deriving DecidableEq, Repr

/-- The three input tapes. -/
structure Inputs where
  pub : Bytes
  claim : Bytes
  proof : Bytes

def Inputs.tape (i : Inputs) : TapeId → Bytes
  | .pub => i.pub
  | .claim => i.claim
  | .proof => i.proof

/-! ## Semantics -/

def BinOp.eval : BinOp → Nat → Nat → Nat
  | .add, x, y => (x + y) % wordMod
  | .sub, x, y => (x % wordMod + (wordMod - y % wordMod)) % wordMod
  | .mul, x, y => (x * y) % wordMod
  | .and, x, y => (x &&& y) % wordMod
  | .or, x, y => (x ||| y) % wordMod
  | .xor, x, y => (x ^^^ y) % wordMod
  | .shl, x, y => (x <<< (y % 64)) % wordMod
  | .shr, x, y => (x % wordMod) >>> (y % 64)
  | .eq, x, y => if x = y then 1 else 0
  | .ltu, x, y => if x < y then 1 else 0

/-- A (possibly stateful) hash oracle used by the `SHA256` opcode. -/
abbrev HashOracle (σ : Type) := σ → Bytes → Bytes × σ

/-- The deployed hash: real SHA-256, no state. -/
def shaOracle : HashOracle Unit := fun s m => (ArenaCore.sha256 m, s)

/-- Machine state. -/
structure State (σ : Type) where
  pc : Nat
  regs : Nat → Nat
  mem : Nat → UInt8
  fuel : Nat
  out0 : Bytes
  out1 : Bytes
  hs : σ

/-- Final outcomes. -/
inductive Outcome where
  | accept
  | reject
  | trap
  | outOfFuel
  deriving DecidableEq, Repr

/-- Result of a single step. -/
inductive StepResult (σ : Type) where
  | next (s : State σ)
  | done (o : Outcome) (s : State σ)

def setReg (r : Nat → Nat) (a v : Nat) : Nat → Nat :=
  fun j => if j = a then v else r j

/-- `len` bytes of memory starting at `p`. -/
def readMem (m : Nat → UInt8) (p len : Nat) : Bytes :=
  (List.range len).map fun i => m (p + i)

/-- Overwrite `len` bytes at `dst` with `src[0..len)` (`src` padded with 0). -/
def writeMem (m : Nat → UInt8) (dst len : Nat) (src : Bytes) : Nat → UInt8 :=
  fun j => if dst ≤ j ∧ j < dst + len then src.getD (j - dst) 0 else m j

/-- Cost of an instruction given the current registers. -/
def cost (regs : Nat → Nat) : Instr → Nat
  | .tcopy _ _ c _ => 1 + regs c / 64
  | .sha256 _ _ c => 1 + regs c / 64
  | .memeq _ _ _ d => 1 + regs d / 64
  | .out _ _ b => 1 + regs b / 64
  | _ => 1

/-- Execute one (already fetched and paid-for) instruction. -/
def exec1 {σ : Type} (p : Program) (inp : Inputs) (H : HashOracle σ) (s : State σ) :
    Instr → StepResult σ
  | .halt a => .done (if s.regs a = 0 then .reject else .accept) s
  | .const a imm => .next { s with pc := s.pc + 1, regs := setReg s.regs a (imm % wordMod) }
  | .mov a b => .next { s with pc := s.pc + 1, regs := setReg s.regs a (s.regs b) }
  | .bin op a b c =>
      .next { s with pc := s.pc + 1, regs := setReg s.regs a (op.eval (s.regs b) (s.regs c)) }
  | .addi a b imm =>
      .next { s with pc := s.pc + 1, regs := setReg s.regs a ((s.regs b + imm) % wordMod) }
  | .jmp t => .next { s with pc := t }
  | .jz a t => .next { s with pc := if s.regs a = 0 then t else s.pc + 1 }
  | .jnz a t => .next { s with pc := if s.regs a = 0 then s.pc + 1 else t }
  | .tlen a t =>
      .next { s with pc := s.pc + 1, regs := setReg s.regs a ((inp.tape t).length % wordMod) }
  | .tload a b t =>
      let tp := inp.tape t
      if s.regs b < tp.length then
        .next { s with pc := s.pc + 1, regs := setReg s.regs a (tp.getD (s.regs b) 0).toNat }
      else .done .trap s
  | .tcopy a b c t =>
      let tp := inp.tape t
      let dst := s.regs a
      let src := s.regs b
      let len := s.regs c
      if src + len ≤ tp.length ∧ dst + len ≤ p.memSize then
        .next { s with pc := s.pc + 1, mem := writeMem s.mem dst len (tp.drop src) }
      else .done .trap s
  | .ld8 a b =>
      if s.regs b < p.memSize then
        .next { s with pc := s.pc + 1, regs := setReg s.regs a (s.mem (s.regs b)).toNat }
      else .done .trap s
  | .st8 a b =>
      if s.regs a < p.memSize then
        .next { s with pc := s.pc + 1,
                       mem := writeMem s.mem (s.regs a) 1 [UInt8.ofNat (s.regs b % 256)] }
      else .done .trap s
  | .sha256 a b c =>
      let dst := s.regs a
      let src := s.regs b
      let len := s.regs c
      if src + len ≤ p.memSize ∧ dst + 32 ≤ p.memSize then
        let (d, hs') := H s.hs (readMem s.mem src len)
        .next { s with pc := s.pc + 1, mem := writeMem s.mem dst 32 d, hs := hs' }
      else .done .trap s
  | .memeq a b c d =>
      let x := s.regs b
      let y := s.regs c
      let len := s.regs d
      if x + len ≤ p.memSize ∧ y + len ≤ p.memSize then
        .next { s with pc := s.pc + 1,
                       regs := setReg s.regs a
                         (if readMem s.mem x len = readMem s.mem y len then 1 else 0) }
      else .done .trap s
  | .out k a b =>
      let x := s.regs a
      let len := s.regs b
      if x + len ≤ p.memSize then
        if k = 0 then .next { s with pc := s.pc + 1, out0 := s.out0 ++ readMem s.mem x len }
        else .next { s with pc := s.pc + 1, out1 := s.out1 ++ readMem s.mem x len }
      else .done .trap s

/-- One step: fetch (trap if `pc` is out of range), charge fuel, execute. -/
def step {σ : Type} (p : Program) (inp : Inputs) (H : HashOracle σ) (s : State σ) :
    StepResult σ :=
  match p.code[s.pc]? with
  | none => .done .trap s
  | some ins =>
    let c := cost s.regs ins
    if s.fuel < c then .done .outOfFuel s
    else exec1 p inp H { s with fuel := s.fuel - c } ins

/-- Iterate `step` at most `gas` times.  Every executed instruction costs at
least one unit of fuel, so with `gas = fuel + 1` the `gas = 0` branch is
never reached before fuel runs out; it returns `outOfFuel` for totality. -/
def exec {σ : Type} (p : Program) (inp : Inputs) (H : HashOracle σ) :
    Nat → State σ → Outcome × State σ
  | 0, s => (.outOfFuel, s)
  | gas + 1, s =>
    match step p inp H s with
    | .next s' => exec p inp H gas s'
    | .done o s' => (o, s')

/-- Initial state. -/
def init {σ : Type} (p : Program) (fuel : Nat) (hs : σ) : State σ :=
  { pc := 0, regs := fun _ => 0, mem := fun j => p.data.getD j 0, fuel := fuel,
    out0 := [], out1 := [], hs := hs }

/-- Maximum length of each input tape (2^32 bytes).  Larger inputs trap
before execution starts, so tape lengths and offsets never wrap. -/
def maxTapeLen : Nat := 4294967296

/-- Run with an arbitrary hash oracle starting in oracle state `hs`. -/
def runWith {σ : Type} (H : HashOracle σ) (hs : σ) (p : Program) (inp : Inputs) (fuel : Nat) :
    Outcome × State σ :=
  if inp.pub.length < maxTapeLen ∧ inp.claim.length < maxTapeLen ∧ inp.proof.length < maxTapeLen
  then exec p inp H (fuel + 1) (init p fuel hs)
  else (.trap, init p fuel hs)

/-- Deployed semantics (real SHA-256): full outcome and final state. -/
def runFull (p : Program) (inp : Inputs) (fuel : Nat) : Outcome × State Unit :=
  runWith shaOracle () p inp fuel

/-- Deployed semantics: `some true` = accept, `some false` = reject,
`none` = trap or out of fuel (the production wrapper treats `none` as an
error, which is never acceptance). -/
def run (p : Program) (inp : Inputs) (fuel : Nat) : Option Bool :=
  match (runFull p inp fuel).1 with
  | .accept => some true
  | .reject => some false
  | _ => none

/-- Output buffers of an accepting run (used for reduction programs). -/
def runOut (p : Program) (inp : Inputs) (fuel : Nat) : Option (Bytes × Bytes) :=
  match runFull p inp fuel with
  | (.accept, s) => some (s.out0, s.out1)
  | _ => none

/-! ## Binary encoding (NPAI v1) -/

def magic : Bytes := [0x4E, 0x50, 0x41, 0x49]  -- "NPAI"
def version : UInt8 := 1

/-- Decoder limits. -/
def maxMemSize : Nat := 16777216   -- 2^24
def maxCodeLen : Nat := 65536      -- 2^16
def numRegs : Nat := 16

def TapeId.toNat : TapeId → Nat
  | .pub => 0
  | .claim => 1
  | .proof => 2

def TapeId.ofNat? : Nat → Option TapeId
  | 0 => some .pub
  | 1 => some .claim
  | 2 => some .proof
  | _ => none

def BinOp.opcode : BinOp → Nat
  | .add => 0x03 | .sub => 0x04 | .mul => 0x05 | .and => 0x06 | .or => 0x07
  | .xor => 0x08 | .shl => 0x09 | .shr => 0x0A | .eq => 0x0B | .ltu => 0x0C

def BinOp.ofOpcode? : Nat → Option BinOp
  | 0x03 => some .add | 0x04 => some .sub | 0x05 => some .mul | 0x06 => some .and
  | 0x07 => some .or | 0x08 => some .xor | 0x09 => some .shl | 0x0A => some .shr
  | 0x0B => some .eq | 0x0C => some .ltu | _ => none

/-- Raw fields of an instruction word: `[op, a, b, c, imm (u32 LE)]`. -/
def Instr.fields : Instr → Nat × Nat × Nat × Nat × Nat
  | .halt a => (0x00, a, 0, 0, 0)
  | .const a imm => (0x01, a, 0, 0, imm)
  | .mov a b => (0x02, a, b, 0, 0)
  | .bin op a b c => (op.opcode, a, b, c, 0)
  | .addi a b imm => (0x0D, a, b, 0, imm)
  | .jmp t => (0x10, 0, 0, 0, t)
  | .jz a t => (0x11, a, 0, 0, t)
  | .jnz a t => (0x12, a, 0, 0, t)
  | .tlen a t => (0x20, a, 0, 0, t.toNat)
  | .tload a b t => (0x21, a, b, 0, t.toNat)
  | .tcopy a b c t => (0x22, a, b, c, t.toNat)
  | .ld8 a b => (0x30, a, b, 0, 0)
  | .st8 a b => (0x31, a, b, 0, 0)
  | .sha256 a b c => (0x40, a, b, c, 0)
  | .memeq a b c d => (0x41, a, b, c, d)
  | .out k a b => (0x50, a, b, 0, k)

def Instr.encode (i : Instr) : Bytes :=
  let (op, a, b, c, imm) := i.fields
  [UInt8.ofNat op, UInt8.ofNat a, UInt8.ofNat b, UInt8.ofNat c] ++ Bytes.leN 4 imm

/-- Decode one instruction from its fields; unused fields must be zero and
register operands `< 16` (canonical encoding). -/
def Instr.decode (op a b c imm : Nat) : Option Instr :=
  let r (x : Nat) : Bool := x < numRegs
  match op with
  | 0x00 => if r a && b == 0 && c == 0 && imm == 0 then some (.halt a) else none
  | 0x01 => if r a && b == 0 && c == 0 then some (.const a imm) else none
  | 0x02 => if r a && r b && c == 0 && imm == 0 then some (.mov a b) else none
  | 0x0D => if r a && r b && c == 0 then some (.addi a b imm) else none
  | 0x10 => if a == 0 && b == 0 && c == 0 then some (.jmp imm) else none
  | 0x11 => if r a && b == 0 && c == 0 then some (.jz a imm) else none
  | 0x12 => if r a && b == 0 && c == 0 then some (.jnz a imm) else none
  | 0x20 => if r a && b == 0 && c == 0 then (TapeId.ofNat? imm).map (.tlen a) else none
  | 0x21 => if r a && r b && c == 0 then (TapeId.ofNat? imm).map (.tload a b) else none
  | 0x22 => if r a && r b && r c then (TapeId.ofNat? imm).map (.tcopy a b c) else none
  | 0x30 => if r a && r b && c == 0 && imm == 0 then some (.ld8 a b) else none
  | 0x31 => if r a && r b && c == 0 && imm == 0 then some (.st8 a b) else none
  | 0x40 => if r a && r b && r c && imm == 0 then some (.sha256 a b c) else none
  | 0x41 => if r a && r b && r c && r imm then some (.memeq a b c imm) else none
  | 0x50 => if r a && r b && c == 0 && imm < 2 then some (.out imm a b) else none
  | op =>
    match BinOp.ofOpcode? op with
    | some bop => if r a && r b && r c && imm == 0 then some (.bin bop a b c) else none
    | none => none

/-- Decode exactly `n` instruction words. -/
def decodeCode : Nat → Bytes → Option (List Instr)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, op :: a :: b :: c :: i0 :: i1 :: i2 :: i3 :: rest => do
      let ins ← Instr.decode op.toNat a.toNat b.toNat c.toNat (Bytes.leToNat [i0, i1, i2, i3])
      let tl ← decodeCode n rest
      pure (ins :: tl)
  | _ + 1, _ => none

/-- Decode a program image.  Layout:
`"NPAI" ‖ 0x01 ‖ memSize:u32le ‖ dataLen:u32le ‖ data ‖ codeLen:u32le ‖ code`.
Trailing bytes are rejected. -/
def decode (b : Bytes) : Option Program :=
  match b with
  | m0 :: m1 :: m2 :: m3 :: v :: s0 :: s1 :: s2 :: s3 :: d0 :: d1 :: d2 :: d3 :: rest =>
    if [m0, m1, m2, m3] = magic ∧ v = version then
      let memSize := Bytes.leToNat [s0, s1, s2, s3]
      let dataLen := Bytes.leToNat [d0, d1, d2, d3]
      if memSize ≤ maxMemSize ∧ dataLen ≤ memSize ∧ dataLen ≤ rest.length then
        let data := rest.take dataLen
        match rest.drop dataLen with
        | c0 :: c1 :: c2 :: c3 :: code =>
          let codeLen := Bytes.leToNat [c0, c1, c2, c3]
          if codeLen ≤ maxCodeLen then
            (decodeCode codeLen code).map fun is => { memSize, data, code := is }
          else none
        | _ => none
      else none
    else none
  | _ => none

/-- Encode a program image (inverse of `decode` on well-formed programs). -/
def encode (p : Program) : Bytes :=
  magic ++ [version] ++ Bytes.leN 4 p.memSize ++ Bytes.leN 4 p.data.length ++ p.data ++
    Bytes.leN 4 p.code.length ++ p.code.flatMap Instr.encode

/-! ## The verifier and reduction programs as Lean functions -/

/-- The deployed verifier of the approved-interpreter route: decode the
bytecode image and run it with real SHA-256; anything but `accept` (including
an undecodable image) is rejection. -/
def interpVerify (code : Bytes) (fuel : Nat) (pub claim proof : Bytes) : Bool :=
  match decode code with
  | some p => run p { pub, claim, proof } fuel == some true
  | none => false

end Interp
end ArenaCore
