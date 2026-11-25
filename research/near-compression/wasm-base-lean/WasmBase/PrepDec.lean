import WasmBase.M2Check
/-!
# WasmBase.PrepDec — the PREP decoder certificate: reference functions (A-T4)

The PREP AIR (`PrepAir.lean`) decodes the hashed code bytes in-circuit.  This file is the
**reference** it is proved against (`PrepDecSound.lean`): plain functions on the byte list, written
to mirror the AIR row by row, so that "the AIR holds" becomes "the trace is these functions'
output".  How the reference relates to the spec's `prepare` is a separate, trace-independent
statement (`DecFaithfulAt`, §5), decided by evaluation for a given code.

* §1 `lebBytes` / `lebU` / `lebS` — LEB128 as the AIR reads it (continuation bit 7, at most `n`
  bytes, the groups from `g` on zero for exactness in the field).
* §2 `clsOf` — the instruction classes by opcode byte (13 classes, the M2 subset whose immediates
  the records carry); bytes in no class are rejected by the AIR (completeness only).
* §3 `decInstr` / `decSeq` — one instruction and one function body (`[iS, bE)`, ending exactly at
  `bE`, as the spec's `operators` does).
* §4 `hstep` / `emits` — the section walk from byte 8: section headers (the code section, id 10,
  entered; every other section skipped by its size), the code section's count, each body's size and
  local-group vector; a body is *emitted* as `(k, iS, bE)` (index, first instruction byte, end).
* §5 `dimg`, `decFields`, `DecFaithfulAt` — what a decoded instruction fixes in a CODE record, and
  the faithfulness of this decoder to `prepare`.
-/
namespace WasmBase
namespace PrepDec

/-! ## 1. LEB128 -/

/-- The bytes of one LEB128 at `i`: bytes `≥ 128` continue, at most `n` bytes. -/
def lebBytes (c : List Nat) (i : Nat) : Nat → Option (List Nat)
  | 0 => none
  | n + 1 => match c[i]? with
    | none => none
    | some b => if b < 128 then some [b] else (lebBytes c (i + 1) n).map (b :: ·)

/-- The unsigned value of LEB bytes: `Σ (b_g mod 128)·2^{7g}`. -/
def lebVal : List Nat → Nat
  | [] => 0
  | b :: bs => b % 128 + 128 * lebVal bs

/-- Unsigned LEB of at most `n` bytes whose groups from `g` on are zero; `(value, length)`. -/
def lebU (c : List Nat) (i n g : Nat) : Option (Nat × Nat) := do
  let bs ← lebBytes c i n
  if (bs.drop g).all (· % 128 = 0) then some (lebVal bs, bs.length) else none

/-- Bit `t` of a signed LEB's two's-complement value: the data bit inside the encoding, the sign
(bit 6 of the last byte) above it. -/
def sbit (bs : List Nat) (t : Nat) : Nat :=
  if t / 7 < bs.length then (bs.getD (t / 7) 0 / 2 ^ (t % 7)) % 2
  else (bs.getLastD 0 / 64) % 2

/-- The signed value modulo `2^w`, bit by bit. -/
def sval (bs : List Nat) (w : Nat) : Nat := ((List.range w).map fun t => 2 ^ t * sbit bs t).sum

/-- Signed LEB of at most `n` bytes, as a `w`-bit two's-complement value; `(value, length)`. -/
def lebS (c : List Nat) (i n w : Nat) : Option (Nat × Nat) := do
  let bs ← lebBytes c i n
  some (sval bs w, bs.length)

/-! ## 2. Instruction classes -/

/-- The integer numeric operators without immediates (`Decode.isIntNumOp`). -/
def numBytes : List Nat :=
  (List.range' 0x45 22) ++ (List.range' 0x67 36) ++ [0xA7, 0xAC, 0xAD] ++ (List.range' 0xC0 5)

/-- The integer loads and stores (`isLoadOp`, `isStoreOp`). -/
def memBytes : List Nat :=
  [0x28, 0x29] ++ List.range' 0x2C 10 ++ [0x36, 0x37] ++ List.range' 0x3A 5

inductive Cls where
  | eq0 | next | if_ | else_ | end_ | ret | brx | call | loc | mem | msg | c32 | c64
  deriving DecidableEq, Repr, Inhabited

/-- The classes in column order (`PrepAir.Code.clsCol`). -/
def clsList : List Cls := [.eq0, .next, .if_, .else_, .end_, .ret, .brx, .call, .loc, .mem, .msg, .c32, .c64]

/-- The opcode bytes of each class. -/
def clsBytes : Cls → List Nat
  | .eq0 => [0x00, 0x1A, 0x1B] ++ numBytes
  | .next => [0x02, 0x03]
  | .if_ => [0x04]
  | .else_ => [0x05]
  | .end_ => [0x0B]
  | .ret => [0x0F]
  | .brx => [0x0C, 0x0D]
  | .call => [0x10]
  | .loc => [0x20, 0x21, 0x22, 0x23, 0x24]
  | .mem => memBytes
  | .msg => [0x3F, 0x40]
  | .c32 => [0x41]
  | .c64 => [0x42]

def clsOf (b : Nat) : Option Cls := clsList.find? fun k => (clsBytes k).contains b

/-! ## 3. Instructions and bodies -/

/-- One instruction at `p`: `(opcode byte, immediate, encoded length)`.  The immediate is the
local / global / label / function index (`loc`, `brx`, `call`), the memory offset (`mem`), or the
constant modulo `2^32` / `2^64` (`c32`, `c64`); 0 otherwise. -/
def decInstr (c : List Nat) (p : Nat) : Option (Nat × Nat × Nat) := do
  let b ← c[p]?
  match clsOf b with
  | none => none
  | some k => match k with
    | .eq0 | .else_ | .end_ | .ret => some (b, 0, 1)
    | .next | .if_ | .msg => some (b, 0, 2)
    | .brx | .call | .loc => do let (v, l) ← lebU c (p + 1) 5 3; some (b, v, 1 + l)
    | .mem => do
      let a ← c[p + 1]?
      if a < 128 then do let (v, l) ← lebU c (p + 2) 5 4; some (b, v, 2 + l) else none
    | .c32 => do let (v, l) ← lebS c (p + 1) 5 32; some (b, v, 1 + l)
    | .c64 => do let (v, l) ← lebS c (p + 1) 10 64; some (b, v, 1 + l)

/-- The instructions from `p` to exactly `e` (fuel bounds the count). -/
def decSeq (c : List Nat) : Nat → Nat → Nat → Option (List (Nat × Nat))
  | 0, _, _ => none
  | f + 1, p, e => do
    let (b, v, l) ← decInstr c p
    if p + l = e then some [(b, v)]
    else if p + l < e then (decSeq c f (p + l) e).map ((b, v) :: ·) else none

/-- A body's instructions. -/
def decBody (c : List Nat) (iS bE : Nat) : Option (List (Nat × Nat)) := decSeq c (bE - iS) iS bE

/-! ## 4. The section walk -/

/-- Walk state: item kind (0 section header, 1 code count, 2 body size, 3 local-group count,
4 local group), position, body index, body end, local groups left. -/
structure HS where
  kind : Nat
  pos : Nat
  kk : Nat
  bE : Nat
  rem : Nat
  deriving DecidableEq, Repr, Inhabited

def hs0 : HS := ⟨0, 8, 0, 0, 0⟩

/-- One walk step: the item at `s.pos`, its emission (`(k, iS, bE)` at the end of a body's local
groups) and the next state. -/
def hrow (c : List Nat) (s : HS) : Option (Option (Nat × Nat × Nat) × HS) :=
  match s.kind with
  | 0 => do
    let id ← c[s.pos]?
    let (v, l) ← lebU c (s.pos + 1) 5 4
    if id = 10 then some (none, { s with kind := 1, pos := s.pos + 1 + l })
    else some (none, { s with pos := s.pos + 1 + l + v })
  | 1 => do
    let (_, l) ← lebU c s.pos 5 4
    some (none, { s with kind := 2, pos := s.pos + l, kk := 0 })
  | 2 => do
    let (v, l) ← lebU c s.pos 5 4
    some (none, { s with kind := 3, pos := s.pos + l, bE := s.pos + l + v })
  | 3 => do
    let (v, l) ← lebU c s.pos 5 4
    if v = 0 then some (some (s.kk, s.pos + l, s.bE), { s with kind := 2, pos := s.bE, kk := s.kk + 1, rem := 0 })
    else some (none, { s with kind := 4, pos := s.pos + l, rem := v })
  | _ => do
    let (_, l) ← lebU c s.pos 5 4
    if s.rem = 1 then some (some (s.kk, s.pos + l + 1, s.bE), { s with kind := 2, pos := s.bE, kk := s.kk + 1, rem := 0 })
    else some (none, { s with pos := s.pos + l + 1, rem := s.rem - 1 })

/-- The walk's states: `walk c r` is the state of row `r` (`none` once a step fails). -/
def walk (c : List Nat) : Nat → Option HS
  | 0 => some hs0
  | r + 1 => (walk c r).bind fun s => (hrow c s).map (·.2)

/-- The emissions of the first `f` rows (computed by iterating `hrow`, stopping at a failure). -/
def emitsGo (c : List Nat) : Nat → HS → List (Nat × Nat × Nat)
  | 0, _ => []
  | f + 1, s => match hrow c s with
    | none => []
    | some (e, s') => e.toList ++ emitsGo c f s'

/-- Every body the walk emits within `2^24` rows (the AIR's maximal height). -/
@[irreducible] def emits (c : List Nat) : List (Nat × Nat × Nat) := emitsGo c (2 ^ 24) hs0

/-! ## 5. Records and faithfulness -/

/-- What the AIR decodes of a spec instruction: `(opcode byte, immediate)`; instructions outside
the classes map to `(1000, 0)`, which no decoded instruction equals. -/
def dimg : NearSpecV3.Wasm.Instr → Nat × Nat
  | .unreachable => (0x00, 0)
  | .block _ => (0x02, 0)
  | .loop _ => (0x03, 0)
  | .if_ _ => (0x04, 0)
  | .else_ => (0x05, 0)
  | .end_ => (0x0B, 0)
  | .br l => (0x0C, l)
  | .brIf l => (0x0D, l)
  | .ret => (0x0F, 0)
  | .call f => (0x10, f)
  | .drop => (0x1A, 0)
  | .select none => (0x1B, 0)
  | .localGet x => (0x20, x)
  | .localSet x => (0x21, x)
  | .localTee x => (0x22, x)
  | .globalGet x => (0x23, x)
  | .globalSet x => (0x24, x)
  | .load op _ o => (op, o)
  | .store op _ o => (op, o)
  | .memSize => (0x3F, 0)
  | .memGrow => (0x40, 0)
  | .i32Const v => (0x41, v.toNat)
  | .i64Const v => (0x42, v.toNat)
  | .num op => (op, 0)
  | _ => (1000, 0)

/-- The CODE-record fields a decoded instruction fixes, at global pc `j`: `some v` = the field is
`v`; `none` = static analysis (`h`, `fee`, control targets, call fields), the residual
`StaticCert`.  Fields: `[pc, op, h, fee, x0, x1, x2, x3]`. -/
def fieldsOf (k : Cls) (j b v : Nat) : List (Option Nat) :=
  let z := some 0
  match k with
  | .eq0 => [some j, some b, none, none, z, z, z, z]
  | .next => [some j, some Chips.Ctrl.opNext, none, none, z, z, z, z]
  | .if_ => [some j, some Chips.IfC.opIf, none, none, none, z, z, z]
  | .else_ => [some j, some Chips.Ctrl.opJump, none, none, none, z, z, z]
  | .end_ => [some j, none, none, none, z, z, z, z]
  | .ret => [some j, some Chips.Ctrl.opHalt, none, none, z, z, z, z]
  | .brx => [some j, none, none, none, none, z, z, z]
  | .call => [some j, none, none, none, none, none, none, z]
  | .loc => [some j, some b, none, none, some v, z, z, z]
  | .mem => [some j, some b, none, none, some (v % 65536), some (v / 65536), z, z]
  | .msg => [some j, some (640 - b), none, none, z, z, z, z]
  | .c32 => [some j, some b, none, none, some (v % 65536), some (v / 65536 % 65536), z, z]
  | .c64 => [some j, some b, none, none, some (v % 65536), some (v / 65536 % 65536),
      some (v / 2 ^ 32 % 65536), some (v / 2 ^ 48 % 65536)]

def decFields (j : Nat) (d : Nat × Nat) : List (Option Nat) :=
  match clsOf d.1 with
  | some k => fieldsOf k j d.1 d.2
  | none => [some j, none, none, none, none, none, none, none]

theorem decFields_eq {j b v : Nat} {k : Cls} (h : clsOf b = some k) :
    decFields j (b, v) = fieldsOf k j b v := by simp [decFields, h]

/-- A record agrees with the fixed fields (decidable). -/
def agreeB (fs : List (Option Nat)) (r : List Nat) : Bool :=
  r.length == 8 && (List.range 8).all fun i => match fs.getD i none with
    | some v => r.getD i 0 == v
    | none => true

def Agree (fs : List (Option Nat)) (r : List Nat) : Prop := agreeB fs r = true

/-- The faithfulness check (a `Bool`, so the kernel can decide it for a given code). -/
def decFaithfulB (cfg : NearSpecV3.Wasm.NearCfg) (c : ArenaCore.Bytes) : Bool :=
  match NearSpecV3.Wasm.prepare cfg ⟨c.toArray⟩ true with
  | .ok p => (emits (c.map (·.toNat))).all (fun e =>
      match p.funcs[e.1]?, decBody (c.map (·.toNat)) e.2.1 e.2.2 with
      | some pf, some B => B == pf.code.toList.map dimg
      | _, _ => true)
  | _ => true

/-- **Decoder faithfulness at a code** (trace-independent): if `prepare` accepts `c`, every body
the walk emits for a defined function decodes to that function's instructions (as `dimg`). -/
def DecFaithfulAt (cfg : NearSpecV3.Wasm.NearCfg) (c : ArenaCore.Bytes) : Prop := decFaithfulB cfg c = true

/-! ## 6. The decoder certificate -/

/-- **What the PREP AIR proves about its cached matrices** (`PrepDecSound`): `cm` (height `hC`)
and `fm` (height `hF`) are `n` / `nF` live rows padded by repetition; FUNC row `i` is the function
whose body the walk emits as `ks[i]` at `[iS, bE)`, placed at `off i` (prefix sums of the body
sizes, ending at `n`); and every CODE row of it agrees with the decoded instruction's fixed fields
(`decFields`). -/
structure DecodeW (c : List Nat) (hC hF : Nat) (cm fm : List (List Nat)) (ks : List Nat)
    (n nF : Nat) (off size : Nat → Nat) : Prop where
  hn : 1 ≤ n ∧ n ≤ hC
  hnF : 1 ≤ nF ∧ nF ≤ hF
  cmLen : cm.length = hC
  fmLen : fm.length = hF
  ksLen : ks.length = nF
  off0 : off 0 = 0
  offS : ∀ i, i + 1 < nF → off (i + 1) = off i + size i
  offL : off (nF - 1) + size (nF - 1) = n
  body : ∀ i, i < nF → ∃ iS bE B, (ks.getD i 0, iS, bE) ∈ emits c ∧ decBody c iS bE = some B ∧
    B.length = size i ∧ (fm.getD i []).length = 8 ∧ (fm.getD i []).getD 0 0 = off i ∧
    ∀ l, l < size i → Agree (decFields (off i + l) (B.getD l (0, 0))) (cm.getD (off i + l) [])
  padC : ∀ j, n ≤ j → j < hC → cm.getD j [] = cm.getD (n - 1) []
  padF : ∀ i, nF ≤ i → i < hF → fm.getD i [] = fm.getD (nF - 1) []

def DecodeCert (c : List Nat) (hC hF : Nat) (cm fm : List (List Nat)) (ks : List Nat) : Prop :=
  ∃ n nF off size, DecodeW c hC hF cm fm ks n nF off size

end PrepDec
end WasmBase
