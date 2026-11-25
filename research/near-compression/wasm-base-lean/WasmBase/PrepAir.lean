import WasmBase.ShaSound
import WasmBase.PrepDec

/-!
# WasmBase.PrepAir — the PREP leaf's AIR (A-T3, plan §3.5: PREP is a `wasm`-kind template)

PREP is the `.pre → preConf q` step of a call (`TmplPrep.lean`): it takes the in-record's
`codeRoot = preCodeRoot q = SHA-256(q.code) ‖ 0^10` (S2, written by lane F's enter leaf) to the
out-record's `codeRoot` / `funcRoot`, the cached-commitment roots of the padded CODE / FUNC record
matrices that every Wasm segment leaf of the call commits (S3, R1 of `a-t1/README.md` §4).

## Tables (`prepAir`, A-T4: 6 tables, 33 public values)

| # | table | role |
|---|---|---|
| 0 | `PHDR` | one active row (`act`, first row only): **sends** the hash-call summary `[0, 53, len, 0, 1, 0, 0, 0]` and **receives** the digest `[0, 53, 1, len, h_0 … h_31]`, with `h_i` = public `i` (the 32 digest bytes) and `len` = public 32 |
| 1 | `SHA256` | lane A's SHA-256 table (the classical `ZkFormal.Sha.Table` constraints, 549 columns) plus `Dmult ∈ {0, 1}`; its digest row **sends** `[ts, hid] ++` the classical digest message `[Id, Nd, digest bytes]` to `PHDR`; A-T4: its 16 byte slots **receive** `[Id, pos, byte]` from `CB` (`byteRecv`, the classical byte interactions) |
| 2 | `CB` | the code bytes, row `i` = byte `i`, live rows exactly `i < len`; **sends** `[1, i, byte]` to the SHA byte slots (`busCB`) and **answers** byte reads `[i, byte]` (`busLB`, live rows only) |
| 3 | `HDR` | the section walk (`PrepDec.hrow`): one row per section header / code count / body size / local-group count / local group; the code section entered by an `id = 10` test, others skipped by size; **emits** each body `(k, iS, bE)` at the end of its local groups (`busBody`) |
| 4 | `CODE` | the 8 cached record columns of the segment AIR's `CODE`, then the decoder: pointer, 11-byte window, class one-hot (indicator polynomials of the opcode bits), LEB chains; each live row's record fields fixed by the bytes (`PrepDec.decFields`) are constrained, rows step by the instruction length, functions start at FUNC rows (`busFn`) and end at their body end |
| 5 | `FUNC` | the 8 cached record columns of the segment AIR's `FUNC`, then `[live, k, iS, bE, size]`: offsets are prefix sums, each row's body is looked up among `HDR`'s emissions |

The cached CODE / FUNC columns are the segment tables' (same names, first 8 columns, the template
height and commitment parameters), so the PREP proof's cached commitments equal the segment leaves'
for equal matrices (R1; measured on T1, `a-t1/README.md` §10–11).

## What the AIR binds

* **In-circuit, kernel-checked** (`PrepSound.prep_sha_sound`): the public values are
  `SHA-256(m)` and `|m|` for the message `m` the SHA table lays out.
* **A-T4, in-circuit:** the decoder certificate `PrepDec.DecodeCert` (stated as the AIR obligation
  `PrepDecSound.PrepDecodeSound`; its byte-read layer `PrepDecSound.lb_read_sound` is proved).
* **Not in-circuit:** the static-analysis fields (`TmplPrep.StaticCert`).

Finding (A-T3): `Chips.Sha`'s added `sh_len` column is not tied to the classical `Nd` by any
constraint, so the segment AIR's `sha256` host summary does not bind the message length (it is
inside the stated `HashInputLink` obligation).  A PREP mutant with a wrong public length was
accepted while PREP's digest message carried no `Nd`.
-/

namespace WasmBase
namespace Chips
namespace Prep

open Expr

/-- The code-hash public values: the 32 digest bytes. -/
def pubHash (i : Nat) : Nat := i
/-- The code length (bytes). -/
def pubLen : Nat := 32
def numPub : Nat := 33

/-- The SHA host id the summary carries (`sha256`). -/
def hid : Nat := 53
/-- The message id (the classical table's `Id`). -/
def mid : Nat := 1

/-- The classical digest message `[Id, Nd, digest bytes]` (`ZkFormal.Sha.Table.interactions`,
entry 16; its fields do not depend on the bus numbers). -/
def classDigMsg : List ZkFormal.Air.Expr := ((ZkFormal.Sha.Table.interactions 0 0)[16]!).msg

/-- The digest message `[ts, hid, Id, Nd, b_0 … b_31]`. -/
def digMsgP : List Expr := [Sha.tsE, Sha.hidE] ++ classDigMsg.map Sha.toW

/-- `Dmult` is a bit (the classical table leaves it free). -/
def cDmult : Expr := bool Sha.dmultE

/-- `SHA256` with the digest sent to `PHDR`: the classical constraints, the message constancy
constraints, `Dmult ∈ {0,1}`, the digest declaration pair and the call-summary receive. -/
def shaTable : Table :=
  ⟨"SHA256", Sha.cols, Sha.constraints ++ [cDmult],
    [⟨busHashCall, true, Sha.dmultE, digMsgP⟩,
     ⟨busHashDigest, true, Sha.sE, Sha.declMsg⟩,
     ⟨busHashDigest, false, Sha.dmultE, Sha.declMsg⟩,
     ⟨busHashCall, false, Sha.dmultE, Sha.callMsg⟩]⟩

/-- `PHDR`: `act = 1` on the first row only. -/
def act : Nat := 0

/-- The call summary PREP announces: `[ts = 0, hid, len, ptr = 0, reg = id, 0, 0, 0]`. -/
def callMsg : List Expr := [0, Expr.c hid, pv pubLen, 0, Expr.c mid, 0, 0, 0]

/-- The digest PREP expects: `[ts = 0, hid, id, public length, public hash bytes]`. -/
def hashMsg : List Expr :=
  [0, Expr.c hid, Expr.c mid, pv pubLen] ++ (List.range 32).map (fun i => pv (pubHash i))

def phdrConstraints : List Expr :=
  [.first * (v act - 1), (1 - .first) * v act]

def phdrTable : Table :=
  ⟨"PHDR", ["act"], phdrConstraints,
    [⟨busHashCall, true, v act, callMsg⟩,
     ⟨busHashCall, false, v act, hashMsg⟩]⟩

/-! ## A-T4: the decoder certificate tables

Buses (PREP-local): `busCB` — code bytes into the SHA table's byte slots; `busLB` — byte lookups
`[pos, byte]` answered by `CB`; `busBody` — body lookups `[k, iS, bE]` answered by `HDR`'s
emitting rows; `busFn` — the function rows `[off, k, iS, bE, size]`, a permutation between `FUNC`'s
live rows and `CODE`'s function-start rows. -/

def busCB : Nat := 220
def busLB : Nat := 221
def busBody : Nat := 222
def busFn : Nat := 223

/-- The classical table's 16 byte slots, received from `CB` on `busCB`: slot `q` of a round row
receives `[Id, pos, byte]` with count `F q` (`ZkFormal.Sha.Table.interactions`, entries 0–15). -/
def byteRecv : List Inter :=
  ((ZkFormal.Sha.Table.interactions busCB 0).take 16).map fun i =>
    ⟨busCB, false, Sha.toW (i.mult.headD (.const 0)), i.msg.map Sha.toW⟩

/-- `SHA256` of A-T4: A-T3's table plus the byte slots. -/
def shaTableD : Table := ⟨"SHA256", shaTable.cols, shaTable.constraints, shaTable.inters ++ byteRecv⟩

namespace Dec

/-- `Σ_{j<8} 2^j · bit j`. -/
def byteOf (bit : Nat → Expr) : Expr := (List.range 8).foldl (fun e j => e + Expr.c (2 ^ j) * bit j) 0
/-- `Σ_{j<7} 2^j · bit j` (the LEB group). -/
def low7Of (bit : Nat → Expr) : Expr := (List.range 7).foldl (fun e j => e + Expr.c (2 ^ j) * bit j) 0
def lit (x : Expr) (one : Bool) : Expr := if one then x else 1 - x
/-- `[byte = val]` on boolean bits: the product of the eight bit literals. -/
def eqPat (bit : Nat → Expr) (val : Nat) : Expr :=
  (List.range 8).foldl (fun e j => e * lit (bit j) (val.testBit j)) 1
/-- `[byte ∈ S]` (degree 8). -/
def indE (bit : Nat → Expr) (S : List Nat) : Expr := S.foldl (fun e val => e + eqPat bit val) 0
def sumE (l : List Expr) : Expr := l.foldl (· + ·) 0

end Dec

/-! ### CB: the code bytes (row `i` = byte `i`, live rows `i < len`) -/
namespace CB
open Expr
def pos : Nat := 0
def byte : Nat := 1
def live : Nat := 2
def mult : Nat := 3
def cols : List String := ["pos", "byte", "live", "mult"]
def constraints : List Expr :=
  [.first * v pos, .trans * (nv pos - v pos - 1), bool (v live), .first * (v live - 1),
   .trans * (nv live * (1 - v live)),
   .trans * (v live * (1 - nv live) * (v pos + 1 - pv pubLen)),
   .last * (v live * (v pos + 1 - pv pubLen)),
   v mult * (1 - v live)]
def inters : List Inter :=
  [⟨busCB, true, v live, [Expr.c mid, v pos, v byte]⟩,
   ⟨busLB, false, v mult, [v pos, v byte]⟩]
def table : Table := ⟨"CB", cols, constraints, inters⟩
end CB

/-! ### HDR: the section walk (one row per item; `PrepDec.hrow`) -/
namespace Hdr
open Expr
def act : Nat := 0
def kS : Nat := 1
def kC : Nat := 2
def kB : Nat := 3
def kG : Nat := 4
def kL : Nat := 5
def pos : Nat := 6
def isc : Nat := 7
def zinv : Nat := 8
def z : Nat := 9
def zi : Nat := 10
def kk : Nat := 11
def bE : Nat := 12
def rem : Nat := 13
def mult : Nat := 14
/-- bit `j` of window byte `i < 6` -/
def bitC (i j : Nat) : Nat := 15 + 8 * i + j
/-- chain A (section size, bytes 1..5): `aA i` for `i ∈ 2..5` -/
def aAc (i : Nat) : Nat := 63 + (i - 2)
/-- chain B (other LEBs, bytes 0..4): `aB i` for `i ∈ 1..4` -/
def aBc (i : Nat) : Nat := 67 + (i - 1)
/-- the read count of window byte `i < 6` (a column, `= rd i`, boolean) -/
def uc (i : Nat) : Nat := 71 + i
def ncols : Nat := 77
def cols : List String :=
  ["act", "kS", "kC", "kB", "kG", "kL", "pos", "isc", "zinv", "z", "zi", "kk", "bE", "rem", "mult"] ++
  ((List.range 6).flatMap fun i => (List.range 8).map fun j => s!"y{i}b{j}") ++
  ((List.range' 2 4).map fun i => s!"aA{i}") ++ ((List.range' 1 4).map fun i => s!"aB{i}") ++
  ((List.range 6).map fun i => s!"u{i}")

def bit (i j : Nat) : Expr := v (bitC i j)
def Y (i : Nat) : Expr := Dec.byteOf (bit i)
def cb (i : Nat) : Expr := bit i 7
def low7 (i : Nat) : Expr := Dec.low7Of (bit i)
def aA (i : Nat) : Expr := if i = 1 then v kS else v (aAc i)
def aB (i : Nat) : Expr := if i = 0 then v kC + v kB + v kG + v kL else v (aBc i)
def LA : Expr := Dec.sumE ((List.range' 1 5).map aA)
def LB : Expr := Dec.sumE ((List.range 5).map aB)
def VA : Expr := Dec.sumE ((List.range 4).map fun g => aA (1 + g) * low7 (1 + g) * Expr.c (2 ^ (7 * g)))
def VB : Expr := Dec.sumE ((List.range 4).map fun g => aB g * low7 g * Expr.c (2 ^ (7 * g)))
def kinds : List Nat := [kS, kC, kB, kG, kL]
/-- the zero-tested expression: the group count (GCNT) or the groups left minus one (LG) -/
def zE : Expr := v kG * VB + v kL * (v rem - 1)
def kGL : Expr := v kG + v kL
def gate : Expr := .trans * nv act
def newPos : Expr :=
  v kS * (v pos + 1 + LA + (1 - v isc) * VA) + (v kC + v kB) * (v pos + LB) +
  kGL * (v z * v bE + (1 - v z) * (v pos + LB + v kL))
def newKk : Expr := v kk - v kC * v kk + v z
def newBE : Expr := v bE + v kB * (v pos + LB + VB - v bE)
def newRem : Expr := v rem + v kG * (VB - v rem) - v kL
def iS : Expr := v pos + LB + v kL
/-- read counts: byte 0 always (the section id or a LEB's first byte), then the active chain -/
def rd (i : Nat) : Expr := if i = 0 then v act else if i = 5 then aA 5 else aA i + aB i

def constraints : List Expr :=
  ((List.range 6).flatMap fun i => (List.range 8).map fun j => bool (bit i j)) ++
  (kinds.map fun k => bool (v k)) ++
  [bool (v act), v act - Dec.sumE (kinds.map v), .trans * (nv act * (1 - v act)),
   .first * (v act - 1), .first * (v kS - 1), .first * (v pos - 8),
   .first * v kk, .first * v bE, .first * v rem,
   -- LEB chains
   aA 2 - aA 1 * cb 1, aA 3 - aA 2 * cb 2, aA 4 - aA 3 * cb 3, aA 5 - aA 4 * cb 4,
   aA 5 * cb 5, aA 5 * low7 5,
   aB 1 - aB 0 * cb 0, aB 2 - aB 1 * cb 1, aB 3 - aB 2 * cb 2, aB 4 - aB 3 * cb 3,
   aB 4 * cb 4, aB 4 * low7 4,
   -- section id = 10 test
   bool (v isc), v isc * (1 - v kS), v isc * (Y 0 - 10), v kS * ((Y 0 - 10) * v zinv - 1 + v isc),
   -- zero test of `zE` on GCNT / LG rows
   bool (v z), v z * (1 - kGL), v z * zE, kGL * (zE * v zi - 1 + v z),
   v mult * (1 - v z),
   -- transitions
   gate * (nv kS - v kS * (1 - v isc)), gate * (nv kC - v kS * v isc), gate * (nv kB - v kC - v z),
   gate * (nv kG - v kB), gate * (nv kL - kGL * (1 - v z)),
   gate * (nv pos - newPos), gate * (nv kk - newKk), gate * (nv bE - newBE), gate * (nv rem - newRem)] ++
  ((List.range 6).flatMap fun i => [bool (v (uc i)), v (uc i) - rd i])

def inters : List Inter :=
  ((List.range 6).map fun i => ⟨busLB, true, v (uc i), [v pos + Expr.c i, Y i]⟩) ++
  [⟨busBody, false, v mult, [v kk, iS, v bE]⟩]
def table : Table := ⟨"HDR", cols, constraints, inters⟩
end Hdr

/-! ### CODE: the records (cached) and their decoding (`PrepDec.decInstr`) -/
namespace CodeP
open Expr
/-- cached record columns `0..7` -/
def cPc : Nat := 0
def cOp : Nat := 1
def cX (l : Nat) : Nat := 4 + l
def live : Nat := 8
def fst : Nat := 9
def kk : Nat := 10
def bE : Nat := 11
def fsz : Nat := 12
def lpc : Nat := 13
def ptr : Nat := 14
def sg : Nat := 15
/-- class column of class number `k < 13` (`PrepDec.clsList` order) -/
def clsC (k : Nat) : Nat := 16 + k
def bitC (i j : Nat) : Nat := 29 + 8 * i + j
/-- chain 1 (`loc`, `brx`, `call`, `c32`, `c64`; bytes 1..10): `a1 i`, `i ∈ 2..10` -/
def a1c (i : Nat) : Nat := 117 + (i - 2)
/-- chain 2 (`mem` offset; bytes 2..6): `a2 i`, `i ∈ 3..6` -/
def a2c (i : Nat) : Nat := 126 + (i - 3)
/-- the read count of window byte `i < 11` (a column, `= rd i`, boolean) -/
def uc (i : Nat) : Nat := 130 + i
def ncols : Nat := 141
def cols : List String :=
  ["pc", "op", "h", "fee", "x0", "x1", "x2", "x3", "live", "fst", "kk", "bE", "fsz", "lpc", "ptr", "sg"] ++
  ((List.range 13).map fun k => s!"cls{k}") ++
  ((List.range 11).flatMap fun i => (List.range 8).map fun j => s!"y{i}b{j}") ++
  ((List.range' 2 9).map fun i => s!"a1_{i}") ++ ((List.range' 3 4).map fun i => s!"a2_{i}") ++
  ((List.range 11).map fun i => s!"u{i}")

def bit (i j : Nat) : Expr := v (bitC i j)
def Y (i : Nat) : Expr := Dec.byteOf (bit i)
def cb (i : Nat) : Expr := bit i 7
def low7 (i : Nat) : Expr := Dec.low7Of (bit i)
def cls (k : PrepDec.Cls) : Expr := v (clsC (PrepDec.clsList.idxOf k))
def a1 (i : Nat) : Expr :=
  if i = 1 then cls .loc + cls .brx + cls .call + cls .c32 + cls .c64 else v (a1c i)
def a2 (i : Nat) : Expr := if i = 2 then cls .mem else v (a2c i)
def len : Expr :=
  1 + cls .next + cls .if_ + cls .msg + Dec.sumE ((List.range' 1 10).map a1) + cls .mem +
    Dec.sumE ((List.range' 2 5).map a2)
def V1 : Expr := Dec.sumE ((List.range 3).map fun g => a1 (1 + g) * low7 (1 + g) * Expr.c (2 ^ (7 * g)))
def ob (t : Nat) : Expr := a2 (2 + t / 7) * bit (2 + t / 7) (t % 7)
def lo : Expr := Dec.sumE ((List.range 16).map fun t => Expr.c (2 ^ t) * ob t)
def hi : Expr := Dec.sumE ((List.range 12).map fun t => Expr.c (2 ^ t) * ob (16 + t))
def vb (t : Nat) : Expr := a1 (1 + t / 7) * bit (1 + t / 7) (t % 7) + (1 - a1 (1 + t / 7)) * v sg
def limb (l : Nat) : Expr := Dec.sumE ((List.range 16).map fun u => Expr.c (2 ^ u) * vb (16 * l + u))
def sgE : Expr := Dec.sumE ((List.range 10).map fun g => a1 (1 + g) * (1 - cb (1 + g)) * bit (1 + g) 6)
def u32c : Expr := cls .loc + cls .brx + cls .call
def gl (k : PrepDec.Cls) : Expr := v live * cls k
def sumCls (ks : List PrepDec.Cls) : Expr := Dec.sumE (ks.map cls)
def rd (i : Nat) : Expr :=
  if i = 0 then v live else if i = 1 then a1 1 + cls .mem
  else if i ≤ 6 then a1 i + a2 i else a1 i
/-- `1 − [this row ends its function]`: the next row continues the same function -/
def cont : Expr := .trans * nv live * (1 - nv fst)

def constraints : List Expr :=
  ((List.range 11).flatMap fun i => (List.range 8).map fun j => bool (bit i j)) ++
  (PrepDec.clsList.map fun k => cls k - Dec.indE (bit 0) (PrepDec.clsBytes k)) ++
  [bool (v live), .first * (v live - 1), .trans * (nv live * (1 - v live)),
   v live * (sumCls PrepDec.clsList - 1),
   bool (v fst), v fst * (1 - v live), .first * (v fst - 1), v fst * v lpc,
   .first * v cPc, .trans * (nv live * (nv cPc - v cPc - 1))] ++
  -- within a function: carry and step
  [cont * (nv kk - v kk), cont * (nv bE - v bE), cont * (nv fsz - v fsz),
   cont * (nv lpc - v lpc - 1), cont * (nv ptr - v ptr - len),
   -- the last row of a function ends at the body end, after `fsz` instructions
   v live * (1 - cont) * (v ptr + len - v bE),
   v live * (1 - cont) * (v lpc + 1 - v fsz)] ++
  -- padding rows repeat the last record (`padRep`)
  ((List.range 8).map fun i => .trans * ((1 - nv live) * (nv i - v i))) ++
  -- LEB chains, termination, exactness
  ((List.range' 1 9).map fun i => a1 (i + 1) - a1 i * cb i) ++
  ((List.range' 2 4).map fun i => a2 (i + 1) - a2 i * cb i) ++
  [(u32c + cls .c32) * a1 6, a1 10 * cb 10, a2 6 * cb 6, a2 6 * low7 6,
   u32c * (a1 4 * low7 4), u32c * (a1 5 * low7 5), cls .mem * cb 1,
   v sg - sgE] ++
  -- record fields
  [v live * (sumCls [.eq0, .loc, .mem, .c32, .c64]) * (v cOp - Y 0),
   gl .next * (v cOp - Expr.c Chips.Ctrl.opNext), gl .if_ * (v cOp - Expr.c Chips.IfC.opIf),
   gl .else_ * (v cOp - Expr.c Chips.Ctrl.opJump), gl .ret * (v cOp - Expr.c Chips.Ctrl.opHalt),
   gl .msg * (v cOp - (640 - Y 0)),
   v live * sumCls [.eq0, .next, .end_, .ret, .msg] * v (cX 0),
   gl .loc * (v (cX 0) - V1), gl .mem * (v (cX 0) - lo),
   v live * (cls .c32 + cls .c64) * (v (cX 0) - limb 0),
   v live * sumCls [.eq0, .next, .if_, .else_, .end_, .ret, .brx, .loc, .msg] * v (cX 1),
   gl .mem * (v (cX 1) - hi), v live * (cls .c32 + cls .c64) * (v (cX 1) - limb 1),
   v live * (1 - cls .call - cls .c64) * v (cX 2), gl .c64 * (v (cX 2) - limb 2),
   v live * (1 - cls .c64) * v (cX 3), gl .c64 * (v (cX 3) - limb 3)] ++
  ((List.range 11).flatMap fun i => [bool (v (uc i)), v (uc i) - rd i])

def inters : List Inter :=
  ((List.range 11).map fun i => ⟨busLB, true, v (uc i), [v ptr + Expr.c i, Y i]⟩) ++
  [⟨busFn, false, v fst, [v cPc, v kk, v ptr, v bE, v fsz]⟩]
def table : Table := ⟨"CODE", cols, constraints, inters⟩
end CodeP

/-! ### FUNC: the function rows (cached) and their bodies -/
namespace FuncP
open Expr
def cOff : Nat := 0
def live : Nat := 8
def kk : Nat := 9
def iS : Nat := 10
def bE : Nat := 11
def size : Nat := 12
def cols : List String :=
  ["entry", "shape", "charge", "pro", "m0", "m1", "m2", "m3", "live", "kk", "iS", "bE", "size"]
def constraints : List Expr :=
  [bool (v live), .first * (v live - 1), .trans * (nv live * (1 - v live)),
   .first * v cOff, .trans * (nv live * (nv cOff - v cOff - v size))] ++
  ((List.range 8).map fun i => .trans * ((1 - nv live) * (nv i - v i)))
def inters : List Inter :=
  [⟨busFn, true, v live, [v cOff, v kk, v iS, v bE, v size]⟩,
   ⟨busBody, true, v live, [v kk, v iS, v bE]⟩]
def table : Table := ⟨"FUNC", cols, constraints, inters⟩
end FuncP

end Prep

/-- **The PREP AIR** (A-T4: PHDR, SHA256 with its byte slots, the decoder tables CB and HDR, and
CODE / FUNC with their cached record columns first). -/
def prepAir : Air :=
  { tables := [Prep.phdrTable, Prep.shaTableD, Prep.CB.table, Prep.Hdr.table, Prep.CodeP.table,
      Prep.FuncP.table], numPub := Prep.numPub }

/-! ## Kernel facts about the AIR value -/

theorem prepAir_tables : prepAir.tables.length = 6 := rfl

/-- PREP's CODE / FUNC tables have the segment AIR's cached record columns first (the cached
commitment covers exactly these 8 columns, `ToolCore.cachedCols`), so equal record matrices give
equal roots (R1). -/
theorem prep_cached_names : (prepAir.tables[4]'(by decide)).name = Code.table.name ∧
    (prepAir.tables[5]'(by decide)).name = Func.table.name ∧
    ((prepAir.tables[4]'(by decide)).cols.take 8 = Code.table.cols.take 8) ∧
    ((prepAir.tables[5]'(by decide)).cols.take 8 = Func.table.cols.take 8) := by decide

/-- PREP's SHA table has the classical constraints of lane A's SHA-256 table (and one more). -/
theorem prep_sha_constraints :
    (prepAir.tables[1]'(by decide)).constraints = Sha.constraints ++ [Prep.cDmult] := rfl

/-- A-T3's SHA table is kept, with the 16 byte slots appended. -/
theorem prep_sha_inters : (prepAir.tables[1]'(by decide)).inters = Prep.shaTable.inters ++ Prep.byteRecv := rfl

theorem classDigMsg_len : Prep.classDigMsg.length = 34 := by
  simp [Prep.classDigMsg, ZkFormal.Sha.Table.interactions]

/-- The digest message has 36 fields, the summary 8: the receive of `hashMsg` can only be matched
by a digest row's send (no other 36-field sender on bus 211). -/
theorem phdr_msg_len : Prep.hashMsg.length = 36 ∧ Prep.digMsgP.length = 36 ∧
    Prep.callMsg.length = 8 ∧ Sha.callMsg.length = 8 := by
  refine ⟨by simp [Prep.hashMsg], ?_, rfl, rfl⟩
  simp only [Prep.digMsgP, List.length_append, List.length_map, classDigMsg_len]; rfl

end Chips
end WasmBase
