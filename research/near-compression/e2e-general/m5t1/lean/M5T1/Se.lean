import M5T1.Air
import M5T1.Sh

/-!
# M5T1.Se — the engine half of the STATE leaves (F-5)

A STATE leaf proves `eng I c →* eng I c'` along VM-free engine steps (lane E's `MState`; T1: seg A
`c1 → c2`, receipt 0 and the forwards; seg B `c7 → c8`; and, D-b, the finalize step `c8 → c9`,
`yields _ _ 0 → done out`). It is a **split leaf** (plan §3.5 "Split leaves"): lane F's engine
half joined with lane B's state half (`m5tSegC`: `STC` + the working-set rows) on `STMQ`/`STMA`/
`SREQ`/`HB`. This file is the engine half's boundary table:

* **`SE`** (row 0, public values only; `B_in` = `engF` at 0, `B_out` = `engF` at 450): the input
  is an engine record (`phase 1`, `inCall 0`, no Wasm part); the output by `seRule` — `phase 1`,
  out of a call, **`vmAcc = bdigest []`** (no VM call in a VM-free step), **`rPrepaid = rBurnt =
  rUsed = 0`** (lane E's `clearE` outside a call), **`gasUsed = gasBurnt`** (`clearE`: both are
  `rs.gas`), every field `clearE` / `ctxDE` / `outDE` keeps constant along an engine run copied
  (`claimDigest`, `blockIdx`, `actionIdx`, `t`, `ctxRoot`, `outRcptN`, `bwAcc`), and the fields the
  steps move left to their owners: **`stRoot` = `STMA`'s `r_out`** (lane B's `STC`, exactly as in
  the resume leaf `RB`), the receipt-state counters (`receiptIdx`, `gasUsed`, `compute`,
  `balanceBurnt`) and the accumulators (`outcomeAcc`, `outRcpt0`, `proposalsAcc`): the step
  contract `SeC.SeStep` (no STATE engine rows compute VM-free steps yet).
* the `STMQ` / `STMA` traffic `[r_in, tag_out, rest_out]` / `[r_out, tag_in, rest_in]` (14
  three-byte big-endian limbs per digest, lane B's `STC` layout), the metas `RNG`-checked bytes.

The leaf AIR is `[SE, RNG]` (`seAir`); the prover adds `XTAPE` (on T1: the stand-in for lane B's
`STC`) as a cached table (`fullSe`).

## F-7: the opening rows (lane E's M14 interface)

`SE` row 0 now also **opens** the configuration it steps from and **closes** the one it steps to,
with lane E's incremental remainder (`join/RestI.lean`, `encRestI`). Every hash is a run of the new
table `SH` (`Sh.lean`: SHA-384 through the native SHA-512 chip, as `ACC`), demanded on `SHD` and,
for fixed content, fed block by block on `SHB` (`hashes`):

| `hid` | message (SHA-512-padded by `padE`) | digest | when |
|---|---|---|---|
| 0 | `tag_in ‖ ws ‖ u64 wsLen ‖ trie ‖ u64 idx ‖ rest_in` (139 B: lane B's `StCommit.ser`) | `B_in.stRoot` (public) | always |
| 1 | `d_static ‖ d_queue ‖ d_move` (126 B, `encRestI`) | `rest_in` (`STMA`) | always |
| 2 | `d_static' ‖ d_queue' ‖ d_move'` | `rest_out` (`STMQ`) | always |
| 3 | `d_keys ‖ d_shape` (84 B) | `d_static` | finalize (`fin`) |
| 4 | `d_keys ‖ d_shape'` | `d_static'` | finalize |
| 5 | `Ser.enc none` = `[0]` | `d_shape'` | finalize |
| 6 | witnessed (`Ser.enc (restMove (restOfB v))`) | `d_move` | always |
| 7 | witnessed (the stepped moving part) | `d_move'` | always |
| 8 | witnessed (`1 ‖ Ser.enc I`) | `B_in.ctxRoot` (public) | `cx` (item 4's measurement) |

and row 0 checks: `fin ⇒ tag_in = 8 ∧ tag_out = 3 ∧ d_queue' = d_queue` (the finalize step:
`yields _ _ 0 → done`, lane E's `finPos_of_tag`), `¬fin ⇒ d_static' = d_static` (copied), `tag_in <
255` (`RNG [tag_in + 1]`), every opened / closed byte `RNG`-checked. The step itself — how the
witnessed moving part `d_move'`'s preimage, `d_queue'` and `tag_out` follow from the opened ones and
the intake — is the named residual `SeMove` (`join-check/SeStepI.lean`).
-/

namespace M5T1

open ZkFormal.Air

namespace Se

def L : Layout := [("tgo", 1), ("rso", 42), ("tgi", 1), ("rsi", 42),
  -- F-7: the mode bits, the opened `stRoot` fields, the remainder's parts in / out, the counts
  ("fin", 1), ("cx", 1), ("wsi", 48), ("wli", 8), ("tri", 32), ("ixi", 8),
  ("dS", 42), ("dQ", 42), ("dM", 42), ("dSo", 42), ("dQo", 42), ("dMo", 42), ("dK", 42), ("dSh", 42),
  ("dShN", 42), ("nbi", 1), ("nbo", 1), ("nbc", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

/-- Public values: the boundary pair (two engine records). -/
def PL : Layout := [("bin", 450), ("bout", 450)]
def NUM_PUB : Nat := PL.width

def SI : BndLay.Side := ⟨BndLay.engF, 0⟩
def SO : BndLay.Side := ⟨BndLay.engF, 450⟩

/-- **The STATE engine half's output rules** (F-5; module header). -/
def seRule : String → BndLay.ORule
  | "phase" => .num 1 | "inCall" => .num 0 | "wasmTag" => .num 0
  | "rPrepaid" => .num 0 | "rBurnt" => .num 0 | "rUsed" => .num 0
  | "vmAcc" => .dig BndLay.emptyDig
  | "stRoot" => .free | "receiptIdx" => .free | "gasUsed" => .free | "gasBurnt" => .free
  | "compute" => .free | "balanceBurnt" => .free | "outcomeAcc" => .free | "outRcpt0" => .free
  | "proposalsAcc" => .free
  | _ => .copy

/-- **`SE`'s constraints (F-5)** (row 0): input an engine record, output by `seRule`, `gasUsed =
gasBurnt` out. -/
def cons5 : List Expr :=
  BndLay.constF SI "phase" 1 ++ BndLay.constF SI "inCall" 0 ++ BndLay.constF SI "wasmTag" 0 ++
  (BndLay.engF.flatMap fun p => BndLay.ruleCons SI SO p.1 p.2 (seRule p.1)) ++
  (List.range 8).map fun j => BndLay.gate (SO.b "gasUsed" j - SO.b "gasBurnt" j)

/-! ### F-7: the opening rows -/

/-- `w` columns of group `s`. -/
def cols (s : String) (w : Nat) : List Expr := (List.range w).map fun j => c s j

/-- SHA-512 padding of a byte-expression message (FIPS 180-4 §5.1.2): `m ‖ 0x80 ‖ 0^k ‖ be128 (8·|m|)`. -/
def padE (m : List Expr) : List Expr :=
  m ++ [K 128] ++ List.replicate ((239 - m.length % 128) % 128) (K 0) ++
    (List.range 16).map fun i => K (8 * m.length / 256 ^ (15 - i) % 256)

/-- A hash `SE` demands from `SH`: its id, multiplicity (a 0/1 product of bits), kind, fixed message,
digest bytes and (witnessed kind) the run's last block index. -/
structure HSpec where
  hid : Nat
  mul : Expr
  fx : Bool
  msg : List Expr
  dig : Nat → Expr
  nb : Expr

/-- `tag_in ‖ ws ‖ u64 wsLen ‖ trie ‖ u64 idx ‖ rest_in`: lane B's `StCommit.ser` of the opening. -/
def serIn : List Expr := [c "tgi"] ++ cols "wsi" 48 ++ cols "wli" 8 ++ cols "tri" 32 ++ cols "ixi" 8 ++ cols "rsi" 42

def hS0 : HSpec := ⟨0, .isFirst, true, serIn, (fun j => SI.b "stRoot" j), 0⟩
def hS1 : HSpec := ⟨1, .isFirst, true, cols "dS" 42 ++ cols "dQ" 42 ++ cols "dM" 42, (fun j => c "rsi" j), 0⟩
def hS2 : HSpec := ⟨2, .isFirst, true, cols "dSo" 42 ++ cols "dQo" 42 ++ cols "dMo" 42, (fun j => c "rso" j), 0⟩
def hS3 : HSpec := ⟨3, .isFirst * c "fin", true, cols "dK" 42 ++ cols "dSh" 42, (fun j => c "dS" j), 0⟩
def hS4 : HSpec := ⟨4, .isFirst * c "fin", true, cols "dK" 42 ++ cols "dShN" 42, (fun j => c "dSo" j), 0⟩
def hS5 : HSpec := ⟨5, .isFirst * c "fin", true, [K 0], (fun j => c "dShN" j), 0⟩
def hS6 : HSpec := ⟨6, .isFirst, false, [], (fun j => c "dM" j), c "nbi"⟩
def hS7 : HSpec := ⟨7, .isFirst, false, [], (fun j => c "dMo" j), c "nbo"⟩
def hS8 : HSpec := ⟨8, .isFirst * c "cx", false, [], (fun j => SI.b "ctxRoot" j), c "nbc"⟩

def hashes : List HSpec := [hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]

/-- The number of blocks of a fixed message. -/
def nBlk (m : List Expr) : Nat := (padE m).length / 128

/-- Block `i` of a padded fixed message, as a byte function. -/
def blkE (m : List Expr) (i : Nat) : Nat → Expr := fun j => (padE m).getD (128 * i + j) 0

/-- **`SE`'s demands of one hash**: the blocks of a fixed message on `SHB`, the digest on `SHD`. -/
def hashIx (s : HSpec) : List Interaction :=
  if s.fx then
    ((List.range (nBlk s.msg)).map fun i => snd B_SHB s.mul (K s.hid :: K i :: Sh.limbs43 (blkE s.msg i))) ++
    [snd B_SHD s.mul ([K s.hid, K 1, K (nBlk s.msg - 1)] ++ Rb.limbs s.dig)]
  else [snd B_SHD s.mul ([K s.hid, K 0, s.nb] ++ Rb.limbs s.dig)]

/-- The byte columns of the opening rows (each `RNG`-checked on row 0). -/
def byteGroups : List (String × Nat) :=
  [("wsi", 48), ("wli", 8), ("tri", 32), ("ixi", 8), ("dS", 42), ("dQ", 42), ("dM", 42), ("dSo", 42),
   ("dQo", 42), ("dMo", 42), ("dK", 42), ("dSh", 42), ("dShN", 42)]

/-- **F-7 constraints** (row 0): the mode bits; finalize: tags `8 → 3`, the queue copied; otherwise
the static part copied. -/
def cons7 : List Expr :=
  [BndLay.gate (bool (c "fin")), BndLay.gate (bool (c "cx")), BndLay.gate (c "fin" * (c "tgi" - 8)),
   BndLay.gate (c "fin" * (c "tgo" - 3))] ++
  ((List.range 42).map fun j => BndLay.gate ((1 - c "fin") * (c "dSo" j - c "dS" j))) ++
  ((List.range 42).map fun j => BndLay.gate (c "fin" * (c "dQo" j - c "dQ" j)))

def cons : List Expr := cons5 ++ cons7

def interactions5 : List Interaction :=
  [snd B_STMQ .isFirst (Rb.limbs (SI.b "stRoot") ++ [c "tgo"] ++ Rb.limbs (fun j => c "rso" j)),
   rcv B_STMA .isFirst (Rb.limbs (SO.b "stRoot") ++ [c "tgi"] ++ Rb.limbs (fun j => c "rsi" j))] ++
  ((List.range 42).map fun j => rcv B_RNG .isFirst [c "rso" j]) ++
  ((List.range 42).map fun j => rcv B_RNG .isFirst [c "rsi" j]) ++
  -- F-6: every public value (both records, 900 B) is a byte, in-circuit
  pubBytes NUM_PUB

/-- **F-7 interactions**: the tags' ranges (`tag_in < 255`: `tag_in` and `tag_in + 1` are bytes), every opened / closed byte, the hashes. -/
def interactions7 : List Interaction :=
  [rcv B_RNG .isFirst [c "tgi" + 1], rcv B_RNG .isFirst [c "tgi"], rcv B_RNG .isFirst [c "tgo"]] ++
  (byteGroups.flatMap fun (s, w) => (List.range w).map fun j => rcv B_RNG .isFirst [c s j]) ++
  hashes.flatMap hashIx

def interactions : List Interaction := interactions5 ++ interactions7

def table : Table := { width := L.width, constraints := cons, interactions, maxLog := 2 }

def tableNames : List String := ["SE", "RNG", "SH"]

/-- The STATE engine half's leaf AIR (F-7: `[SE, RNG, SH, chip stub]`). -/
def seAir : Air := { tables := [table, Rng.table, Sh.table, chipStub], numBuses := NUM_BUSES_SE, numPub := NUM_PUB }

/-- The AIR the prover interprets: every Lean table but the chip stub (the native SHA-512 chip
replaces it, as in the resume leaf). -/
def exportAir : Air := { seAir with tables := seAir.tables.take 3 }

/-- With the public stand-in tape (Lean's view of the prover's `XTAPE`). -/
def fullSe (xtape : List (Nat × Bool × List Nat)) : Air :=
  { seAir with tables := seAir.tables ++ [tapeTable xtape] }

end Se

end M5T1
