import M5T1.Air

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
-/

namespace M5T1

open ZkFormal.Air

namespace Se

def L : Layout := [("tgo", 1), ("rso", 42), ("tgi", 1), ("rsi", 42)]
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

/-- **`SE`'s constraints** (row 0): input an engine record, output by `seRule`, `gasUsed =
gasBurnt` out. -/
def cons : List Expr :=
  BndLay.constF SI "phase" 1 ++ BndLay.constF SI "inCall" 0 ++ BndLay.constF SI "wasmTag" 0 ++
  (BndLay.engF.flatMap fun p => BndLay.ruleCons SI SO p.1 p.2 (seRule p.1)) ++
  (List.range 8).map fun j => BndLay.gate (SO.b "gasUsed" j - SO.b "gasBurnt" j)

def interactions : List Interaction :=
  [snd B_STMQ .isFirst (Rb.limbs (SI.b "stRoot") ++ [c "tgo"] ++ Rb.limbs (fun j => c "rso" j)),
   rcv B_STMA .isFirst (Rb.limbs (SO.b "stRoot") ++ [c "tgi"] ++ Rb.limbs (fun j => c "rsi" j))] ++
  ((List.range 42).map fun j => rcv B_RNG .isFirst [c "rso" j]) ++
  ((List.range 42).map fun j => rcv B_RNG .isFirst [c "rsi" j]) ++
  -- F-6: every public value (both records, 900 B) is a byte, in-circuit
  pubBytes NUM_PUB

def table : Table := { width := L.width, constraints := cons, interactions, maxLog := 2 }

def tableNames : List String := ["SE", "RNG"]

/-- The STATE engine half's leaf AIR (exported; the prover adds `XTAPE`). -/
def seAir : Air := { tables := [table, Rng.table], numBuses := NUM_BUSES, numPub := NUM_PUB }

/-- With the public stand-in tape (Lean's view of the prover's `XTAPE`). -/
def fullSe (xtape : List (Nat × Bool × List Nat)) : Air :=
  { seAir with tables := seAir.tables ++ [tapeTable xtape] }

end Se

end M5T1
