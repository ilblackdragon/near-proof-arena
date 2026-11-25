import M5T1.Dsl

/-!
# M5T1.BndLay — the `rt` leaves' public values: the boundary pair in lane E's `BndRec` encoding

An `rt` segment (lane E's `Templates.lean`, `MRt`) proves one edge between two cut boundaries. Its
public values are **the two boundary records, byte for byte as `BndRec.encode` writes them**
(`Boundary.lean`: fixed-width big-endian `u64`/`u128`, 42-B digests, one-byte booleans, a
`u64`-counted digest list, a presence byte for the Wasm part), so the leaf wrapper hashes them
directly (`bdigest`) and the digests chain with the neighbouring segments.

* out of a call (`eng`, `phase 1`): `engF`, 450 B (F-3: the output-receipt accumulator is the
  singleton `[chainD enc rs]` of lane E's `outDE (.eng a)`, plan §3.5 G-3 item 2; no Wasm part);
* in a call (`call`, `phase 6`): `callF = engF ++ wasmF`, 834 B (F-3: `WasmBnd.gasLeft`, M11i).

The template's constraints on them (`enterCons`, `resumeCons`; `isFirst`-gated, so degree ≤ 2):

| field | `enter` (`eng I c → call I c [] q .pre`) | `resume` (`call I c K q (.fin r) → eng I c'`) |
|---|---|---|
| `phase`, `inCall`, Wasm tag | `1, 0, 0 → 6, 1, 1` | `6, 1, 1 → 1, 0, 0` |
| `t` | `0` out | carried |
| `gasUsed`, `gasBurnt`, `compute`, `balanceBurnt` | carried | in = the `RX` row's totals in, out = its totals out |
| `rPrepaid` | out free (named check: the query's, `EnterC.EntChecks.prepaid`) | in = the receipt's prepaid gas (`RX.gas`), carried |
| `rBurnt`, `rUsed` | carried | out = the VM's burnt / used gas (`RX.vb`, `RX.vu`) |
| `claimDigest`, indices, `stRoot`, `ctxRoot`, accumulators, `vmAcc` | carried | carried (**other lanes' components**, see below) |
| Wasm part | **F-3: lane A's `.pre` record** (`fbBnd`): counters `0`, digests `bdigest []`, `codeRoot = h ‖ 0^10` (S2; `h` = the code hash, named check `= SHA-256(q.code)`), `vmCtxDigest` free (named check) | in free (lane A: the `fin r` record) |

**Carried fields owned by other lanes.** In a real `resume` the state root (lane B's `stD`), the
outcome / outgoing-receipt accumulators (lanes B/G) and `vmAcc` (`vmD []` after the step) change;
no component computes them yet (lane I's driver: placeholders or the partial `StCommit`), so the
template carries them and the README lists each as an interface item (F-3: so `resume` cannot meet
lane E's relative obligation for any view whose `stD`/`outD` see the step — README §F-3).
`enter`'s input phase `1` does not exclude a finished engine (`eng I ⟨.done _, _⟩`, review-D7 I3):
the position is inside `stRoot`; F-3 makes it the named check `EntChecks.pos` (lane B's
`StCommit.rest` opening) with the view law `RtView.pos`.
-/

namespace M5T1.BndLay

open ZkFormal.Air

/-- The `BndRec` encoding out of a call (no Wasm part, a one-element output-receipt list). -/
def engF : Layout :=
  [("claimDigest", 42), ("phase", 8), ("blockIdx", 8), ("receiptIdx", 8), ("actionIdx", 8),
   ("inCall", 1), ("t", 8), ("stRoot", 42), ("ctxRoot", 42), ("gasUsed", 8), ("gasBurnt", 8),
   ("balanceBurnt", 16), ("compute", 8), ("rPrepaid", 8), ("rBurnt", 8), ("rUsed", 8),
   ("outcomeAcc", 42), ("outRcptN", 8), ("outRcpt0", 42), ("proposalsAcc", 42), ("bwAcc", 42),
   ("vmAcc", 42), ("wasmTag", 1)]

/-- The Wasm part (`WasmBnd`). -/
def wasmF : Layout :=
  [("pc", 8), ("sp", 8), ("stackRem", 8), ("fuel", 8), ("gasLeft", 8), ("framesDigest", 42), ("memRoot", 42),
   ("memPages", 8), ("globalsDigest", 42), ("registersDigest", 42), ("vmCtxDigest", 42),
   ("promisesDigest", 42), ("codeRoot", 42), ("funcRoot", 42)]

/-- The `BndRec` encoding in a call. -/
def callF : Layout := engF ++ wasmF

theorem engF_width : engF.width = 450 := by decide
theorem callF_width : callF.width = 834 := by decide

/-- The width of field `f` of a layout. -/
def fw : Layout → String → Nat
  | [], _ => 0
  | (n, k) :: r, s => if n == s then k else fw r s

/-- One side of a boundary: a record layout at public-value offset `base`. -/
structure Side where
  L : Layout
  base : Nat

/-- Byte `j` (in encoding order: big-endian) of field `f`. -/
def Side.b (S : Side) (f : String) (j : Nat) : Expr := .pub (S.base + S.L.off f + j)

/-- Little-endian byte `k` of field `f` (a `w`-byte big-endian number). -/
def Side.le (S : Side) (f : String) (k : Nat) : Expr := S.b f (fw S.L f - 1 - k)

def gate (e : Expr) : Expr := .isFirst * e

/-- Field `f` of `A` equals field `f` of `B`. -/
def copyF (A B : Side) (f : String) : List Expr :=
  (List.range (fw A.L f)).map fun j => gate (A.b f j - B.b f j)

/-- Field `f` is the constant `v` (big-endian). -/
def constF (A : Side) (f : String) (v : Nat) : List Expr :=
  let w := fw A.L f
  (List.range w).map fun k => gate (A.le f k - K (v / 256 ^ k % 256))

/-- Field `f` (little-endian byte `k`) equals `x k`, for `k < w`. -/
def eqLE (A : Side) (f : String) (x : Nat → Expr) : List Expr :=
  (List.range (fw A.L f)).map fun k => gate (A.le f k - x k)

/-- The fields both records carry unchanged in every `rt` edge. -/
def carried : List String :=
  ["claimDigest", "blockIdx", "receiptIdx", "actionIdx", "stRoot", "ctxRoot", "outcomeAcc",
   "outRcptN", "outRcpt0", "proposalsAcc", "bwAcc", "vmAcc"]

/-- How the `enter` leaf constrains one field of its output record (F-3). -/
inductive ORule where
  /-- equal to the input record's field of the same name -/
  | copy
  /-- a big-endian constant -/
  | num (v : Nat)
  /-- constant bytes -/
  | dig (b : List Nat)
  /-- not constrained by the rows (fixed by a named check of the leaf: `vmCtxDigest`, `rPrepaid`) -/
  | free
  /-- the first `n` bytes not constrained by the rows, the rest zero (`codeRoot`: S2) -/
  | pad (n : Nat)

/-- `bdigest []` = the first 42 bytes of `SHA-384("")` (the constant digests of lane A's fallback
record `fbBnd`; `EnterC.emptyDig_eq` proves it in the kernel). -/
def emptyDig : List Nat :=
  [0x38, 0xb0, 0x60, 0xa7, 0x51, 0xac, 0x96, 0x38, 0x4c, 0xd9, 0x32, 0x7e, 0xb1, 0xb1, 0xe3, 0x6a,
   0x21, 0xfd, 0xb7, 0x11, 0x14, 0xbe, 0x07, 0x43, 0x4c, 0x0c, 0xc7, 0xbf, 0x63, 0xf6, 0xe1, 0xda,
   0x27, 0x4e, 0xde, 0xbf, 0xe7, 0x6f, 0x65, 0xfb, 0xd5, 0x1a]

/-- **The `enter` edge's output record** (`eng I c → call I c [] q .pre`, F-3): `phase 6`,
`inCall 1`, clock `0`, the Wasm part present and equal to lane A's **`.pre` record** (`fbBnd`: every
counter `0`, every digest `bdigest []` except the remainder digest `vmCtxDigest`, and — S2 —
`codeRoot = SHA-256(q.code) ‖ 0^10`); `rPrepaid` and `vmCtxDigest` are the query's (named checks);
every other field is the input's. -/
def outRule : String → ORule
  | "phase" => .num 6 | "inCall" => .num 1 | "t" => .num 0 | "wasmTag" => .num 1
  | "rPrepaid" => .free | "vmCtxDigest" => .free | "codeRoot" => .pad 32
  | "pc" => .num 0 | "sp" => .num 0 | "stackRem" => .num 0 | "fuel" => .num 0 | "gasLeft" => .num 0
  | "memPages" => .num 0
  | "framesDigest" => .dig emptyDig | "memRoot" => .dig emptyDig | "globalsDigest" => .dig emptyDig
  | "registersDigest" => .dig emptyDig | "promisesDigest" => .dig emptyDig
  | "funcRoot" => .dig emptyDig
  | _ => .copy

/-- The constraints of one output field. -/
def ruleCons (I O : Side) (f : String) (w : Nat) : ORule → List Expr
  | .copy => copyF I O f
  | .num v => constF O f v
  | .dig b => (List.range w).map fun j => gate (O.b f j - K (b.getD j 0))
  | .free => []
  | .pad n => (List.range (w - n)).map fun j => gate (O.b f (n + j))

/-- **`enter`** (F-3): `in` out of a call (`engF`: phase 1, `inCall 0`, no Wasm part), `out` in a
call (`callF`, by `outRule`). -/
def enterCons (I O : Side) : List Expr :=
  constF I "phase" 1 ++ constF I "inCall" 0 ++ constF I "wasmTag" 0 ++
  callF.flatMap fun p => ruleCons I O p.1 p.2 (outRule p.1)

/-- **`resume`**: `in` in a call (`callF`), `out` out of a call (`engF`); the receipt step's values
come from the `RX` row (`x g k`: little-endian byte `k` of `RX` group / public group `g`). -/
def resumeCons (I O : Side) (pubG colG : String → Nat → Expr) : List Expr :=
  constF I "phase" 6 ++ constF I "inCall" 1 ++ constF I "wasmTag" 1 ++
  constF O "phase" 1 ++ constF O "inCall" 0 ++ constF O "wasmTag" 0 ++
  (carried ++ ["t", "rPrepaid"]).flatMap (copyF I O) ++
  eqLE I "gasUsed" (pubG "gin") ++ eqLE I "gasBurnt" (pubG "gin") ++ eqLE I "compute" (pubG "cin") ++
  eqLE I "balanceBurnt" (pubG "tbin") ++
  eqLE O "gasUsed" (pubG "gout") ++ eqLE O "gasBurnt" (pubG "gout") ++ eqLE O "compute" (pubG "cout") ++
  eqLE O "balanceBurnt" (pubG "tbout") ++
  eqLE I "rPrepaid" (colG "gas") ++ eqLE O "rBurnt" (colG "vb") ++ eqLE O "rUsed" (colG "vu")

end M5T1.BndLay
