import M5T1.Dsl

/-!
# M5T1.BndLay — the `rt` leaves' public values: the boundary pair in lane E's `BndRec` encoding

An `rt` segment (lane E's `Templates.lean`, `MRt`) proves one edge between two cut boundaries. Its
public values are **the two boundary records, byte for byte as `BndRec.encode` writes them**
(`Boundary.lean`: fixed-width big-endian `u64`/`u128`, 42-B digests, one-byte booleans, a
`u64`-counted digest list, a presence byte for the Wasm part), so the leaf wrapper hashes them
directly (`bdigest`) and the digests chain with the neighbouring segments.

* out of a call (`eng`, `phase 1`): `engF`, 408 B (the output-receipt list empty, no Wasm part);
* in a call (`call`, `phase 6`): `callF = engF ++ wasmF`, 784 B.

The template's constraints on them (`enterCons`, `resumeCons`; `isFirst`-gated, so degree ≤ 2):

| field | `enter` (`eng I c → call I c [] q .pre`) | `resume` (`call I c K q (.fin r) → eng I c'`) |
|---|---|---|
| `phase`, `inCall`, Wasm tag | `1, 0, 0 → 6, 1, 1` | `6, 1, 1 → 1, 0, 0` |
| `t` | `0` out | carried |
| `gasUsed`, `gasBurnt`, `compute`, `balanceBurnt` | carried | in = the `RX` row's totals in, out = its totals out |
| `rPrepaid` | out free (checked at `resume`) | in = the receipt's prepaid gas (`RX.gas`), carried |
| `rBurnt`, `rUsed` | carried | out = the VM's burnt / used gas (`RX.vb`, `RX.vu`) |
| `claimDigest`, indices, `stRoot`, `ctxRoot`, accumulators, `vmAcc` | carried | carried (**other lanes' components**, see below) |
| Wasm part | out free (lane A / PREP: the `.pre` record) | in free (lane A: the `fin r` record) |

**Carried fields owned by other lanes.** In a real `resume` the state root (lane B's `stD`), the
outcome / outgoing-receipt accumulators (lanes B/G) and `vmAcc` (`vmD []` after the step) change;
no component computes them yet (lane I's driver: placeholders or the partial `StCommit`), so the
template carries them and the README lists each as an interface item. `enter`'s input phase `1`
does not exclude a finished engine (`eng I ⟨.done _, _⟩`, review-D7 I3): the position is inside
`stRoot`; also an interface item (lane B's `StCommit.rest` opening).
-/

namespace M5T1.BndLay

open ZkFormal.Air

/-- The `BndRec` encoding out of a call (no Wasm part, empty output-receipt list). -/
def engF : Layout :=
  [("claimDigest", 42), ("phase", 8), ("blockIdx", 8), ("receiptIdx", 8), ("actionIdx", 8),
   ("inCall", 1), ("t", 8), ("stRoot", 42), ("ctxRoot", 42), ("gasUsed", 8), ("gasBurnt", 8),
   ("balanceBurnt", 16), ("compute", 8), ("rPrepaid", 8), ("rBurnt", 8), ("rUsed", 8),
   ("outcomeAcc", 42), ("outRcptN", 8), ("proposalsAcc", 42), ("bwAcc", 42), ("vmAcc", 42),
   ("wasmTag", 1)]

/-- The Wasm part (`WasmBnd`). -/
def wasmF : Layout :=
  [("pc", 8), ("sp", 8), ("stackRem", 8), ("fuel", 8), ("framesDigest", 42), ("memRoot", 42),
   ("memPages", 8), ("globalsDigest", 42), ("registersDigest", 42), ("vmCtxDigest", 42),
   ("promisesDigest", 42), ("codeRoot", 42), ("funcRoot", 42)]

/-- The `BndRec` encoding in a call. -/
def callF : Layout := engF ++ wasmF

theorem engF_width : engF.width = 408 := by decide
theorem callF_width : callF.width = 784 := by decide

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
   "outRcptN", "proposalsAcc", "bwAcc", "vmAcc"]

/-- **`enter`**: `in` out of a call (`engF`), `out` in a call (`callF`). -/
def enterCons (I O : Side) : List Expr :=
  constF I "phase" 1 ++ constF I "inCall" 0 ++ constF I "wasmTag" 0 ++
  constF O "phase" 6 ++ constF O "inCall" 1 ++ constF O "wasmTag" 1 ++ constF O "t" 0 ++
  (carried ++ ["gasUsed", "gasBurnt", "balanceBurnt", "compute", "rBurnt", "rUsed"]).flatMap
    (copyF I O)

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
