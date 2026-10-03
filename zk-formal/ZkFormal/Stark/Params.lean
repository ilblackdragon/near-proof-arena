/-!
# ZkFormal.Stark.Params — protocol parameters of `np-udr-stark-v1`

Defaults are the DESIGN.md §8 "UDR2" set: rate `1/16`, 216 queries
(24 oracle answers × 9 positions of 26 bits), binary folds committed with
arity ≤ 8, final polynomial of degree `< 2`, largest LDE domain `2^26`.
The kernel-checked security budget for these values is
`ZkFormal.Params.udr2_ok`.
-/

namespace ZkFormal.Stark

structure Params where
  /-- `log₂` of the blowup (rate `2^-logBlowup`). -/
  logBlowup : Nat := 4
  /-- Number of query-phase oracle answers ("chunks"). -/
  numChunks : Nat := 24
  /-- Positions per chunk. -/
  posPerChunk : Nat := 9
  /-- Bits per position (`posPerChunk · posBits ≤ 256`; positions are
  reduced mod the query domain size `2^n0 ≤ 2^posBits`). -/
  posBits : Nat := 26
  /-- `log₂` of the maximal FRI commitment arity (8). -/
  maxArityLog : Nat := 3
  /-- `log₂` of the final polynomial's degree bound (`deg < 2`). -/
  finalLog : Nat := 1
  /-- Largest admissible `log₂` of an LDE domain. -/
  maxLogLde : Nat := 26
  /-- Proofs longer than this are rejected before parsing (8 MiB). -/
  maxProofBytes : Nat := 8 * 2 ^ 20
  /-- Interactions per running-product (aux) column. -/
  auxGroup : Nat := 1
  deriving Repr, DecidableEq

/-- The deployed parameter set. -/
def Params.default : Params := {}

/-- `log₂` of the smallest admissible trace height: the smallest LDE domain
must still hold the final layer (`logBlowup + finalLog`), i.e. trace heights
are at least `2^minLog`. -/
def Params.minLog (prm : Params) : Nat := prm.finalLog

end ZkFormal.Stark
