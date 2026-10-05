import ZkFormal.Sha.Eval
import ZkFormal.Sha.Table
import ZkFormal.Sha.Gen

/-!
# ZkFormal.Sha.View — `Nat` views of a SHA-table trace

Decoded quantities the soundness statements talk about: cell values as
naturals, bit-decomposed words, the chaining state of a state row, the 64
block bytes of a block, the message chain ending at a digest row, its data
bytes, and the list `digests tr t` of `(message, digest)` pairs the table
claims.
-/

namespace ZkFormal.Sha.View

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout

variable (tr : Trace Fp) (t : Nat)

/-- Cell `(r, c)` of table `t` as a natural. -/
def nv (r c : Nat) : Nat := (tr.cell t r c).toNat

/-- `Σ_{b<n} 2^b · f b`. -/
def ofBits (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ofBits f n + 2 ^ n * f n

/-- 32-bit word stored in bit columns `col 0 … col 31` of row `r`. -/
def wordAt (r : Nat) (col : Nat → Nat) : Nat := ofBits (fun b => nv tr t r (col b)) 32

/-- Chaining state (`a..h`) of a state row (or of the last round row). -/
def stateAt (r : Nat) : List Nat := (List.range 8).map fun w => wordAt tr t r (colSt w)

/-- Byte `q < 16` of round row `r` (big-endian bytes of `W 0..3`). -/
def byteAt (r q : Nat) : Nat := wordAt tr t r (colW (q / 4)) / 2 ^ (8 * (3 - q % 4)) % 256

/-- The 64 bytes of the block whose `R0` row is `s`. -/
def blockBytes (s : Nat) : List Nat := (List.range 64).map fun kk => byteAt tr t (s + kk / 16) (kk % 16)

/-- Data bytes of the block starting at `s` (those with data flag `1`). -/
def blockData (s : Nat) : List Nat :=
  (List.range 64).filterMap fun kk =>
    if nv tr t (s + kk / 16) (colF (kk % 16)) = 1 then some (byteAt tr t (s + kk / 16) (kk % 16)) else none

/-- `D` row with `Last = 1`: the end of a message. -/
def IsDigestRow (d : Nat) : Prop := nv tr t d colD = 1 ∧ nv tr t d colLast = 1

instance (d : Nat) : Decidable (IsDigestRow tr t d) := by unfold IsDigestRow; infer_instance

/-- Block starts (`R0` rows) of the message whose last block's `D` row is
`d`, walking back through `D` rows (`fuel` bounds the walk). -/
def chainStarts : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, d =>
    if nv tr t (d - 17) colD = 1 ∧ 17 ≤ d then chainStarts fuel (d - 17) ++ [d - 16] else [d - 16]

/-- The message chain ending at digest row `d`. -/
def chainOf (d : Nat) : List Nat := chainStarts tr t (tr.height t) d

/-- The message hashed by the chain ending at `d`. -/
def msgOf (d : Nat) : List Nat := (chainOf tr t d).flatMap (blockData tr t)

/-- `(message, digest)` pairs claimed by the table. -/
def digests : List (ArenaCore.Bytes × ArenaCore.Bytes) :=
  ((List.range (tr.height t)).filter fun d => decide (IsDigestRow tr t d)).map fun d =>
    ((msgOf tr t d).map UInt8.ofNat, ArenaCore.SHA256.digestBytes (stateAt tr t d))

end ZkFormal.Sha.View
