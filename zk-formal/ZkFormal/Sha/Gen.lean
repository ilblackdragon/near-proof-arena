import ZkFormal.Sha.Spec
import ZkFormal.Sha.Layout

/-!
# ZkFormal.Sha.Gen — the honest trace of the SHA-256 block table

`honestRows msgs` lays out every message `(id, bytes, dmult)` as one `S` row
followed by `R0..R15, D` for each block of `pad bytes`, and `honestCell` gives
every cell as a `Nat` (all values are `< 2^17`, so the field embedding is
injective on them).  The definitions read the `Nat`-level spec of
ZkFormal.Sha.Spec directly, so completeness proofs unfold to spec facts.

This is also the reference for lane L8's Rust trace generator: the cell
formulas below are the specification, column by column.
-/

namespace ZkFormal.Sha.Gen

open ArenaCore ArenaCore.SHA256 ZkFormal.Sha.Spec ZkFormal.Sha.Layout

/-- One message: identifier, bytes (as `Nat`s `< 256`), digest-bus multiplicity. -/
structure Msg where
  id : Nat
  bytes : List Nat
  dmult : Nat

/-- Block `b` of a message (all the data the rows of the block depend on). -/
structure Blk where
  id : Nat
  /-- message length in bytes -/
  len : Nat
  /-- block index within the message -/
  idx : Nat
  /-- number of blocks of the message -/
  nblk : Nat
  /-- chaining value (8 words) -/
  hin : List Nat
  /-- the 64 padded bytes of this block -/
  blk : List Nat
  dmult : Nat

/-- Row descriptors. -/
inductive Row where
  | start (id : Nat)
  | round (j : Nat) (B : Blk)
  | digest (B : Blk)
  | pad

def chunks : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, l => l.take 64 :: chunks n (l.drop 64)

/-- Padded 64-byte blocks of a message. -/
def msgBlocks (m : List Nat) : List (List Nat) := chunks ((pad m).length / 64) (pad m)

def blkOf (M : Msg) (b : Nat) : Blk :=
  let bs := msgBlocks M.bytes
  { id := M.id, len := M.bytes.length, idx := b, nblk := bs.length,
    hin := (bs.take b).foldl compress H0, blk := bs.getD b [], dmult := M.dmult }

def msgRows (M : Msg) : List Row :=
  .start M.id ::
    (List.range (msgBlocks M.bytes).length).flatMap fun b =>
      (List.range 16).map (fun j => Row.round j (blkOf M b)) ++ [Row.digest (blkOf M b)]

def honestRows (msgs : List Msg) : List Row := msgs.flatMap msgRows

/-- Smallest `log` with `n ≤ 2^log`. -/
def clog2 (n : Nat) : Nat := go n 0 where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | fuel + 1, acc => if n ≤ 2 ^ acc then acc else go fuel (acc + 1)

/-! ## Cell values -/

def bit (x b : Nat) : Nat := (x / 2 ^ b) % 2
def lo16 (x : Nat) : Nat := x % 65536
def hi16 (x : Nat) : Nat := x / 65536
def limbN (x l : Nat) : Nat := if l = 0 then lo16 x else hi16 x

/-- Carry out of limb `l` of the sum of `xs` (limb-wise, low limb first). -/
def carry (xs : List Nat) (l : Nat) : Nat :=
  let c0 := (xs.map lo16).sum / 65536
  if l = 0 then c0 else ((xs.map hi16).sum + c0) / 65536

namespace Blk
variable (B : Blk)
def A (u : Nat) : Nat := As B.hin B.blk u
def Ee (u : Nat) : Nat := Es B.hin B.blk u
def W (t : Nat) : Nat := Wt B.blk t
/-- Byte `p` of the message is data / the in-block data flag. -/
def isData (kk : Nat) : Bool := 64 * B.idx + kk < B.len
def last : Bool := B.idx + 1 == B.nblk
def p80 : Bool := 64 * B.idx ≤ B.len && B.len < 64 * B.idx + 64
def seen : Bool := B.len < 64 * B.idx
/-- Terms of the `a` addition of round `t`. -/
def termsA (t : Nat) : List Nat :=
  [B.Ee t, bsig1 (B.Ee (t + 3)), ch (B.Ee (t + 3)) (B.Ee (t + 2)) (B.Ee (t + 1)), Kt t, B.W t,
   bsig0 (B.A (t + 3)), maj (B.A (t + 3)) (B.A (t + 2)) (B.A (t + 1))]
def termsE (t : Nat) : List Nat :=
  [B.A t, B.Ee t, bsig1 (B.Ee (t + 3)), ch (B.Ee (t + 3)) (B.Ee (t + 2)) (B.Ee (t + 1)), Kt t, B.W t]
/-- Schedule helper `σ₀(W_{m+1}) + W_m`, limb `l` (stored unreduced). -/
def help (m l : Nat) : Nat := limbN (ssig0 (B.W (m + 1))) l + limbN (B.W m) l
/-- Limb-terms of the schedule addition for word `t ≥ 16`. -/
def schedCarry (t l : Nat) : Nat :=
  let c0 := (lo16 (ssig1 (B.W (t - 2))) + lo16 (B.W (t - 7)) + B.help (t - 16) 0) / 65536
  if l = 0 then c0 else (hi16 (ssig1 (B.W (t - 2))) + hi16 (B.W (t - 7)) + B.help (t - 16) 1 + c0) / 65536
/-- Final working variable for state word `w`. -/
def fin (w : Nat) : Nat := if w < 4 then B.A (67 - w) else B.Ee (71 - w)
def hout (w : Nat) : Nat := add32 (B.hin.getD w 0) (B.fin w)
/-- Message bytes counted through row `Rj` (`j < 4`) / through the block. -/
def ndRow (j : Nat) : Nat := min B.len (64 * B.idx + 16 * (min j 3 + 1))
end Blk

/-- State word `w` of the IV. -/
def ivW (w : Nat) : Nat := H0.getD w 0

/-- Cell `col` of a start row. -/
def startCell (id col : Nat) : Nat :=
  if col < 256 then
    -- colSt w b ↔ col: A slot i = word 3-i, E slot i = word 7-i
    if col < 128 then bit (ivW (3 - col / 32)) (col % 32) else bit (ivW (7 - (col - 128) / 32)) (col % 32)
  else if col = colS then 1
  else if col = colId then id
  else 0

/-- Cell `col` of round row `Rj` of block `B`. -/
def roundCell (j : Nat) (B : Blk) (col : Nat) : Nat :=
  let t0 := 4 * j
  if col < 128 then bit (B.A (t0 + 4 + col / 32)) (col % 32)
  else if col < 256 then bit (B.Ee (t0 + 4 + (col - 128) / 32)) (col % 32)
  else if col < 384 then bit (B.W (t0 + (col - 256) / 32)) (col % 32)
  else if col < 408 then
    let i := (col - 384) / 6; let l := (col - 384) % 6 / 3; let k := (col - 384) % 3
    bit (carry (B.termsA (t0 + i)) l) k
  else if col < 432 then
    let i := (col - 408) / 6; let l := (col - 408) % 6 / 3; let k := (col - 408) % 3
    bit (carry (B.termsE (t0 + i)) l) k
  else if col < 456 then
    let i := (col - 432) / 6; let l := (col - 432) % 6 / 3; let k := (col - 432) % 3
    if 4 ≤ j then bit (B.schedCarry (t0 + i) l) k else 0
  else if col < 480 then
    -- I4 / I8 / I12: helper for words of row j+3, j+2, j+1 (computed on row j-1, j-2, j-3)
    let d := (col - 456) / 8 + 1; let i := (col - 456) % 8 / 2; let l := (col - 456) % 2
    if d ≤ j then B.help (4 * (j - d) + i) l else 0
  else if col < 486 then
    let i := (col - 480) / 2; let l := (col - 480) % 2
    if 1 ≤ j then limbN (B.W (4 * (j - 1) + i + 1)) l else 0
  else if col < 502 then limbN (B.hin.getD ((col - 486) / 2) 0) ((col - 486) % 2)
  else if col < 518 then (if col - 502 = j then 1 else 0)
  else if col < 520 then 0
  else if col < 536 then (if j < 4 && B.isData (16 * j + (col - 520)) then 1 else 0)
  else if col = colFprev then (if j = 0 then 1 else if j < 4 && B.isData (16 * j - 1) then 1 else 0)
  else if col = colNd then B.ndRow j
  else if col = colId then B.id
  else if col = colLast then (if B.last then 1 else 0)
  else if col = colP80 then (if B.p80 then 1 else 0)
  else if col = colSeen then (if B.seen then 1 else 0)
  else if col = colPn then (if B.p80 && !B.last then 1 else 0)
  else 0

/-- Cell `col` of the digest row of block `B`. -/
def digestCell (B : Blk) (col : Nat) : Nat :=
  if col < 128 then bit (B.hout (3 - col / 32)) (col % 32)
  else if col < 256 then bit (B.hout (7 - (col - 128) / 32)) (col % 32)
  else if 384 ≤ col ∧ col < 432 then
    -- carries of the final addition: CA slot i ↔ word 3-i, CE slot i ↔ word 7-i
    let isE := decide (408 ≤ col); let off := if isE then col - 408 else col - 384
    let i := off / 6; let l := off % 6 / 3; let k := off % 3
    let w := if isE then 7 - i else 3 - i
    bit (carry [B.hin.getD w 0, B.fin w] l) k
  else if col = colD then 1
  else if col = colNd then B.ndRow 4
  else if col = colId then B.id
  else if col = colLast then (if B.last then 1 else 0)
  else if col = colP80 then (if B.p80 then 1 else 0)
  else if col = colSeen then (if B.seen then 1 else 0)
  else if col = colPn then (if B.p80 && !B.last then 1 else 0)
  else if col = colDmult then (if B.last then B.dmult else 0)
  else 0

def rowCell : Row → Nat → Nat
  | .start id, col => startCell id col
  | .round j B, col => roundCell j B col
  | .digest B, col => digestCell B col
  | .pad, _ => 0

/-- The honest table: `log` and `cell r col`. -/
def honestLog (msgs : List Msg) : Nat := clog2 (honestRows msgs).length

def honestCell (msgs : List Msg) (r col : Nat) : Nat :=
  rowCell ((honestRows msgs).getD r .pad) col

/-! ## Expected bus traffic -/

/-- Bytes received: `(id, pos, byte)` for every message byte. -/
def expectedBytes (msgs : List Msg) : List (List Nat) :=
  msgs.flatMap fun M => (List.range M.bytes.length).map fun p => [M.id, p, M.bytes.getD p 0]

/-- Digests provided: `((id, len, sha256 bytes), dmult)`. -/
def expectedDigests (msgs : List Msg) : List (List Nat × Nat) :=
  msgs.map fun M =>
    ([M.id, M.bytes.length] ++ (sha256 (M.bytes.map UInt8.ofNat)).map UInt8.toNat, M.dmult)

end ZkFormal.Sha.Gen
