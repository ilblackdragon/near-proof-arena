import M5T1.Acc

/-!
# M5T1.Sh — `SH`: the STATE engine half's SHA-384 hashes (F-7)

`ACC` (F-4) generalised: **one row per 128-byte SHA-512 compression block**, through the native
SHA-512 compression chip on `IF384` (lane B's `Sha512If`, the same limb layout and word splits as
`ACC`), a hash being a run of active rows from a `fst` row (chaining value `IV384`, block index
`bi = 0`) to a `lst` row (`bi` = the number of blocks − 1), each next row chaining the previous
row's output and incrementing `bi`; `hid`, `fx` constant along the run. What `ACC` bound to public
accumulators, `SH` binds to the `SE` row over two buses:

* **`SHD [hid, fx, bi, 14 limbs of dg[0..42)]`** — received by every `lst` row: the hash's id, its
  kind, its last block index and its 42-byte (truncated SHA-384) digest. `SE` sends one per hash it
  needs (`Se.hashes`), so each demanded hash has a run ending in a `lst` row with that digest.
* **`SHB [hid, bi, 43 limbs of blk]`** — received by every active row of a **fixed-content** run
  (`fx = 1`): its block. `SE` sends the padded message's blocks (`Se.padE`), so a fixed run's
  message *is* `SE`'s padded bytes. A witnessed run (`fx = 0`: the `d_move` preimages, the intake)
  receives nothing: its message is free bytes (`RNG`-checked), bound only by its digest.

Limbs: a block limb `j < 42` is bytes `3j, 3j+1, 3j+2` big-endian (`< 2^24`), limb 42 is bytes 126,
127; a digest limb `j < 14` as `Rb.limbs`.
-/

namespace M5T1

open ZkFormal.Air

namespace Sh

def L : Layout :=
  [("act", 1), ("fst", 1), ("lst", 1), ("hid", 1), ("cid", 1), ("fx", 1), ("bi", 1), ("blk", 128),
   ("bsp", 64), ("h", 24), ("o", 24), ("dg", 48), ("dsp", 24)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def n (s : String) (j : Nat := 0) : Expr := T.n s j

/-- 43 limbs of 128 byte expressions (`3j, 3j+1, 3j+2` big-endian; the last limb bytes 126, 127). -/
def limbs43 (b : Nat → Expr) : List Expr :=
  (List.range 43).map fun j =>
    if j < 42 then K 65536 * b (3 * j) + K 256 * b (3 * j + 1) + b (3 * j + 2)
    else K 256 * b 126 + b 127

def blkB : Nat → Expr := fun j => c "blk" j
def blkS : Nat → Expr := fun j => c "bsp" j
def dgB : Nat → Expr := fun j => c "dg" j
def dgS : Nat → Expr := fun j => c "dsp" j

def limbW (s : String) (t : Nat) : Acc.W3 := (c s (3 * t), c s (3 * t + 1), c s (3 * t + 2))
def blockW : List Acc.W3 := (List.range 16).map (Acc.wordOf blkB blkS)
def hW : List Acc.W3 := (List.range 8).map (limbW "h")
def oW : List Acc.W3 := (List.range 8).map (limbW "o")

/-- The transition gate: the next row is active and not first (it continues this row's hash). -/
def gN : Expr := n "act" * (1 - n "fst")

def constraints : List Expr :=
  let act := c "act"; let fst := c "fst"; let lst := c "lst"
  (["act", "fst", "lst", "fx"].map fun s => bool (c s)) ++
  [(1 - act) * fst, (1 - act) * lst, .isFirst * act * (1 - fst)] ++
  ((List.range 16).flatMap (Acc.splitCons blkB blkS)) ++
  ((List.range 6).flatMap (Acc.splitCons dgB dgS)) ++
  -- a hash starts from SHA-384's IV, at block 0
  ((List.range 24).map fun l => fst * (c "h" l - K ((Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0))) ++
  [fst * c "bi"] ++
  -- its last row's output words 0..5 are `dg` (48 big-endian bytes)
  ((List.range 6).flatMap fun t =>
    let (a0, a1, a2) := Acc.wordOf dgB dgS t
    [lst * (a0 - c "o" (3 * t)), lst * (a1 - c "o" (3 * t + 1)), lst * (a2 - c "o" (3 * t + 2))]) ++
  -- inside a hash: the previous row is active, not last, same `hid` / `fx`, next block, and chains
  [.isTransition * gN * (1 - act), .isTransition * gN * lst, .isTransition * gN * (n "hid" - c "hid"),
   .isTransition * gN * (n "fx" - c "fx"), .isTransition * gN * (n "bi" - c "bi" - 1)] ++
  ((List.range 24).map fun l => .isTransition * gN * (n "h" l - c "o" l))

def dgLimbs : List Expr := (List.range 14).map (Rb.limb dgB)

def interactions : List Interaction :=
  let act := c "act"; let lst := c "lst"
  Acc.comp act (c "cid") (hW ++ blockW ++ oW) ++
  [rcv B_SHD lst ([c "hid", c "fx", c "bi"] ++ dgLimbs),
   rcv B_SHB (act * c "fx") (c "hid" :: c "bi" :: limbs43 blkB)] ++
  ((List.range 128).map fun j => rcv B_RNG act [c "blk" j]) ++
  ((List.range 16).flatMap (Acc.splitRng act blkS)) ++
  ((List.range 48).map fun j => rcv B_RNG lst [c "dg" j]) ++
  ((List.range 6).flatMap (Acc.splitRng lst dgS))

def table : Table := { width := L.width, constraints, interactions, maxLog := 16 }

end Sh

end M5T1
