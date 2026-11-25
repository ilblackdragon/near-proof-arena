import M5T1.Rb

/-!
# M5T1.Acc — `ACC`: the resume edge's SHA-384 accumulator appends (F-4)

Lane E's output commitment of an engine state is `outDE (.eng (os, rs, ps)) = (chainD Ser.enc os,
[chainD Ser.enc rs], …)`, and appending one item is one SHA-384: `chainD (os ++ [o]) =
bdigest (chainD os ‖ Ser.enc o)`. The resume edge appends the receipt's outcome to `outcomeAcc`
(`hid = 0`) and its outgoing (refund) receipt to `outRcpt0` (`hid = 1`). `ACC` computes both
in-circuit, **one row per 128-byte SHA-512 compression block**, through the native SHA-512
compression chip on `IF384` (lane B's interface `Sha512If`: 16 messages `(cid, pair, limbs(w₂ₘ),
limbs(w₂ₘ₊₁))` over `h ‖ block ‖ compress(h, block)`, limbs `[0,21) [21,42) [42,64)`):

* a hash is a run of active rows from a `fst` row to a `lst` row with one `hid`; the `fst` row's
  chaining value is SHA-384's `IV384`, each next row's chaining value is the previous row's output
  (`h' = o`), and **the first 42 message bytes are the input record's accumulator**
  (`B_in.outcomeAcc` / `B_in.outRcpt0`, public);
* the `lst` row's output words 0..5, as 48 big-endian bytes (`dg`), truncated to 42, **are the
  output record's accumulator** (`B_out.outcomeAcc` / `B_out.outRcpt0`, public);
* each `lst` row receives `ACCD [hid]`, which `RB` sends once per `hid`, so each accumulator has
  exactly one hash.

The block bytes after the 42-byte prefix (the item `Ser.enc o` / `Ser.enc rr` and SHA-512's
padding) are witnessed and `RNG`-checked; that they are `pad (acc ‖ Ser.enc item)` of the step's
item is the resume leaf's named premise (`ResumeC`: no in-circuit `Ser.enc` encoder yet).

Bytes → words: a word is 8 big-endian bytes `β₀..β₇`; with `Bᵢ = β₇₋ᵢ` its limbs are
`B₀ + 2^8 B₁ + 2^16 s₀`, `s₁ + 2^3 B₃ + 2^11 B₄ + 2^19 s₂`, `s₃ + 2^6 B₆ + 2^14 B₇` with the
splits `B₂ = s₀ + 2^5 s₁`, `B₅ = s₂ + 2^2 s₃` (each split range-checked by two `RNG` lookups:
`s` and `2^(8−k) s` below 256).
-/

namespace M5T1

open ZkFormal.Air

namespace Acc

/-- SHA-384 initial hash value (FIPS 180-4 §5.3.4; `Bnd.IV384`). -/
def IV384 : List Nat :=
  [0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
   0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- The chip's limbs of a 64-bit word (lane B's `Ws.wlimbs`). -/
def wlimbs (x : Nat) : List Nat := [x % 2 ^ 21, x / 2 ^ 21 % 2 ^ 21, x / 2 ^ 42]

def L : Layout :=
  [("act", 1), ("fst", 1), ("lst", 1), ("hid", 1), ("cid", 1), ("blk", 128), ("bsp", 64),
   ("h", 24), ("o", 24), ("dg", 48), ("dsp", 24)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def n (s : String) (j : Nat := 0) : Expr := T.n s j

/-- A word as three limb expressions. -/
abbrev W3 := Expr × Expr × Expr

/-- Word `w` of 8 big-endian byte columns `b (8w) .. b (8w+7)` with its 4 split columns
`s (4w) .. s (4w+3)`. -/
def wordOf (b s : Nat → Expr) (w : Nat) : W3 :=
  let B (i : Nat) : Expr := b (8 * w + 7 - i)
  (B 0 + K 256 * B 1 + K 65536 * s (4 * w),
   s (4 * w + 1) + K 8 * B 3 + K 2048 * B 4 + K 524288 * s (4 * w + 2),
   s (4 * w + 3) + K 64 * B 6 + K 16384 * B 7)

/-- The split constraints of word `w`. -/
def splitCons (b s : Nat → Expr) (w : Nat) : List Expr :=
  [b (8 * w + 5) - s (4 * w) - K 32 * s (4 * w + 1), b (8 * w + 2) - s (4 * w + 2) - K 4 * s (4 * w + 3)]

/-- The split range checks of word `w` (`s₀ < 32`, `s₁ < 8`, `s₂ < 4`, `s₃ < 64`). -/
def splitRng (g : Expr) (s : Nat → Expr) (w : Nat) : List Interaction :=
  [rcv B_RNG g [s (4 * w)], rcv B_RNG g [K 8 * s (4 * w)],
   rcv B_RNG g [s (4 * w + 1)], rcv B_RNG g [K 32 * s (4 * w + 1)],
   rcv B_RNG g [s (4 * w + 2)], rcv B_RNG g [K 64 * s (4 * w + 2)],
   rcv B_RNG g [s (4 * w + 3)], rcv B_RNG g [K 4 * s (4 * w + 3)]]

def blkB : Nat → Expr := fun j => c "blk" j
def blkS : Nat → Expr := fun j => c "bsp" j
def dgB : Nat → Expr := fun j => c "dg" j
def dgS : Nat → Expr := fun j => c "dsp" j

def limbW (s : String) (t : Nat) : W3 := (c s (3 * t), c s (3 * t + 1), c s (3 * t + 2))
def blockW : List W3 := (List.range 16).map (wordOf blkB blkS)
def hW : List W3 := (List.range 8).map (limbW "h")
def oW : List W3 := (List.range 8).map (limbW "o")

/-- The 16 interface receives of one compression `(h_in 8 words, block 16, h_out 8)` (lane B's
`Ws.comp`). -/
def comp (g cid : Expr) (ws : List W3) : List Interaction :=
  (List.range 16).map fun m =>
    let (a0, a1, a2) := ws.getD (2 * m) (0, 0, 0)
    let (b0, b1, b2) := ws.getD (2 * m + 1) (0, 0, 0)
    rcv B_IF384 g [cid, K m, a0, a1, a2, b0, b1, b2]

/-- The public accumulator bytes of `hid` (`0`: `outcomeAcc`, `1`: `outRcpt0`) on a side. -/
def accPub (S : BndLay.Side) (j : Nat) : Expr :=
  (1 - c "hid") * S.b "outcomeAcc" j + c "hid" * S.b "outRcpt0" j

def constraints : List Expr :=
  let act := c "act"; let fst := c "fst"; let lst := c "lst"
  let g := n "act" * (1 - n "fst")
  (["act", "fst", "lst", "hid"].map fun s => bool (c s)) ++
  [(1 - act) * fst, (1 - act) * lst, .isFirst * act * (1 - fst)] ++
  ((List.range 16).flatMap (splitCons blkB blkS)) ++
  ((List.range 6).flatMap (splitCons dgB dgS)) ++
  -- a hash starts from SHA-384's IV; its first 42 message bytes are the input accumulator
  ((List.range 24).map fun l => fst * (c "h" l - K ((wlimbs (IV384.getD (l / 3) 0)).getD (l % 3) 0))) ++
  ((List.range 42).map fun j => fst * (c "blk" j - accPub Rb.SI j)) ++
  -- its last row's output words 0..5 are `dg` (48 big-endian bytes); the first 42 are the output
  -- accumulator
  ((List.range 6).flatMap fun t =>
    let (a0, a1, a2) := wordOf dgB dgS t
    [lst * (a0 - c "o" (3 * t)), lst * (a1 - c "o" (3 * t + 1)), lst * (a2 - c "o" (3 * t + 2))]) ++
  ((List.range 42).map fun j => lst * (c "dg" j - accPub Rb.SO j)) ++
  -- inside a hash: the previous row is active, not last, same `hid`, and chains
  [.isTransition * g * (1 - act), .isTransition * g * lst, .isTransition * g * (n "hid" - c "hid")] ++
  ((List.range 24).map fun l => .isTransition * g * (n "h" l - c "o" l))

def interactions : List Interaction :=
  let act := c "act"; let lst := c "lst"
  comp act (c "cid") (hW ++ blockW ++ oW) ++
  [rcv B_ACCD lst [c "hid"]] ++
  ((List.range 128).map fun j => rcv B_RNG act [c "blk" j]) ++
  ((List.range 16).flatMap (splitRng act blkS)) ++
  ((List.range 48).map fun j => rcv B_RNG lst [c "dg" j]) ++
  ((List.range 6).flatMap (splitRng lst dgS))

def table : Table := { width := L.width, constraints, interactions, maxLog := 8 }

end Acc

/-! ## The `IF384` chip stub (lane B's `ChipStub.chipStub`, on this package's bus number)

In Lean the native SHA-512 compression chip is a sender-only table (no constraints, multiplicity
column 0, message columns 1..8); the prover runs the native chip (`s384/`, the recursion chip v4)
in its place, mapping `IF384` to the native bus 103. Its faithfulness is the named premise
`Sha512IfContract` on its sends (lane B's `Sha512If`). -/
def stubIx : Interaction :=
  { bus := B_IF384, mult := [.col 0 false], msg := (List.range 8).map (fun j => Expr.col (j + 1) false),
    send := true }

def chipStub : Table := { width := 9, constraints := [], interactions := [stubIx], maxLog := 22 }

end M5T1
