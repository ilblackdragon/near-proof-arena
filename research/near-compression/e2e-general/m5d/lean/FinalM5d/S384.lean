import FinalM5d.Dsl
import NearSpecV3.E2E.Boundary

/-!
# FinalM5d.S384 — SHA-384 of byte messages over the native compression chip, and the range table

**`S384`** turns the native SHA-512 compression chip (`IF384`, lane B's `Sha512If` contract) into
a byte-message hash with the interface of the SHA-256 table: it **receives** the message bytes
`SB (id, pos, byte)` and **sends** `SD (id, len, digest[48])` once per message. One row per
128-byte block:

* `f[i]` (data flags, monotone in `i`), `b[i]` (block bytes), `cnt` (bytes before this block),
  `len` (constant along the message); `SB (id, cnt + i, b[i])` with multiplicity `f[i]`;
* FIPS 180-4 §5.1.2 padding: the marker `p[i]` (`p[0] = m0`, `p[i] = f[i−1] − f[i]`) puts `0x80`
  right after the data (`m0` carries "the previous block was full" across rows), zeros elsewhere,
  and on the last block the 128-bit big-endian bit length (`len < 2^24`: bytes 124..127). A
  non-full non-last block has `≥ 112` data bytes and is followed by the extra block `x = 1`
  (no data, no marker); a last block with `x = 0` has `≤ 111` data bytes;
* the 16 block words as 21-bit limbs (`[0,21) [21,42) [42,64)`) from the bytes, with byte `B5`
  split `lo5 + 32·hi3` and `B2` split `lo2 + 4·hi6` (lookups `S5`/`S2`, the other bytes `R8`);
* `hin` = IV384 on a first block, the previous block's `hout` otherwise; the row receives the
  chip's 16 `IF384` messages `(cid, m, limbs w_{2m}, limbs w_{2m+1})` over `hin ‖ block ‖ hout`;
* on the last block, the digest bytes `ob[48]` of `hout[0..6)` (same splits) are sent on `SD`.

**`RNG`** is the lookup provider: rows `v = 0..255` (bits `β`), sending `R8 (v)`, `S2 (v, v mod 4,
v / 4)`, `S5 (v, v mod 32, v / 32)` with multiplicity bits.
-/

namespace FinalM5d.S384

open ZkFormal.Air

def L : Layout :=
  [("act", 1), ("first", 1), ("last", 1), ("x", 1), ("m0", 1), ("id", 1), ("len", 1), ("cnt", 1),
   ("cid", 1), ("f", 128), ("b", 128), ("s5lo", 16), ("s5hi", 16), ("s2lo", 16), ("s2hi", 16),
   ("hin", 24), ("hout", 24), ("ob", 48), ("o5lo", 6), ("o5hi", 6), ("o2lo", 6), ("o2hi", 6)]

def T : Cols := ⟨L⟩

/-- 21-bit limbs of a 64-bit word. -/
def limbsN (x : Nat) : List Nat := [x % 2 ^ 21, (x / 2 ^ 21) % 2 ^ 21, x / 2 ^ 42]

def ivLimbs : List Nat := NearSpecV3.E2E.Bnd.IV384.flatMap limbsN

/-- The limbs of a big-endian word from its 8 bytes and the two splits. -/
def wordLimbs (B : Nat → Expr) (lo5 hi3 lo2 hi6 : Expr) : List Expr :=
  [B 7 + K 256 * B 6 + K 65536 * lo5,
   hi3 + K 8 * B 4 + K 2048 * B 3 + K (2 ^ 19) * lo2,
   hi6 + K 64 * B 1 + K 16384 * B 0]

def blockLimbs (w : Nat) : List Expr :=
  wordLimbs (fun i => T.c "b" (8 * w + i)) (T.c "s5lo" w) (T.c "s5hi" w) (T.c "s2lo" w) (T.c "s2hi" w)

def outLimbs (w : Nat) : List Expr :=
  wordLimbs (fun i => T.c "ob" (8 * w + i)) (T.c "o5lo" w) (T.c "o5hi" w) (T.c "o2lo" w) (T.c "o2hi" w)

/-- The 32 interface words' limbs: `hin ‖ block ‖ hout`. -/
def ifLimbs : List Expr :=
  T.cs "hin" 24 ++ (List.range 16).flatMap blockLimbs ++ T.cs "hout" 24

def act := T.c "act"
def last := T.c "last"
def nd : Expr := sumE (T.cs "f" 128)
def p (i : Nat) : Expr := if i == 0 then T.c "m0" else T.c "f" (i - 1) - T.c "f" i

def constraints : List Expr :=
  let f := fun i => T.c "f" i
  let b := fun i => T.c "b" i
  let notLast := act - last
  -- booleans
  (["act", "first", "last", "x", "m0"].map fun s => bool (T.c s)) ++
  (List.range 128).map (fun i => bool (f i)) ++
  [ last * (1 - act), T.c "first" * (1 - act), f 0 * (1 - act), T.c "x" * (1 - act),
    -- monotone activity, row 0 is a first block
    .isTransition * (T.n "act") * (1 - act),
    .isFirst * (T.c "first" - act) ] ++
  (List.range 127).map (fun i => f (i + 1) * (1 - f i)) ++
  -- first block
  [ T.c "first" * T.c "cnt", T.c "first" * T.c "x", T.c "first" * (T.c "m0" - (1 - f 0)) ] ++
  (List.range 24).map (fun k => T.c "first" * (T.c "hin" k - K (ivLimbs.getD k 0))) ++
  -- inside a message: the next row continues it
  [ .isTransition * notLast * (1 - T.n "act"),
    .isTransition * notLast * T.n "first",
    .isTransition * last * T.n "act" * (1 - T.n "first"),
    .isTransition * notLast * (T.n "id" - T.c "id"),
    .isTransition * notLast * (T.n "len" - T.c "len"),
    .isTransition * notLast * (T.n "cnt" - T.c "cnt" - 128),
    .isTransition * notLast * (T.n "x" - (1 - f 127)),
    .isTransition * notLast * (T.n "m0" - (f 127 - T.n "f" 0)),
    notLast * (1 - f 127) * (1 - f 111),
    .isLast * notLast ] ++
  (List.range 24).map (fun k => .isTransition * notLast * (T.n "hin" k - T.c "hout" k)) ++
  -- the extra block / the last block
  [ T.c "x" * (1 - last), T.c "x" * f 0, last * (1 - T.c "x") * f 111,
    -- the message ends in a last block with `x = 0`, or in the non-full block before `x = 1`
    last * (1 - T.c "x") * (T.c "len" - T.c "cnt" - nd),
    notLast * (1 - f 127) * (T.c "len" - T.c "cnt" - nd),
    last * (K 8 * T.c "len" - (K (2 ^ 24) * b 124 + K 65536 * b 125 + K 256 * b 126 + b 127)) ] ++
  (List.range 12).map (fun i => last * b (112 + i)) ++
  -- padding bytes
  (List.range 112).map (fun i => (act - f i) * (b i - K 128 * p i)) ++
  (List.range 16).map (fun i => notLast * (1 - f (112 + i)) * (b (112 + i) - K 128 * p (112 + i))) ++
  -- the digest bytes of `hout[0..6)` on the last block
  (List.range 6).flatMap (fun w => (List.range 3).map fun l =>
    last * ((outLimbs w).getD l 0 - T.c "hout" (3 * w + l)))

def interactions : List Interaction :=
  (List.range 128).map (fun i => rcv B_SB (T.c "f" i) [T.c "id", T.c "cnt" + K i, T.c "b" i]) ++
  [snd B_SD last ([T.c "id", T.c "len"] ++ T.cs "ob" 48)] ++
  (List.range 16).map (fun m =>
    rcv B_IF384 act ([T.c "cid", K m] ++ (List.range 6).map fun k => ifLimbs.getD (6 * m + k) 0)) ++
  -- block bytes: splits for B2, B5, range for the rest
  (List.range 16).flatMap (fun w =>
    [rcv B_S5 act [T.c "b" (8 * w + 5), T.c "s5lo" w, T.c "s5hi" w],
     rcv B_S2 act [T.c "b" (8 * w + 2), T.c "s2lo" w, T.c "s2hi" w]] ++
    ([0, 1, 3, 4, 6, 7].map fun i => rcv B_R8 act [T.c "b" (8 * w + i)])) ++
  (List.range 6).flatMap (fun w =>
    [rcv B_S5 last [T.c "ob" (8 * w + 5), T.c "o5lo" w, T.c "o5hi" w],
     rcv B_S2 last [T.c "ob" (8 * w + 2), T.c "o2lo" w, T.c "o2hi" w]] ++
    ([0, 1, 3, 4, 6, 7].map fun i => rcv B_R8 last [T.c "ob" (8 * w + i)]))

def table : Table :=
  { width := L.width, constraints, interactions, maxLog := 20 }

end FinalM5d.S384

namespace FinalM5d.Rng

open ZkFormal.Air

def MB : Nat := 20

def L : Layout := [("v", 1), ("bit", 8), ("m8", MB), ("m2", MB), ("m5", MB)]
def T : Cols := ⟨L⟩

def bitsVal (lo n : Nat) : Expr := sumE ((List.range n).map fun i => K (2 ^ i) * T.c "bit" (lo + i))

def constraints : List Expr :=
  (List.range 8).map (fun i => bool (T.c "bit" i)) ++
  [ T.c "v" - bitsVal 0 8, .isFirst * T.c "v", .isTransition * (T.n "v" - T.c "v" - 1) ]

def interactions : List Interaction :=
  [ sndBits B_R8 (T.cs "m8" MB) [T.c "v"],
    sndBits B_S2 (T.cs "m2" MB) [T.c "v", bitsVal 0 2, bitsVal 2 6],
    sndBits B_S5 (T.cs "m5" MB) [T.c "v", bitsVal 0 5, bitsVal 5 3] ]

def table : Table := { width := L.width, constraints, interactions, maxLog := 8 }

end FinalM5d.Rng
