/-!
# A zstd decompressor matching the vendored zstd 1.5.6 decoder

A Lean port of the decompression path of the zstd library nearcore 2.13.4 links
(`zstd-sys-2.0.10+zstd.1.5.6`, used through `zstd::stream::Decoder`), enough to decode the
`EncodedChunkStateWitness` that chunk producers distribute (`CompressedData::decode`: zstd level 1,
4 workers, no content checksum). It is a reference decoder: every valid RFC-8878 frame is accepted
and it rejects wherever the vendored decoder errors.

What is ported (checked by `nearspec-v3-zstd-decode` differential tests against the vendored library
through the `zref` harness, `docs/evidence/lean-chunk-completion/size-limits/`):

* Frame header (magic, descriptor, window, FCS, dict-id), skippable frames, and the stream
  decoder's loop over every concatenated frame (`zstd::stream::read::Decoder`).
* Blocks: Raw / RLE / Compressed, the last-block flag, `Block_Maximum_Size = min(windowSize,128KiB)`.
* Literals section: Raw / RLE / Compressed / Treeless (Huffman) in 1 and 4 streams, 3/4/5-byte sizes.
* Sequences section: Predefined / RLE / FSE_Compressed / Repeat modes for LL, OF and ML, and
  sequence execution with three repeat offsets.
* Entropy: `FSE_readNCount`, FSE table build and decode, canonical Huffman weights (direct and
  FSE-compressed), single-symbol (X1) Huffman decoding, and the register-based reverse bitstream
  `BIT_DStream` (so the subtle reload-driven termination matches byte-for-byte).
* Content checksum: XXH64 of the output, low 32 bits compared when the descriptor's checksum flag is
  set (the vendored stream decoder verifies it by default).

The `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` = 64 MiB zip-bomb cut-off is applied by the caller on the
produced bytes, exactly as nearcore's `CountingRead` does, not inside this decoder.
-/

namespace NearSpecV3.Zstd

/-! ## 64-bit arithmetic -/

@[inline] def mkArr {α : Type} (n : Nat) (x : α) : Array α := Array.replicate n x
@[inline] def setD {α : Type} (a : Array α) (i : Nat) (x : α) : Array α := a.setIfInBounds i x

abbrev mask64 : Nat := 18446744073709551615

@[inline] def and64 (a b : Nat) : Nat := a &&& b
@[inline] def lo64 (n : Nat) : Nat := n &&& mask64
@[inline] def rotl64 (x r : Nat) : Nat :=
  let x := lo64 x
  lo64 ((x <<< r) ||| (x >>> (64 - r)))
@[inline] def mul64 (a b : Nat) : Nat := lo64 (a * b)
@[inline] def add64 (a b : Nat) : Nat := lo64 (a + b)
@[inline] def sub64 (a b : Nat) : Nat := lo64 (a + (mask64 + 1 - (b &&& mask64)))

/-- Index of the most significant set bit (0-based); `highbit32 0 = 0`, matching the callers that
never pass 0 where it matters. -/
@[inline] def highbit32 (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n

/-- Trailing-zero count over the low 32 bits; `x` always has bit 31 forced by the caller. -/
def ctz32 (x : Nat) : Nat := Id.run do
  let mut v := x &&& 0xFFFFFFFF
  if v == 0 then return 32
  let mut c := 0
  while v &&& 1 == 0 do
    v := v >>> 1
    c := c + 1
  return c

@[inline] def mask (nbBits : Nat) : Nat := (1 <<< nbBits) - 1

/-- Byte `i` of `data`, `0` out of range. The definition reads the byte through `ByteArray.data`;
compiled code uses `getBFast` instead (`getB_eq`, `@[csimp]`), because in compiled code
`ByteArray.data` converts the whole byte array to a boxed `Array UInt8` on every call (this made
each byte read O(input size), W02/W16). -/
def getB (data : ByteArray) (i : Nat) : UInt8 := data.data.getD i 0

/-- `getB` without the conversion: a bounds-checked direct read. -/
@[inline] def getBFast (data : ByteArray) (i : Nat) : UInt8 :=
  if h : i < data.size then data[i] else 0

@[csimp] theorem getB_eq : @getB = @getBFast := by
  funext data i
  cases data with
  | mk a =>
    unfold getB getBFast
    have hs : ({ data := a } : ByteArray).size = a.size := rfl
    by_cases h : i < a.size
    · have h' : i < ({ data := a } : ByteArray).size := h
      simp only [h', ↓reduceDIte]
      show a.getD i 0 = a[i]
      simp [Array.getD, h]
    · have h' : ¬ i < ({ data := a } : ByteArray).size := h
      simp only [h', ↓reduceDIte]
      show a.getD i 0 = 0
      simp [Array.getD, h]

/-- Little-endian integer of `k` bytes at absolute index `i`. Out-of-range bytes read as 0. -/
def readLE (data : ByteArray) (i k : Nat) : Nat := Id.run do
  let mut v := 0
  let mut sh := 0
  for j in [0:k] do
    let b := (getB data (i + j)).toNat
    v := v + (b <<< sh)
    sh := sh + 8
  return v

@[inline] def byteAt (data : ByteArray) (i : Nat) : Nat :=
  (getB data i).toNat

/-! ## `BIT_DStream`: the register-based reverse reader, ported from `bitstream.h`. -/

/-- Pure logical reverse reader. The logical bit sequence is MSB-first within each byte, bytes from
`hi-1` down to `lo`; `cur` counts bits consumed from the top (initialized past the sentinel), and a
read returns bits with the first-read bit as the most significant. This gives the same values as the
vendored register-based `BIT_readBits` (the register's `lookBits` extracts the same top bits), while
`endOk`/overflow are exact logical conditions. -/
structure BitD where
  data : ByteArray
  start : Nat            -- lo
  total : Nat            -- total logical bits = (hi-lo)*8
  cur : Nat              -- bits consumed from the top
  deriving Inhabited

/-- Result of a (now logical) end check; `reload` is retained as a no-op for API parity. -/
inductive DStat | unfinished | endOfBuffer | completed | overflow
  deriving DecidableEq, Repr

namespace BitD

/-- `BIT_initDStream` over `data[lo..hi)`: skip the last byte's sentinel bit and its leading zeros. -/
def init (data : ByteArray) (lo hi : Nat) : Except String BitD := do
  if hi ≤ lo then throw "zstd: empty bitstream"
  let last := byteAt data (hi - 1)
  if last == 0 then throw "zstd: corrupted (no endMark)"
  pure { data, start := lo, total := (hi - lo) * 8, cur := 8 - highbit32 last }

/-- The logical bit at top-offset `j` (0 = MSB of the last byte). -/
@[inline] def bitAt (b : BitD) (j : Nat) : Nat :=
  let byteFromTop := j / 8
  let within := j % 8
  let idx := b.start + (b.total / 8) - 1 - byteFromTop
  ((byteAt b.data idx) >>> (7 - within)) &&& 1

/-- `BIT_lookBits`: the next `nbBits` (first-read bit = MSB), without consuming. Byte-granular. -/
@[inline] def lookBits (b : BitD) (nbBits : Nat) : Nat := Id.run do
  let hi := b.start + (b.total / 8)
  let mut j := b.cur
  let mut need := nbBits
  let mut v := 0
  while need > 0 do
    let within := j % 8                   -- bits already consumed from this byte's MSB side
    let avail := 8 - within               -- bits left in this byte
    let idx := hi - 1 - (j / 8)
    let take := Nat.min need avail
    let byteVal := byteAt b.data idx
    let bits := (byteVal >>> (avail - take)) &&& ((1 <<< take) - 1)
    v := (v <<< take) ||| bits
    j := j + take
    need := need - take
  return v

@[inline] def skip (b : BitD) (nbBits : Nat) : BitD := { b with cur := b.cur + nbBits }

@[inline] def readBits (b : BitD) (nbBits : Nat) : Nat × BitD :=
  if nbBits == 0 then (0, b) else (b.lookBits nbBits, b.skip nbBits)

/-- Retained for API parity; the logical reader needs no window reload. -/
@[inline] def reload (b : BitD) : DStat × BitD := (.unfinished, b)

/-- `BIT_endOfDStream`: every bit consumed exactly. -/
@[inline] def endOk (b : BitD) : Bool := b.cur == b.total

/-- A read has gone past the available bits (used for FSE two-state flush termination). -/
@[inline] def overran (b : BitD) : Bool := b.cur > b.total

end BitD

end NearSpecV3.Zstd
