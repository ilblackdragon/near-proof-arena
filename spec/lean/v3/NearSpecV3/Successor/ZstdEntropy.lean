import NearSpecV3.Successor.Zstd

/-!
# zstd entropy stages: FSE and Huffman (ported from zstd 1.5.6)

`FSE_readNCount`, FSE table build/decode, `FSE_decompress` (used for Huffman weights), canonical
Huffman weight reading and single-symbol (X1) Huffman decoding, 1- and 4-stream.
-/

namespace NearSpecV3.Zstd

/-! ## FSE table description reader (`FSE_readNCount`, forward LE bitstream). -/

/-- Peek `k` bits (LE) at absolute bit offset `bp` into `data`. -/
@[inline] def peekF (data : ByteArray) (bp k : Nat) : Nat :=
  let byteStart := bp / 8
  let bitOff := bp % 8
  let nbytes := (k + bitOff + 7) / 8
  (readLE data byteStart nbytes >>> bitOff) &&& mask k

/-- Returns `(normalizedCounts, tableLog, maxSymbol, bytesConsumed)`. `start` is the absolute byte
index of the header; `maxSV0` is the caller's maximum symbol value. -/
def fseReadNCount (data : ByteArray) (start maxSV0 : Nat) :
    Except String (Array Int × Nat × Nat × Nat) := do
  -- all bit offsets are relative to `start`
  let peek (bp k : Nat) : Nat := peekF data (start * 8 + bp) k
  let w0 := peek 0 32
  let tableLog := (w0 &&& 0xF) + 5
  if tableLog > 15 then throw "zstd: FSE tableLog too large"
  let mut bp := 4
  let mut remaining : Int := (1 <<< tableLog) + 1
  let mut threshold : Int := 1 <<< tableLog
  let mut nbBits := tableLog + 1
  let mut charnum : Nat := 0
  let mut previous0 := false
  let maxSV1 := maxSV0 + 1
  let mut norm : Array Int := mkArr maxSV1 0
  let mut guard := 0
  while guard < 4096 do
    guard := guard + 1
    if previous0 then
      let mut w := peek bp 32
      let mut repeats := (ctz32 ((w ^^^ 0xFFFFFFFF) ||| 0x80000000)) / 2
      while repeats ≥ 12 do
        charnum := charnum + 36
        bp := bp + 24
        w := peek bp 32
        repeats := (ctz32 ((w ^^^ 0xFFFFFFFF) ||| 0x80000000)) / 2
      charnum := charnum + 3 * repeats
      bp := bp + 2 * repeats
      charnum := charnum + (peek bp 2)
      bp := bp + 2
      if charnum ≥ maxSV1 then
        break
    let w := peek bp 32
    let thr := threshold.toNat
    let maxv : Int := (2 * threshold - 1) - remaining
    let mut count : Int := 0
    if ((w &&& (thr - 1)) : Int) < maxv then
      count := (w &&& (thr - 1))
      bp := bp + (nbBits - 1)
    else
      count := (w &&& (2 * thr - 1))
      if count ≥ threshold then count := count - maxv
      bp := bp + nbBits
    count := count - 1
    if count ≥ 0 then remaining := remaining - count else remaining := remaining + count
    norm := setD norm charnum count
    charnum := charnum + 1
    previous0 := (count == 0)
    if remaining < threshold then
      if remaining ≤ 1 then break
      nbBits := highbit32 remaining.toNat + 1
      threshold := 1 <<< (nbBits - 1)
    if charnum ≥ maxSV1 then break
  if remaining != 1 then throw "zstd: FSE NCount corrupted (remaining)"
  if charnum > maxSV1 then throw "zstd: FSE NCount maxSymbolValue too small"
  let consumed := (bp + 7) / 8
  pure (norm.extract 0 charnum, tableLog, charnum - 1, consumed)

/-! ## FSE table build (`ZSTD_buildFSETable` / `FSE_buildDTable`). -/

structure FDTable where
  tableLog : Nat
  symbol : Array Nat
  nbBitsOut : Array Nat
  newState : Array Nat
  deriving Inhabited

/-- Build an FSE decoding table from normalized counts. `norm` has length `maxSymbol+1`. -/
def buildFSE (norm : Array Int) (maxSymbol tableLog : Nat) : FDTable := Id.run do
  let tableSize := 1 <<< tableLog
  let tableMask := tableSize - 1
  let step := (tableSize >>> 1) + (tableSize >>> 3) + 3
  let mut symbolTbl : Array Nat := mkArr tableSize 0
  let mut symbolNext : Array Nat := mkArr (maxSymbol + 1) 0
  let mut highThreshold : Int := (tableSize : Int) - 1
  for s in [0:maxSymbol+1] do
    if norm.getD s 0 == (-1 : Int) then
      let ht := highThreshold.toNat
      symbolTbl := setD symbolTbl ht s
      highThreshold := highThreshold - 1
      symbolNext := setD symbolNext s 1
    else
      symbolNext := setD symbolNext s ((norm.getD s 0).toNat)
  -- spread
  let mut pos := 0
  for s in [0:maxSymbol+1] do
    let cnt := let c := norm.getD s 0; if c < 0 then 0 else c.toNat
    for _ in [0:cnt] do
      symbolTbl := setD symbolTbl pos s
      pos := (pos + step) &&& tableMask
      while (pos : Int) > highThreshold do
        pos := (pos + step) &&& tableMask
  -- build decoding table
  let mut nbBitsOut : Array Nat := mkArr tableSize 0
  let mut newState : Array Nat := mkArr tableSize 0
  for u in [0:tableSize] do
    let sym := symbolTbl.getD u 0
    let nextState := symbolNext.getD sym 0
    symbolNext := setD symbolNext sym (nextState + 1)
    let nb := tableLog - highbit32 nextState
    nbBitsOut := setD nbBitsOut u nb
    newState := setD newState u ((nextState <<< nb) - tableSize)
  return { tableLog, symbol := symbolTbl, nbBitsOut, newState }

/-- RLE "table": one symbol, zero state bits. -/
def rleFSE (symbol : Nat) : FDTable :=
  { tableLog := 0, symbol := #[symbol], nbBitsOut := #[0], newState := #[0] }

/-! ## FSE state decode on a `BitD`. -/

structure FState where
  state : Nat
  deriving Inhabited

/-- `FSE_initDState`: read `tableLog` bits. -/
def fseInit (dt : FDTable) (b : BitD) : FState × BitD :=
  let (st, b) := b.readBits dt.tableLog
  ({ state := st }, b)

/-- Current symbol at the state. -/
@[inline] def fseSymbol (dt : FDTable) (s : FState) : Nat := dt.symbol.getD s.state 0

/-- `FSE_decodeSymbol`: read the state's `nbBits`, update to the next state. -/
def fseNext (dt : FDTable) (s : FState) (b : BitD) : FState × BitD :=
  let nb := dt.nbBitsOut.getD s.state 0
  let (low, b) := b.readBits nb
  ({ state := dt.newState.getD s.state 0 + low }, b)

/-! ## `FSE_decompress_usingDTable_generic` (used for Huffman weights). -/

/-- Decode `maxOut`-bounded symbols from the stream `data[lo..hi)` using table `dt`, matching the
vendored 64-bit generic decoder (`FSE_MAX_TABLELOG = 15`, so only the `*4+7 > 64` reload runs). -/
def fseDecompress (data : ByteArray) (lo hi : Nat) (dt : FDTable) (maxOut : Nat) :
    Except String (Array Nat) := do
  let mut b ← BitD.init data lo hi
  let (s1i, b1) := fseInit dt b; b := b1
  let (s2i, b2) := fseInit dt b; b := b2
  let mut s1 := s1i
  let mut s2 := s2i
  let mut out : Array Nat := #[]
  -- Two-state alternating decode; a state update that reads past the stream end is the final one
  -- (`BIT_reloadDStream == overflow` in the vendored tail loop). The 4-at-a-time main loop is only a
  -- speed unroll and produces the same symbols, so the tail loop alone is exact.
  let mut done := false
  let mut guard := 0
  while !done && guard < maxOut + 4 do
    guard := guard + 1
    if out.size > maxOut - 2 then throw "zstd: FSE decompress overflow"
    out := out.push (fseSymbol dt s1); let (s1', b1) := fseNext dt s1 b; s1 := s1'; b := b1
    if b.overran then
      out := out.push (fseSymbol dt s2); done := true
    else
      if out.size > maxOut - 2 then throw "zstd: FSE decompress overflow"
      out := out.push (fseSymbol dt s2); let (s2', b2) := fseNext dt s2 b; s2 := s2'; b := b2
      if b.overran then
        out := out.push (fseSymbol dt s1); done := true
  if !done then throw "zstd: FSE decompress did not terminate"
  pure out

/-! ## Huffman weights (`HUF_readStats`) and X1 table. -/

structure HufX1 where
  tableLog : Nat
  byteTbl : Array Nat    -- length 1<<tableLog: decoded symbol per lookahead index
  nbBits : Array Nat
  deriving Inhabited

/-- Read the Huffman weight description; returns (weights per symbol, nbSymbols, tableLog,
bytesConsumed). `src` is the absolute byte index of the description. -/
def hufReadStats (data : ByteArray) (src srcSize : Nat) :
    Except String (Array Nat × Nat × Nat × Nat) := do
  if srcSize == 0 then throw "zstd: HUF stats empty"
  let iSize0 := byteAt data src
  let mut weights : Array Nat := mkArr 256 0
  let mut oSize : Nat := 0
  let mut consumed : Nat := 0
  if iSize0 ≥ 128 then
    oSize := iSize0 - 127
    let bytesW := (oSize + 1) / 2
    if bytesW + 1 > srcSize then throw "zstd: HUF stats srcSize"
    for n in [0:oSize] do
      if n % 2 == 0 then
        let byte := byteAt data (src + 1 + n / 2)
        weights := setD weights n (byte >>> 4)
      else
        let byte := byteAt data (src + 1 + n / 2)
        weights := setD weights n (byte &&& 15)
    consumed := bytesW + 1
  else
    let iSize := iSize0
    if iSize + 1 > srcSize then throw "zstd: HUF stats srcSize"
    let (norm, tableLog, maxSym, ncount) ← fseReadNCount data (src + 1) 255
    if tableLog > 6 then throw "zstd: HUF weight FSE tableLog"
    let dt := buildFSE norm maxSym tableLog
    let decoded ← fseDecompress data (src + 1 + ncount) (src + 1 + iSize) dt 255
    oSize := decoded.size
    for n in [0:oSize] do
      weights := setD weights n (decoded.getD n 0)
    consumed := iSize + 1
  -- collect stats
  let mut weightTotal : Nat := 0
  for n in [0:oSize] do
    let w := weights.getD n 0
    if w > 12 then throw "zstd: HUF weight too large"
    weightTotal := weightTotal + ((1 <<< w) >>> 1)
  if weightTotal == 0 then throw "zstd: HUF weightTotal 0"
  let tableLog := highbit32 weightTotal + 1
  if tableLog > 12 then throw "zstd: HUF tableLog too large"
  let total := 1 <<< tableLog
  let rest := total - weightTotal
  let lastWeight := highbit32 rest + 1
  if (1 <<< highbit32 rest) != rest then throw "zstd: HUF last weight not power of two"
  weights := setD weights oSize lastWeight
  let nbSymbols := oSize + 1
  -- rank-1 validity
  let mut rank1 := 0
  for n in [0:nbSymbols] do
    if weights.getD n 0 == 1 then rank1 := rank1 + 1
  if rank1 < 2 || rank1 % 2 == 1 then throw "zstd: HUF rank1 invalid"
  pure (weights, nbSymbols, tableLog, consumed)

/-- Build the X1 (single-symbol) decoding table (no rescale: output identical to the vendored
rescaled table). -/
def hufBuildX1 (weights : Array Nat) (nbSymbols tableLog : Nat) : HufX1 := Id.run do
  let tableSize := 1 <<< tableLog
  -- rankVal[w] = count of symbols of weight w
  let mut rankVal : Array Nat := mkArr (tableLog + 1) 0
  for n in [0:nbSymbols] do
    let w := weights.getD n 0
    if w ≤ tableLog then rankVal := setD rankVal w (rankVal.getD w 0 + 1)
  -- rankStart cumulative
  let mut rankStart : Array Nat := mkArr (tableLog + 1) 0
  let mut acc := 0
  for w in [0:tableLog+1] do
    rankStart := setD rankStart w acc
    acc := acc + rankVal.getD w 0
  -- symbols ordered by weight then symbol index
  let mut symbols : Array Nat := mkArr nbSymbols 0
  let mut rs := rankStart
  for n in [0:nbSymbols] do
    let w := weights.getD n 0
    if w ≤ tableLog then
      let p := rs.getD w 0
      symbols := setD symbols p n
      rs := setD rs w (p + 1)
  -- fill DTable
  let mut byteTbl : Array Nat := mkArr tableSize 0
  let mut nbBitsT : Array Nat := mkArr tableSize 0
  let mut symbol := rankVal.getD 0 0   -- skip weight-0 symbols
  let mut uStart := 0
  for w in [1:tableLog+1] do
    let symbolCount := rankVal.getD w 0
    let len := (1 <<< w) >>> 1
    let nb := tableLog + 1 - w
    for s in [0:symbolCount] do
      let sym := symbols.getD (symbol + s) 0
      for j in [0:len] do
        byteTbl := setD byteTbl (uStart + j) sym
        nbBitsT := setD nbBitsT (uStart + j) nb
      uStart := uStart + len
    symbol := symbol + symbolCount
  return { tableLog, byteTbl, nbBits := nbBitsT }

/-! ## X1 Huffman stream decoding (`HUF_decodeStreamX1`). -/

/-- Decode exactly `count` symbols from `data[lo..hi)` into an output array, matching
`HUF_decodeStreamX1` on 64-bit (4-at-a-time with reload per group, then a no-reload tail). Returns
the produced bytes; the caller checks `count` and end-of-stream separately via `b.endOk`. -/
def hufDecodeStream (data : ByteArray) (lo hi : Nat) (t : HufX1) (count : Nat) :
    Except String (Array Nat × BitD) := do
  let mut b ← BitD.init data lo hi
  let dtLog := t.tableLog
  let decodeSym (b : BitD) : Nat × BitD :=
    let val := b.lookBits dtLog
    let sym := t.byteTbl.getD val 0
    let nb := t.nbBits.getD val 0
    (sym, b.skip nb)
  let mut out : Array Nat := Array.mkEmpty count
  -- The vendored 4-at-a-time structure only governs reload cadence; the symbols are a fixed-count
  -- canonical-code decode, so decoding exactly `count` of them is equivalent.
  while out.size < count do
    let (sym, b') := decodeSym b; out := out.push sym; b := b'
  pure (out, b)

end NearSpecV3.Zstd
