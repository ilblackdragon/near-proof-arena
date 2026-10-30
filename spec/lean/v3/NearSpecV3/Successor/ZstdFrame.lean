import NearSpecV3.Successor.ZstdEntropy

/-!
# zstd block/frame decoding, literals, sequences and the top-level decompressor.

Ported from zstd 1.5.6 (`zstd_decompress.c`, `zstd_decompress_block.c`) for the 64-bit path.
-/

namespace NearSpecV3.Zstd

/-! ## Sequence base/extra-bit tables (`zstd_decompress_block.c`). -/

def LL_base : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,24,28,32,40,48,64,0x80,0x100,0x200,0x400,0x800,0x1000,0x2000,0x4000,0x8000,0x10000]
def LL_bits : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,2,2,3,3,4,6,7,8,9,10,11,12,13,14,15,16]
def ML_base : Array Nat := #[3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,37,39,41,43,47,51,59,67,83,99,0x83,0x103,0x203,0x403,0x803,0x1003,0x2003,0x4003,0x8003,0x10003]
def ML_bits : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,2,2,3,3,4,4,5,7,8,9,10,11,12,13,14,15,16]
def OF_base : Array Nat := #[0,1,1,5,0xD,0x1D,0x3D,0x7D,0xFD,0x1FD,0x3FD,0x7FD,0xFFD,0x1FFD,0x3FFD,0x7FFD,0xFFFD,0x1FFFD,0x3FFFD,0x7FFFD,0xFFFFD,0x1FFFFD,0x3FFFFD,0x7FFFFD,0xFFFFFD,0x1FFFFFD,0x3FFFFFD,0x7FFFFFD,0xFFFFFFD,0x1FFFFFFD,0x3FFFFFFD,0x7FFFFFFD]
def OF_bits : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

def LL_defaultNorm : Array Int := #[4,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,2,2,2,2,2,2,2,2,2,3,2,1,1,1,1,1,-1,-1,-1,-1]
def ML_defaultNorm : Array Int := #[1,4,3,2,2,2,2,2, 2,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1, 1,1,1,1,1,1,-1,-1, -1,-1,-1,-1,-1]
def OF_defaultNorm : Array Int := #[1,1,1,1,1,1,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,-1,-1,-1,-1,-1]

def LL_defaultTable : FDTable := buildFSE LL_defaultNorm 35 6
def ML_defaultTable : FDTable := buildFSE ML_defaultNorm 52 6
def OF_defaultTable : FDTable := buildFSE OF_defaultNorm 28 5

/-! ## Carried entropy across blocks in a frame. -/

structure Entropy where
  huf : Option HufX1 := none
  ll : Option FDTable := none
  of : Option FDTable := none
  ml : Option FDTable := none
  rep : Array Nat := #[1, 4, 8]
  deriving Inhabited

/-! ## Literals section. -/

/-- Decode the literals section at absolute byte index `src` (length `srcSize` is the block's
remaining bytes). Returns `(literalBytes, bytesConsumed, entropy')`. -/
def decodeLiterals (data : ByteArray) (src srcSize : Nat) (ent : Entropy) (blockMax : Nat) :
    Except String (Array UInt8 × Nat × Entropy) := do
  if srcSize == 0 then throw "zstd: literals block empty"
  let b0 := byteAt data src
  let litType := b0 &&& 3
  match litType with
  | 0 | 1 =>   -- Raw (0) or RLE (1)
    let lhlCode := (b0 >>> 2) &&& 3
    let (lhSize, litSize) :=
      match lhlCode with
      | 1 => (2, (readLE data src 2) >>> 4)          -- 2-2-12
      | 3 => (3, (readLE data src 3) >>> 4)          -- 2-2-20 (only valid variant left)
      | _ => (1, b0 >>> 3)                            -- 2-1-5 (codes 0 and 2)
    if litSize > blockMax then throw "zstd: literals too large"
    if litType == 0 then
      if lhSize + litSize > srcSize then throw "zstd: raw literals srcSize"
      let mut out : Array UInt8 := Array.mkEmpty litSize
      for i in [0:litSize] do
        out := out.push (getB data (src + lhSize + i))
      pure (out, lhSize + litSize, ent)
    else
      if lhSize + 1 > srcSize then throw "zstd: rle literals srcSize"
      let v := getB data (src + lhSize)
      pure (Array.replicate litSize v, lhSize + 1, ent)
  | _ =>   -- Compressed (2) or Treeless/Repeat (3)
    if srcSize < 5 then throw "zstd: compressed literals srcSize"
    let lhlCode := (b0 >>> 2) &&& 3
    let lhc := readLE data src 4   -- up to 4 bytes; code 3 needs a 5th
    let (lhSize, litSize, litCSize, singleStream) :=
      match lhlCode with
      | 2 => (4, (lhc >>> 4) &&& 0x3FFF, lhc >>> 18, false)
      | 3 => (5, (lhc >>> 4) &&& 0x3FFFF, (lhc >>> 22) + ((byteAt data (src+4)) <<< 10), false)
      | 1 => (3, (lhc >>> 4) &&& 0x3FF, (lhc >>> 14) &&& 0x3FF, false)
      | _ => (3, (lhc >>> 4) &&& 0x3FF, (lhc >>> 14) &&& 0x3FF, true)  -- lhlCode 0 ⇒ single stream
    if litSize > blockMax then throw "zstd: compressed literals too large"
    if !singleStream && litSize < 6 then throw "zstd: too few literals for 4 streams"
    if litCSize + lhSize > srcSize then throw "zstd: compressed literals csize"
    -- Huffman table: fresh (type 2) or reused (type 3 = treeless/repeat)
    let (t, ent) ← match litType with
      | 2 => do
        let (weights, nbSym, tableLog, _) ← hufReadStats data (src + lhSize) litCSize
        let t := hufBuildX1 weights nbSym tableLog
        pure (t, { ent with huf := some t })
      | _ => match ent.huf with
             | some t => pure (t, ent)
             | none => throw "zstd: treeless literals without prior Huffman table"
    let streamStart :=
      match litType with
      | 2 => src + lhSize + (hufStatsBytes data (src + lhSize))
      | _ => src + lhSize
    let csRemain := litCSize - (streamStart - (src + lhSize))
    if singleStream then
      let (lits, b) ← hufDecodeStream data streamStart (streamStart + csRemain) t litSize
      if !b.endOk then throw "zstd: Huffman 1-stream not fully consumed"
      pure (lits.map (fun n => UInt8.ofNat n), lhSize + litCSize, ent)
    else
      -- 4 streams: 6-byte jump table (3 × LE16) then 4 reverse streams
      if csRemain < 10 then throw "zstd: 4-stream literals too small"
      let l1 := readLE data streamStart 2
      let l2 := readLE data (streamStart+2) 2
      let l3 := readLE data (streamStart+4) 2
      let l4 := csRemain - (l1 + l2 + l3 + 6)
      if l1 + l2 + l3 + 6 > csRemain then throw "zstd: 4-stream jump table overflow"
      let s1 := streamStart + 6
      let s2 := s1 + l1
      let s3 := s2 + l2
      let s4 := s3 + l3
      let seg := (litSize + 3) / 4
      let seg4 := litSize - 3 * seg
      let (o1, b1) ← hufDecodeStream data s1 s2 t seg
      let (o2, b2) ← hufDecodeStream data s2 s3 t seg
      let (o3, b3) ← hufDecodeStream data s3 s4 t seg
      let (o4, b4) ← hufDecodeStream data s4 (s4 + l4) t seg4
      if !b1.endOk || !b2.endOk || !b3.endOk || !b4.endOk then
        throw "zstd: Huffman 4-stream not fully consumed"
      let lits := (o1 ++ o2 ++ o3 ++ o4).map (fun n => UInt8.ofNat n)
      pure (lits, lhSize + litCSize, ent)
where
  /-- Bytes consumed by the Huffman weight description at `p` (so the stream start can be found). -/
  hufStatsBytes (data : ByteArray) (p : Nat) : Nat :=
    let i0 := byteAt data p
    if i0 ≥ 128 then ((i0 - 127) + 1) / 2 + 1 else i0 + 1

/-! ## Sequences. -/

structure Seq where
  litLen : Nat
  matchLen : Nat
  offset : Nat
  deriving Inhabited

/-- Decode one FSE table slot for a sequence symbol family. Returns the table and bytes consumed. -/
def buildSeqTable (data : ByteArray) (src srcLeft : Nat) (type maxSym maxLog : Nat)
    (defTable : FDTable) (prev : Option FDTable) :
    Except String (FDTable × Nat) := do
  match type with
  | 0 => pure (defTable, 0)                              -- Predefined
  | 1 =>                                                  -- RLE
    if srcLeft == 0 then throw "zstd: seq RLE srcSize"
    let sym := byteAt data src
    if sym > maxSym then throw "zstd: seq RLE symbol"
    pure (rleFSE sym, 1)
  | 2 =>                                                  -- FSE_Compressed
    let (norm, tableLog, m, consumed) ← fseReadNCount data src maxSym
    if tableLog > maxLog then throw "zstd: seq FSE tableLog"
    pure (buildFSE norm m tableLog, consumed)
  | _ =>                                                  -- Repeat
    match prev with
    | some t => pure (t, 0)
    | none => throw "zstd: seq repeat without prior table"

/-- `ZSTD_decodeSequence` for the 64-bit regular-offset path, plus rep update. -/
def decodeOneSeq (llT ofT mlT : FDTable) (rep : Array Nat)
    (sLL sOF sML : FState) (b : BitD) (isLast : Bool) :
    Seq × Array Nat × FState × FState × FState × BitD :=
  let llSym := llT.symbol.getD sLL.state 0
  let ofSym := ofT.symbol.getD sOF.state 0
  let mlSym := mlT.symbol.getD sML.state 0
  let mlBase := ML_base.getD mlSym 0
  let llBase := LL_base.getD llSym 0
  let llBits := LL_bits.getD llSym 0
  let mlBits := ML_bits.getD mlSym 0
  let ofBits := OF_bits.getD ofSym 0
  let ofBase := OF_base.getD ofSym 0
  -- offset
  let (offset, rep, b) :=
    if ofBits > 1 then
      let (ex, b) := b.readBits ofBits
      let off := ofBase + ex
      (off, #[off, rep.getD 0 1, rep.getD 1 4], b)
    else
      let ll0 := llBase == 0
      if ofBits == 0 then
        let off := rep.getD (if ll0 then 1 else 0) 1
        let r1 := rep.getD (if ll0 then 0 else 1) 1
        (off, #[off, r1, rep.getD 2 8], b)
      else
        let (bit, b) := b.readBits 1
        let idx := ofBase + (if ll0 then 1 else 0) + bit   -- 1..3
        let temp := if idx == 3 then rep.getD 0 1 - 1 else rep.getD idx 1
        let temp := if temp == 0 then (mask64) else temp   -- 0 invalid → force huge (corruption later)
        let rep2 := if idx != 1 then rep.getD 1 4 else rep.getD 2 8
        (temp, #[temp, rep.getD 0 1, rep2], b)
  -- match length extra
  let (mlEx, b) := if mlBits > 0 then b.readBits mlBits else (0, b)
  let matchLen := mlBase + mlEx
  -- literal length extra
  let (llEx, b) := if llBits > 0 then b.readBits llBits else (0, b)
  let litLen := llBase + llEx
  -- state update (skip on last sequence): LL, ML, OF
  let (sLL, sML, sOF, b) :=
    if isLast then (sLL, sML, sOF, b)
    else
      let (sLL, b) := fseNext llT sLL b
      let (sML, b) := fseNext mlT sML b
      let (sOF, b) := fseNext ofT sOF b
      (sLL, sML, sOF, b)
  (⟨litLen, matchLen, offset⟩, rep, sLL, sOF, sML, b)

/-- Decode all `nbSeq` sequences from `data[lo..hi)`. Returns the sequences and the final reps. -/
def decodeSeqs (data : ByteArray) (lo hi : Nat) (llT ofT mlT : FDTable) (rep0 : Array Nat)
    (nbSeq : Nat) : Except String (Array Seq × Array Nat) := do
  let mut b ← BitD.init data lo hi
  let (sLL, b1) := fseInit llT b; b := b1
  let (sOF, b2) := fseInit ofT b; b := b2
  let (sML, b3) := fseInit mlT b; b := b3
  let mut sLLm := sLL
  let mut sOFm := sOF
  let mut sMLm := sML
  let mut rep := rep0
  let mut seqs : Array Seq := Array.mkEmpty nbSeq
  for i in [0:nbSeq] do
    let isLast := i + 1 == nbSeq
    let (s, rep', l', o', m', b') := decodeOneSeq llT ofT mlT rep sLLm sOFm sMLm b isLast
    seqs := seqs.push s
    rep := rep'; sLLm := l'; sOFm := o'; sMLm := m'; b := b'
  if !b.endOk then throw "zstd: sequence bitstream not fully consumed"
  pure (seqs, rep)

/-- Execute sequences against the literal buffer, appending to `out`. `windowSize` bounds how far a
match may reference back (`offset > windowSize` is corruption in the vendored decoder). -/
def execSeqs (out : ByteArray) (lits : Array UInt8) (seqs : Array Seq) (windowSize : Nat) :
    Except String ByteArray := do
  let mut o := out
  let mut litPos := 0
  for s in seqs do
    if litPos + s.litLen > lits.size then throw "zstd: sequence litLength exceeds literals"
    for i in [0:s.litLen] do
      o := o.push (lits.getD (litPos + i) 0)
    litPos := litPos + s.litLen
    if s.offset == 0 || s.offset > o.size || s.offset > windowSize then
      throw "zstd: sequence offset invalid"
    let startIdx := o.size - s.offset
    for i in [0:s.matchLen] do
      o := o.push (o.get! (startIdx + i))
  -- remaining literals
  for i in [litPos:lits.size] do
    o := o.push (lits.getD i 0)
  pure o

/-! ## Block decoding. -/

/-- Decode a compressed block body `data[src..src+blockSize)`, appending to `out`. -/
def decodeCompressedBlock (data : ByteArray) (src blockSize : Nat) (ent : Entropy)
    (blockMax windowSize : Nat) (out : ByteArray) : Except String (ByteArray × Entropy) := do
  let (lits, litBytes, ent) ← decodeLiterals data src blockSize ent blockMax
  let seqSrc := src + litBytes
  let seqLeft := blockSize - litBytes
  if seqLeft == 0 then throw "zstd: missing sequences section"
  -- sequence header: nbSeq
  let b0 := byteAt data seqSrc
  let (nbSeq, hdr) :=
    if b0 < 128 then (b0, 1)
    else if b0 == 255 then (readLE data (seqSrc+1) 2 + 0x7F00, 3)
    else (((b0 - 0x80) <<< 8) + byteAt data (seqSrc+1), 2)
  if nbSeq == 0 then
    -- no sequences: section ends; output is just the literals
    if hdr != seqLeft then throw "zstd: extraneous data in empty sequences section"
    if lits.size > blockMax then throw "zstd: regenerated block exceeds block maximum"
    pure (out ++ ByteArray.mk lits, ent)
  else
    let modeByte := byteAt data (seqSrc + hdr)
    if modeByte &&& 3 != 0 then throw "zstd: sequence reserved bits"
    let llType := modeByte >>> 6
    let ofType := (modeByte >>> 4) &&& 3
    let mlType := (modeByte >>> 2) &&& 3
    let mut p := seqSrc + hdr + 1
    let endP := seqSrc + seqLeft
    let (llT, c1) ← buildSeqTable data p (endP - p) llType 35 9 LL_defaultTable ent.ll
    p := p + c1
    let (ofT, c2) ← buildSeqTable data p (endP - p) ofType 31 8 OF_defaultTable ent.of
    p := p + c2
    let (mlT, c3) ← buildSeqTable data p (endP - p) mlType 52 9 ML_defaultTable ent.ml
    p := p + c3
    let ent := { ent with ll := some llT, of := some ofT, ml := some mlT }
    let (seqs, rep) ← decodeSeqs data p endP llT ofT mlT ent.rep nbSeq
    let out0size := out.size
    let out ← execSeqs out lits seqs windowSize
    if out.size - out0size > blockMax then throw "zstd: regenerated block exceeds block maximum"
    pure (out, { ent with rep })
where
  _unused := 0

/-- Decode a single block; returns `(out', entropy', bytesConsumed, lastBlock)`. -/
def decodeBlock (data : ByteArray) (src stop : Nat) (ent : Entropy) (windowSize : Nat)
    (out : ByteArray) : Except String (ByteArray × Entropy × Nat × Bool) := do
  if src + 3 > stop then throw "zstd: truncated block header"
  let hdr := readLE data src 3
  let lastBlock := hdr &&& 1 == 1
  let blockType := (hdr >>> 1) &&& 3
  let blockSize := hdr >>> 3
  let blockMax := Nat.min windowSize 131072
  let body := src + 3
  match blockType with
  | 0 =>   -- Raw
    if body + blockSize > stop then throw "zstd: raw block truncated"
    if blockSize > blockMax then throw "zstd: raw block too large"
    pure (out ++ data.extract body (body + blockSize), ent, 3 + blockSize, lastBlock)
  | 1 =>   -- RLE
    if body + 1 > stop then throw "zstd: rle block truncated"
    if blockSize > blockMax then throw "zstd: rle block too large"
    let v := getB data body
    pure (out ++ ByteArray.mk (Array.replicate blockSize v), ent, 3 + 1, lastBlock)
  | 2 =>   -- Compressed
    if body + blockSize > stop then throw "zstd: compressed block truncated"
    if blockSize > blockMax then throw "zstd: compressed block too large"
    let (o, ent) ← decodeCompressedBlock data body blockSize ent blockMax windowSize out
    pure (o, ent, 3 + blockSize, lastBlock)
  | _ => throw "zstd: reserved block type"

/-! ## XXH64 (content checksum). -/

def P1 : Nat := 11400714785074694791
def P2 : Nat := 14029467366897019727
def P3 : Nat :=  1609587929392839161
def P4 : Nat :=  9650029242287828579
def P5 : Nat :=  2870177450012600261

@[inline] def xround (acc input : Nat) : Nat :=
  mul64 (rotl64 (add64 acc (mul64 input P2)) 31) P1

@[inline] def xmerge (acc v : Nat) : Nat :=
  add64 (mul64 (acc ^^^ (xround 0 v)) P1) P4

def xxh64 (data : ByteArray) : Nat := Id.run do
  let len := data.size
  let get64 (i : Nat) : Nat := Id.run do
    let mut v := 0
    for j in [0:8] do v := v + ((byteAt data (i+j)) <<< (8*j))
    return v
  let get32 (i : Nat) : Nat := Id.run do
    let mut v := 0
    for j in [0:4] do v := v + ((byteAt data (i+j)) <<< (8*j))
    return v
  let mut h := 0
  let mut p := 0
  if len ≥ 32 then
    let mut v1 := add64 (add64 0 P1) P2
    let mut v2 := add64 0 P2
    let mut v3 := 0
    let mut v4 := sub64 0 P1
    while p + 32 ≤ len do
      v1 := xround v1 (get64 p)
      v2 := xround v2 (get64 (p+8))
      v3 := xround v3 (get64 (p+16))
      v4 := xround v4 (get64 (p+24))
      p := p + 32
    h := add64 (add64 (rotl64 v1 1) (rotl64 v2 7)) (add64 (rotl64 v3 12) (rotl64 v4 18))
    h := xmerge h v1; h := xmerge h v2; h := xmerge h v3; h := xmerge h v4
  else
    h := add64 0 P5
  h := add64 h len
  while p + 8 ≤ len do
    h := add64 (mul64 (rotl64 (h ^^^ (xround 0 (get64 p))) 27) P1) P4
    p := p + 8
  if p + 4 ≤ len then
    h := add64 (mul64 (rotl64 (h ^^^ (mul64 (get32 p) P1)) 23) P2) P3
    p := p + 4
  while p < len do
    h := mul64 (rotl64 (h ^^^ (mul64 (byteAt data p) P5)) 11) P1
    p := p + 1
  h := h ^^^ (h >>> 33); h := mul64 h P2
  h := h ^^^ (h >>> 29); h := mul64 h P3
  h := h ^^^ (h >>> 32)
  return h

/-! ## Frame header and the top-level decompressor. -/

/-- Parse one zstd frame header at `src`; returns `(windowSize, checksumFlag, bytesConsumed)`. -/
def parseFrameHeader (data : ByteArray) (src stop : Nat) :
    Except String (Nat × Bool × Nat) := do
  if src + 5 > stop then throw "zstd: truncated frame header"
  let fhd := byteAt data (src + 4)
  let dictIdFlag := fhd &&& 3
  let checksumFlag := (fhd >>> 2) &&& 1 == 1
  let singleSegment := (fhd >>> 5) &&& 1 == 1
  let fcsFlag := fhd >>> 6
  let mut p := src + 5
  let mut windowSize := 0
  if singleSegment then
    pure ()   -- window = FCS, handled below
  else
    let wb := byteAt data p
    let exponent := wb >>> 3
    let mantissa := wb &&& 7
    let windowBase := 1 <<< (10 + exponent)
    windowSize := windowBase + (windowBase / 8) * mantissa
    p := p + 1
  let dictIdSize := match dictIdFlag with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 4
  if dictIdSize != 0 then throw "zstd: dictionary not supported"
  p := p + dictIdSize
  let fcsSize := match fcsFlag with
    | 0 => if singleSegment then 1 else 0
    | 1 => 2 | 2 => 4 | _ => 8
  let fcs := if fcsSize == 0 then 0 else
             let raw := readLE data p fcsSize
             if fcsSize == 2 then raw + 256 else raw
  p := p + fcsSize
  if singleSegment then windowSize := fcs
  -- window log limit (ZSTD_WINDOWLOG_LIMIT_DEFAULT = 27)
  if windowSize > (1 <<< 27) then throw "zstd: window too large"
  pure (windowSize, checksumFlag, p - src)

/-- Decode a single frame starting at `src`; returns `(output, bytesConsumed)`. -/
def decodeFrame (data : ByteArray) (src stop : Nat) (cap : Nat := 1 <<< 62) :
    Except String (ByteArray × Nat) := do
  let magic := readLE data src 4
  if magic ≥ 0x184D2A50 && magic ≤ 0x184D2A5F then
    -- skippable frame
    if src + 8 > stop then throw "zstd: truncated skippable frame"
    let fsize := readLE data (src + 4) 4
    if src + 8 + fsize > stop then throw "zstd: skippable frame overruns"
    pure (ByteArray.empty, 8 + fsize)
  else if magic != 0xFD2FB528 then
    throw "zstd: unknown frame descriptor"
  else
    let (windowSize, checksumFlag, hdrBytes) ← parseFrameHeader data src stop
    let mut p := src + hdrBytes
    let mut ent : Entropy := {}
    let mut out : ByteArray := ByteArray.empty
    let mut last := false
    let mut guard := 0
    while !last && guard < 2000000 do
      guard := guard + 1
      let (o, ent', consumed, lastBlock) ← decodeBlock data p stop ent windowSize out
      out := o; ent := ent'; p := p + consumed; last := lastBlock
      if out.size > cap then throw "decode: witness larger than 64 MiB"
    if !last then throw "zstd: too many blocks / not terminated"
    if checksumFlag then
      if p + 4 > stop then throw "zstd: missing content checksum"
      let stored := readLE data p 4
      let computed := (xxh64 out) &&& 0xFFFFFFFF
      if stored != computed then throw "zstd: content checksum mismatch"
      p := p + 4
    pure (out, p - src)

/-- Decompress all frames of `data[lo..hi)` (the vendored stream decoder loops to EOF). The caller
applies the 64 MiB output cap. -/
def decompress (data : ByteArray) (lo hi : Nat) (cap : Nat := 1 <<< 62) : Except String ByteArray := do
  let mut p := lo
  let mut out : ByteArray := ByteArray.empty
  let mut guard := 0
  while p < hi && guard < 1000000 do
    guard := guard + 1
    let (o, consumed) ← decodeFrame data p hi cap
    out := out ++ o
    if out.size > cap then throw "decode: witness larger than 64 MiB"
    if consumed == 0 then throw "zstd: zero-length frame"
    p := p + consumed
  if p < hi then throw "zstd: trailing data could not be framed"
  pure out

/-- Convenience wrapper over a `List UInt8`, returning a `List UInt8`. -/
def decompressList (bytes : List UInt8) : Except String (List UInt8) := do
  let arr := ByteArray.mk bytes.toArray
  let out ← decompress arr 0 arr.size
  pure out.toList

/-- Decompress a `Bytes` (= `List UInt8`) region to `Bytes`, with the 64 MiB output cap applied as
nearcore's `CountingRead` does. -/
def decompressBytesCapped (bytes : List UInt8) : Except String (List UInt8) := do
  let arr := ByteArray.mk bytes.toArray
  let out ← decompress arr 0 arr.size 67108864
  pure out.toList

end NearSpecV3.Zstd
