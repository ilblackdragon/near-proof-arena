import StateM5a.Dsl

/-!
# StateM5a.Ws — the SHA-384 working-set tree: `WSB` (leaves), `WSN` (inner nodes), and a
segment's batched update: `WSA` (write accesses), `WSL` (touched leaves), `WSP` (touched paths)

The working set of a segment is the key-sorted list of every key the chunk touches, each entry
`(sha256 key, pre-value ref, current value ref, written)`; a value ref is `(present, len,
sha256 value)`.  Entries are leaves of a complete binary Merkle tree of depth `D` (indices `≥ n`
hold the zero digest).  Hashing is SHA-384 (FIPS 180-4) through the native SHA-512 compression
chip: every compression is 16 messages `(cid, pair m, limbs(w_{2m}), limbs(w_{2m+1}))` over the
32 words `h_in ‖ block ‖ h_out`, each word as limbs `[0,21) [21,42) [42,64)`.

* leaf digest (M5a-3): the first 6 words of `compress(IV384, leafBlock e)` — one compression; the
  16-bit fields fill the low two limbs, and the high limb is `kd_t + 2^16·x_t` with the flags and
  the two lengths' 6-bit chunks in the side slots `x_t` (`leafBlock`, `leafX`);
* inner node: SHA-384 of the 96 bytes `left48 ‖ right48` (one block with its padding).

`WSB` hashes all `2^D` leaves twice: phase 0 is the INTAKE state (`cur = pre`, not written), each
real leaf's pre-value proved by a find walk from `prev_state_root`; phase 1 is the final state,
each written leaf applied by an upsert / delete walk, in index (= key) order, chaining the trie root
from `prev_state_root` to the post-state root.  `WSN` builds both trees; the phase-0 root starts the
`RCH` chain and the phase-1 root must close it.

**Segments (M5a-3).**  Between the two, the writes are cut into segments (one per STATE segment
in M5b; `RCH(s, root)` is the working-set root at the start of segment `s`).  A segment does not
walk a Merkle path per write: its write accesses (`WSA`, no hashing) are linked per entry by
offline memory checking on `WM` (times strictly increase along each entry's chain), and the
segment rehashes the union of its touched paths once (`WSL` touched leaves, `WSP` path nodes, each
with an old and a new digest; untouched siblings are shared).  `Merkle.batch_update_sound`: with a
collision-free node hash, the old digests authenticate the touched leaves against `RCH(s)` and the
new root is the root of the working set with exactly those leaves replaced.
-/

namespace StateM5a

open ZkFormal.Air

/-- SHA-384 initial hash value (FIPS 180-4 §5.3.4). -/
def IV384 : List Nat :=
  [0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
   0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- The chip's limbs of a 64-bit word. -/
def wlimbs (x : Nat) : List Nat := [x % 2 ^ 21, x / 2 ^ 21 % 2 ^ 21, x / 2 ^ 42]

/-- A word as three limb expressions. -/
abbrev W3 := Expr × Expr × Expr

def constW (x : Nat) : W3 := (K (x % 2 ^ 21), K (x / 2 ^ 21 % 2 ^ 21), K (x / 2 ^ 42))
def zeroW : W3 := (0, 0, 0)

/-- The 16 interface receives of one compression `(h_in 8 words, block 16, h_out 8)`. -/
def comp (g cid : Expr) (ws : List W3) : List Interaction :=
  (List.range 16).map fun m =>
    let (a0, a1, a2) := ws.getD (2 * m) zeroW
    let (b0, b1, b2) := ws.getD (2 * m + 1) zeroW
    rcv B_IF384 g [cid, K m, a0, a1, a2, b0, b1, b2]

/-- Words of a 6-word digest stored as 18 limb columns. -/
def digW (x : Nat → Expr) : List W3 := (List.range 6).map fun i => (x (3 * i), x (3 * i + 1), x (3 * i + 2))
def wordsOf (x : Nat → Expr) (n : Nat) : List W3 :=
  (List.range n).map fun i => (x (3 * i), x (3 * i + 1), x (3 * i + 2))

/-- Chunks of a working-set leaf's value length (6 bits each in an honest trace: `< 2^24`). -/
def LEN_CHUNKS : Nat := 4

/-- The side slots of the leaf block: slot 0 = `pp + 2·cp + 4·wr`, slots 1–4 the pre-value
length's chunks, 5–8 the current length's chunks, 9–15 zero. -/
def leafX (pp cp wr : Expr) (plx clx : Nat → Expr) (t : Nat) : Expr :=
  if t = 0 then pp + K 2 * cp + K 4 * wr
  else if t ≤ LEN_CHUNKS then plx (t - 1)
  else if t ≤ 2 * LEN_CHUNKS then clx (t - 1 - LEN_CHUNKS)
  else 0

/-- **The leaf block** (one SHA-512 compression, M5a-3): 16 words; word `t < 8` is
`(pv_{2t}, pv_{2t+1}, kd_t + 2^16·x_t)`, word `8 + t` is `(cv_{2t}, cv_{2t+1}, kd_{8+t} + 2^16·x_{8+t})`.
The fields `kd`/`pv`/`cv` are 16-bit and the side slots `x = leafX …` are `< 2^8` (`RNG`), so
every limb determines its fields (`Merkle.leafLimb_inj`).  The leaf digest is the first 6 words of
`compress(IV384, block)`. -/
def leafBlock (kd : Nat → Expr) (x : Nat → Expr) (pv cv : Nat → Expr) : List W3 :=
  ((List.range 8).map fun t => (pv (2 * t), pv (2 * t + 1), kd t + K 65536 * x t)) ++
  ((List.range 8).map fun t => (cv (2 * t), cv (2 * t + 1), kd (8 + t) + K 65536 * x (8 + t)))

/-- `v − Σ 64^k ch_k`: a length as its chunks. -/
def lenChunks (v : Expr) (ch : Nat → Expr) : Expr :=
  v - sumE ((List.range LEN_CHUNKS).map fun k => K (64 ^ k) * ch k)

/-- The SHA-384 block of `left48 ‖ right48` (96 bytes: padding `0x80`, length 768 bits). -/
def nodeBlock (l r : List W3) : List W3 :=
  l ++ r ++ [constW (2 ^ 63), zeroW, zeroW, constW 768]

def ivW : List W3 := IV384.map constW

/-! ## Buses added by M5a-3 (numbered after the shared ones) -/

/-- `(seg, kd16, cp, cl, cv16, wr, id)`: working-set entry `kd`'s current value ref and written
flag in segment `seg` as of access time `id` (offline memory checking: a segment's leaf row sends
the entry at `id = 0`, each write access consumes the latest and sends its own at its time `t`,
the leaf row consumes the last). -/
def B_WM : Nat := NUM_BUSES
/-- `(seg, level, index, old18, new18)`: a node of segment `seg`'s batched update (old and new
digest of a node on a touched path). -/
def B_PT : Nat := NUM_BUSES + 1
def NUM_BUSES_WS : Nat := NUM_BUSES + 2

/-- Bytes of a write access's time gap `t − idp − 1` (segment-local times are `< 2^24`). -/
def DT_BYTES : Nat := 3

/-- **The working-set entry count** `wsLen` (M5a-5): public value 16 (after `prev_state_root`'s
16 limbs).  `WSB`'s `real` flag is exactly `i < wsLen` in both phases, and a touched leaf (`WSL`)
has `i < wsLen` (bytes `ix` of `wsLen − 1 − i`), so a real leaf is never a zero padding leaf and
the count is the state commitment's `wsLen` (`StateView`). -/
def PUB_WSLEN : Nat := 16
def wsLenE : Expr := .pub PUB_WSLEN
/-- Bytes of `wsLen − 1 − i` for a touched leaf (`D ≤ 20`). -/
def IX_BYTES : Nat := 3

/-! ## WSB: leaves, both phases (`2^(D+1)` rows: phase 0 indices `0..2^D`, then phase 1) -/

namespace Wsb
def L : Layout :=
  [("ph", 1), ("i", 1), ("e", 1), ("real", 1), ("kid", 1), ("kd", 16), ("pp", 1), ("pl", 1),
   ("pv", 16), ("cp", 1), ("cl", 1), ("cv", 16), ("wr", 1), ("plx", LEN_CHUNKS), ("clx", LEN_CHUNKS),
   ("dg", 18), ("dx", 6), ("cid", 1), ("so", 1), ("j", 1), ("rin", 16), ("rout", 16), ("rk", 1),
   ("rnm", 4), ("rom", 4), ("rif", 1), ("rof", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

def leaf : List W3 :=
  leafBlock (fun t => c "kd" t) (leafX (c "pp") (c "cp") (c "wr") (fun k => c "plx" k) (fun k => c "clx" k))
    (fun t => c "pv" t) (fun t => c "cv" t)

def constraints (D : Nat) : List Expr :=
  let ph := c "ph"; let e := c "e"; let real := c "real"
  (["ph", "e", "real", "pp", "cp", "wr", "so", "rif", "rof"].map fun s => bool (c s)) ++
  [.isFirst * c "i", .isFirst * ph, .isFirst * c "j", .isLast * (1 - e), .isLast * (1 - ph),
   .isTransition * (nx "i" - (1 - e) * (c "i" + 1)),
   .isTransition * (nx "ph" - ph - e),
   e * (c "i" - K (2 ^ D - 1)),
   .isTransition * (1 - e) * nx "real" * (1 - real),
   c "so" - (1 - ph) * (1 - e) * real * nx "real",
   .isTransition * (nx "j" - c "j" - ph * c "wr"),
   (1 - ph) * (c "cp" - c "pp"), (1 - ph) * (c "cl" - c "pl"), (1 - ph) * c "wr",
   (1 - c "pp") * c "pl", (1 - c "cp") * c "cl",
   (1 - real) * c "pp", (1 - real) * c "cp", (1 - real) * c "wr", (1 - real) * c "pl",
   (1 - real) * c "cl",
   lenChunks (c "pl") (fun k => c "plx" k), lenChunks (c "cl") (fun k => c "clx" k),
   ph * c "wr" * (c "rk" - K RK_H) * (c "rk" - K RK_HB) * (c "rk" - K RK_HE) * (c "rk" - K RK_SAME)] ++
  ((List.range 16).flatMap fun t =>
    [(1 - ph) * (c "cv" t - c "pv" t), (1 - c "pp") * c "pv" t, (1 - c "cp") * c "cv" t,
     (1 - real) * c "kd" t]) ++
  ((List.range 18).map fun t => (1 - real) * c "dg" t) ++
  -- M5a-5: `real ↔ i < wsLen` in each phase (`real` is a prefix of the phase, by the transition
  -- constraint above): a phase whose first row is padding has `wsLen = 0`; the last real row of a
  -- phase is `i = wsLen − 1`, or `i = 2^D − 1` with `wsLen = 2^D`
  [.isFirst * (1 - real) * wsLenE,
   .isTransition * e * (1 - nx "real") * wsLenE,
   (1 - e) * real * (1 - nx "real") * (c "i" + 1 - wsLenE),
   e * real * (K (2 ^ D) - wsLenE)]

def interactions : List Interaction :=
  let ph := c "ph"; let real := c "real"; let gw := ph * c "wr"; let g0 := (1 - ph) * real
  [rcv B_KDIG real (c "kid" :: vec "kd" 16),
   rcv B_ORD (c "so") [c "kid", nx "kid"]] ++
  -- the length chunks are bytes (`RNG`), so the leaf block's high limbs are injective
  ((List.range LEN_CHUNKS).flatMap fun k => [rcv B_RNG real [c "plx" k], rcv B_RNG real [c "clx" k]]) ++
  comp real (c "cid") (ivW ++ leaf ++ digW (fun t => c "dg" t) ++ wordsOf (fun t => c "dx" t) 2) ++
  [snd B_TREE 1 ([ph, 0, c "i"] ++ vec "dg" 18),
   -- INTAKE: the pre-value is the trie's answer at `prev_state_root` (public values 0..15)
   snd B_DOWN g0 ([c "i", 0, 0] ++ ((List.range 16).map fun t => Expr.pub t) ++ [c "kid", 0, 0] ++
     List.replicate 16 0),
   rcv B_UP g0 ([c "i", 0, 0, 0] ++ List.replicate 16 0 ++ List.replicate 4 0 ++ List.replicate 4 0 ++
     [0, 0, c "pl"] ++ vec "pv" 16 ++ [c "pp"]),
   -- FINAL: apply the written leaf's final value (upsert if present, else delete)
   snd B_DOWN gw ([K W_FINAL + c "i", 0, c "rif"] ++ vec "rin" 16 ++ [c "kid", 2 - c "cp", c "cl"] ++
     vec "cv" 16),
   rcv B_UP gw ([K W_FINAL + c "i", 0, c "rk", c "rof"] ++ vec "rout" 16 ++ vec "rnm" 4 ++ vec "rom" 4 ++
     [0, 0, 0] ++ List.replicate 16 0 ++ [0]),
   -- the trie root between changes: a ref (flag 1: an in-memory version, batched FINAL); the
   -- public ends `TCH(0, 0, prev_state_root)`, `TCH(n, 0, post_state_root)` are digests
   rcv B_TCH gw ([c "j", c "rif"] ++ vec "rin" 16),
   snd B_TCH gw ([c "j" + 1, c "rof"] ++ vec "rout" 16)]

def table (D : Nat) : Table :=
  { width := L.width, constraints := constraints D, interactions, maxLog := 20 }
end Wsb

/-! ## WSN: inner nodes of both trees -/

namespace Wsn
def L : Layout :=
  [("act", 1), ("ph", 1), ("lvl", 1), ("idx", 1), ("top", 1), ("l", 18), ("r", 18), ("o", 18),
   ("ox", 6), ("cid", 1), ("nw", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

def constraints (D : Nat) : List Expr :=
  [bool (c "act"), bool (c "ph"), bool (c "top"), (1 - c "act") * c "top",
   c "top" * (c "lvl" - K (D - 1)), c "top" * c "idx"]

/-- The phase-0 (INTAKE) root starts the `RCH` chain at segment 0; the phase-1 (FINAL) root
closes it after `nw` segments. -/
def interactions : List Interaction :=
  let A := c "act"; let top := c "top"; let ph := c "ph"
  [rcv B_TREE A ([ph, c "lvl", sm 2 (c "idx")] ++ vec "l" 18),
   rcv B_TREE A ([ph, c "lvl", sm 2 (c "idx") + 1] ++ vec "r" 18),
   snd B_TREE (A - top) ([ph, c "lvl" + 1, c "idx"] ++ vec "o" 18),
   snd B_RCH (top * (1 - ph)) (0 :: vec "o" 18),
   rcv B_RCH (top * ph) (c "nw" :: vec "o" 18)] ++
  comp A (c "cid") (ivW ++ nodeBlock (digW fun t => c "l" t) (digW fun t => c "r" t) ++
    digW (fun t => c "o" t) ++ wordsOf (fun t => c "ox" t) 2)

def table (D : Nat) : Table :=
  { width := L.width, constraints := constraints D, interactions, maxLog := 20 }
end Wsn

/-! ## WSA: one write access (M5a-3: a memory access, no hashing)

The access at time `t` of segment `seg` to entry `kd` consumes the entry's latest value
`WM(seg, kd, old, idp)` with `idp < t` (the gap `t − idp − 1` is `DT_BYTES` bytes) and sends the
written value `WM(seg, kd, new, wr = 1, t)`.  The write itself is `WRITE(seg, t, kd, new)` (the
public tape in M5a; STATE rows in M5b). -/

namespace Wsa
def L : Layout :=
  [("act", 1), ("seg", 1), ("t", 1), ("kd", 16), ("cp", 1), ("cl", 1), ("cv", 16), ("wr", 1),
   ("idp", 1), ("ncp", 1), ("ncl", 1), ("ncv", 16), ("dt", DT_BYTES)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

def constraints : List Expr :=
  [bool (c "act"), bool (c "ncp"), (1 - c "ncp") * c "ncl",
   c "act" * (c "t" - c "idp" - 1 - sumE ((List.range DT_BYTES).map fun k => K (256 ^ k) * c "dt" k))] ++
  (List.range 16).map fun t => (1 - c "ncp") * c "ncv" t

def interactions : List Interaction :=
  let A := c "act"
  [rcv B_WRITE A ([c "seg", c "t"] ++ vec "kd" 16 ++ [c "ncp", c "ncl"] ++ vec "ncv" 16),
   rcv B_WM A ([c "seg"] ++ vec "kd" 16 ++ [c "cp", c "cl"] ++ vec "cv" 16 ++ [c "wr", c "idp"]),
   snd B_WM A ([c "seg"] ++ vec "kd" 16 ++ [c "ncp", c "ncl"] ++ vec "ncv" 16 ++ [1, c "t"])] ++
  (List.range DT_BYTES).map fun k => rcv B_RNG A [c "dt" k]

def table : Table :=
  { width := L.width, constraints, interactions, maxLog := 20 }
end Wsa

/-! ## WSL: a touched leaf of one segment (old leaf → new leaf, 2 compressions)

The old leaf's digest goes up the segment's old path (authenticated by the segment's incoming
`RCH` root), the new leaf's up the new path.  The row opens the entry's memory chain
(`WM(seg, kd, cur, wr, 0)`) and closes it (`WM(seg, kd, ncur, nwr, idl)`: the last access's value,
or the opening one if no access).  `kd` is range-checked (bytes `kb`) and the length chunks are
bytes, so the block determines the fields. -/

namespace Wsl
def L : Layout :=
  [("act", 1), ("seg", 1), ("i", 1), ("kd", 16), ("kb", 32), ("pp", 1), ("pl", 1), ("pv", 16),
   ("plx", LEN_CHUNKS), ("cp", 1), ("cl", 1), ("cv", 16), ("wr", 1), ("clx", LEN_CHUNKS),
   ("ncp", 1), ("ncl", 1), ("ncv", 16), ("nwr", 1), ("nclx", LEN_CHUNKS), ("idl", 1),
   ("cidO", 1), ("dgO", 18), ("dxO", 6), ("cidN", 1), ("dgN", 18), ("dxN", 6), ("ix", IX_BYTES)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

def constraints : List Expr :=
  (["act", "pp", "cp", "wr", "ncp", "nwr"].map fun s => bool (c s)) ++
  [lenChunks (c "pl") (fun k => c "plx" k), lenChunks (c "cl") (fun k => c "clx" k),
   lenChunks (c "ncl") (fun k => c "nclx" k)] ++
  ((List.range 16).map fun t => c "kd" t - (K 256 * c "kb" (2 * t) + c "kb" (2 * t + 1))) ++
  -- M5a-5: a touched leaf is a real entry, `i < wsLen`
  [c "act" * (wsLenE - 1 - c "i" - sumE ((List.range IX_BYTES).map fun k => K (256 ^ k) * c "ix" k))]

def interactions : List Interaction :=
  let A := c "act"
  let kd : Nat → Expr := fun t => c "kd" t
  let oldB := leafBlock kd (leafX (c "pp") (c "cp") (c "wr") (fun k => c "plx" k) (fun k => c "clx" k))
    (fun t => c "pv" t) (fun t => c "cv" t)
  let newB := leafBlock kd (leafX (c "pp") (c "ncp") (c "nwr") (fun k => c "plx" k) (fun k => c "nclx" k))
    (fun t => c "pv" t) (fun t => c "ncv" t)
  comp A (c "cidO") (ivW ++ oldB ++ digW (fun t => c "dgO" t) ++ wordsOf (fun t => c "dxO" t) 2) ++
  comp A (c "cidN") (ivW ++ newB ++ digW (fun t => c "dgN" t) ++ wordsOf (fun t => c "dxN" t) 2) ++
  [snd B_PT A ([c "seg", 0, c "i"] ++ vec "dgO" 18 ++ vec "dgN" 18),
   snd B_WM A ([c "seg"] ++ vec "kd" 16 ++ [c "cp", c "cl"] ++ vec "cv" 16 ++ [c "wr", 0]),
   rcv B_WM A ([c "seg"] ++ vec "kd" 16 ++ [c "ncp", c "ncl"] ++ vec "ncv" 16 ++ [c "nwr", c "idl"])] ++
  ((List.range 32).map fun b => rcv B_RNG A [c "kb" b]) ++
  ((List.range LEN_CHUNKS).flatMap fun k =>
    [rcv B_RNG A [c "plx" k], rcv B_RNG A [c "clx" k], rcv B_RNG A [c "nclx" k]]) ++
  (List.range IX_BYTES).map fun k => rcv B_RNG A [c "ix" k]

def table : Table :=
  { width := L.width, constraints, interactions, maxLog := 20 }
end Wsl

/-! ## WSP: a node on a segment's touched paths (old and new digest, 2 compressions)

A row at `(seg, lvl, idx)` receives its touched children (`tl`, `tr`, at least one) on `PT` and
holds an untouched child as one digest for both trees (`(1 − tl)·(lo − ln) = 0`); it sends its own
`(old, new)` to its parent, or, at the top, takes the segment's incoming root `RCH(seg, old)` and
sends the outgoing one `RCH(seg + 1, new)` (`Merkle.batch_update_sound`). -/

namespace Wsp
def L : Layout :=
  [("act", 1), ("seg", 1), ("lvl", 1), ("idx", 1), ("top", 1), ("tl", 1), ("tr", 1),
   ("lo", 18), ("ln", 18), ("ro", 18), ("rn", 18), ("oo", 18), ("oox", 6), ("on", 18), ("onx", 6),
   ("cidO", 1), ("cidN", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

def constraints (D : Nat) : List Expr :=
  [bool (c "act"), bool (c "top"), bool (c "tl"), bool (c "tr"),
   (1 - c "act") * c "top", (1 - c "act") * c "tl", (1 - c "act") * c "tr",
   c "act" * (1 - c "tl") * (1 - c "tr"),
   c "top" * (c "lvl" - K (D - 1)), c "top" * c "idx"] ++
  ((List.range 18).flatMap fun t =>
    [(1 - c "tl") * (c "lo" t - c "ln" t), (1 - c "tr") * (c "ro" t - c "rn" t)])

def interactions : List Interaction :=
  let A := c "act"; let top := c "top"
  [rcv B_PT (c "tl") ([c "seg", c "lvl", sm 2 (c "idx")] ++ vec "lo" 18 ++ vec "ln" 18),
   rcv B_PT (c "tr") ([c "seg", c "lvl", sm 2 (c "idx") + 1] ++ vec "ro" 18 ++ vec "rn" 18),
   snd B_PT (A - top) ([c "seg", c "lvl" + 1, c "idx"] ++ vec "oo" 18 ++ vec "on" 18),
   rcv B_RCH top (c "seg" :: vec "oo" 18),
   snd B_RCH top ((c "seg" + 1) :: vec "on" 18)] ++
  comp A (c "cidO") (ivW ++ nodeBlock (digW fun t => c "lo" t) (digW fun t => c "ro" t) ++
    digW (fun t => c "oo" t) ++ wordsOf (fun t => c "oox" t) 2) ++
  comp A (c "cidN") (ivW ++ nodeBlock (digW fun t => c "ln" t) (digW fun t => c "rn" t) ++
    digW (fun t => c "on" t) ++ wordsOf (fun t => c "onx" t) 2)

def table (D : Nat) : Table :=
  { width := L.width, constraints := constraints D, interactions, maxLog := 20 }
end Wsp

end StateM5a
