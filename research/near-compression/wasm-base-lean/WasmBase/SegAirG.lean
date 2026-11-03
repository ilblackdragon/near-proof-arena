import WasmBase.SegAirMP
import WasmBase.M3Air
import NearSpecV3.SHA512
/-!
# WasmBase.SegAirG — segments containing `memory.grow` / `memory.size` (`wasmBaseSegAirG`, E2E M4c)

`wasmBaseSegAirMP` fixes the memory size of a segment: the tree depth `D` (pub 103) and the block
count `nblk` (pub 104) are public constants, MEMB creates the bytes of the touched blocks at
`t_in`, MPATH (multiproof) updates the root of a depth-`D` tree.  `wasmBaseM3Air` has the chips for
`memory.size` / `memory.grow` (MEMG, the size message on channel space 8, MSZ, GINIT), but they are
not in the segment AIR.  `wasmBaseSegAirG` is `wasmBaseSegAirMP` (every table at its index,
unchanged) with three tables appended:

```
wasmBaseSegAirG = wasmBaseSegAirMP (0–31) ++ [MEMG (32), SEGG (33), MEMBG (34)]
```

## NEAR's limits: the depth changes at most once, 16 → 17

`prepare` instantiates every contract with `cfg.initialMemoryPages = 1024` pages (`Exec.lean`
`instantiate`; PV86 `NearCfg`) and `memory.grow` succeeds iff `old + n ≤ cfg.maxMemoryPages = 2048`
(`Exec.lean` `.memGrow`).  So `pages ∈ [1024, 2048]` at every boundary, `nblk = 64·pages ∈
[65536, 131072]`, and `WasmView.memDepth = log2 (max nblk 2 − 1) + 1` is **16 for 1024 pages and
17 for 1025–2048 pages**.  The depth increases at most once per call (the first successful grow
by `n ≥ 1`), from 16 to 17; `memory.grow 0` and later grows keep it.  The AIR supports exactly that
lift (`lift = D − D_in ∈ {0, 1}`, a lift needs `D_in = 16`); a general `D_in` would need the zero
root `Z_{D_in}` as a lookup (a 31-row table of `zrootW`), not needed for NEAR.

## The memory tree does not see `nblk`, only `D`

`WasmView.memLeaves s` pads the `nblk` real leaves with `zleaf = sha384 0¹⁰²⁴` up to `2^D`, and a
grown block is all-zero, so its leaf **is** `zleaf`: growing memory without changing `D` does not
change `memRootOf`; changing `D` from `d` to `d + 1` makes the root `nodeH (old root) Z_d`, with
`Z_0 = zleaf`, `Z_{k+1} = nodeH Z_k Z_k` (`zrootW`).  So `nblk` (pages) is a separate public
field (lane E's `WasmBnd.memPages`, unchanged), and `memRoot` stays `WasmView.memRootOf` (no
lane-E interface change).

## Public values (numPub 107)

| index | `wasmBaseSegAirMP` | here |
|---|---|---|
| 103 `pubDepth` | `D` | `D_out`: the depth MPATH works at (the out tree's) |
| 104 `pubNblk` | `nblk` | `nblk_in` (MEMB's bound `blk < nblk_in`) |
| 105 `pubNblkOut` | — | `nblk_out` |
| 106 `pubDepthIn` | — | `D_in` |

The verifier's statement check fixes `D_in = memDepth nblk_in`, `D_out = memDepth nblk_out`
(public values; `MemGeom` on both sides).  The chain check compares `(memRoot, nblk, D)` across a
cut, as before.

## The size message across the cut: SEGG (33), first row

The memory size is the M3 channel message `[8, 0, 0, pages, 0, 0, 0, tp]` (one live message).
SEGG produces `[8, 0, 0, pin, …, t_in]` and consumes the final `[8, 0, 0, pout, …, tz]`, with
`64·pin = nblk_in` and `64·pout = nblk_out`.  MEMG (M3's table, unchanged) consumes and re-produces
it at every `memory.size` / `memory.grow`.  CUTI/CUTO never carry space 8 (CUTO's space classes are
0, 2, 4, 5, 6, ≥ 16), so the size message crosses the cut only through the public `nblk` pair.
MSZ (M3's time-0 producer) is replaced by SEGG and not included.

## Grown blocks: MEMBG (34)

A touched block with `blk ≥ nblk_in` did not exist at `t_in`: it was grown in this segment.
MEMB must not create its bytes at `t_in` (a load before the grow would then succeed), so such a
block is a **MEMBG** block: 9 rows like MEMB's (8 × 128 bytes + the SHA-384 padding row), but

* the 128 bytes of a data row are **produced as zero at the grow's time `tg`** (count `kD`), and
  consumed at the end (`bo`, `tq`), as in MEMB;
* the padding row queries the grow `[tg, gold, gnew]` on M3's grow bus 213 (MEMG offers it, count
  `gm`, only on a successful grow) and checks `64·gold ≤ blk < 64·gnew` and `nblk_in ≤ blk`
  (R16); blocks strictly increase (as in MEMB);
* only the out-bytes are hashed (9 compressions); the **old leaf is the constant `zleaf`** (the
  block is a padding leaf of the in-tree), sent on bus 15 as `[blk, 0] ++ zleaf ++ out`.

So M3's per-byte GINIT is subsumed at block granularity (a touched grown block needs all its 1024
bytes at the end for the out-leaf hash anyway) and is not included.  An **untouched** grown block
costs nothing: it stays inside an untouched multiproof stub whose digest is the same in both
trees (`zleaf`/`Z_k`, bound by the old root).

## The root update for a depth increase: SEGG's lift row

With `lift = D_out − D_in = 1`, MPATH works at depth `D_out` but has **no** root row: SEGG's first
row is the root `(D_out, 0)`.  Its old children are the in-root (left, received on RCH as
`[0] ++ oL` from SEGB's `[0] ++ memIn`) and the constant `Z_{D_in}` (right).  Its new children are
`nL` (from the MPATH node `(D_in, 0)` on bus 17 if `ndL`, else `nL = oL`) and `nR` (from the node
`(D_in, 1)` if `ndR`, else `nR = Z_{D_in}`); it sends `[1] ++ H(nL ‖ nR)` on RCH, which SEGB
receives as `memOut` (`nbt = 1`).  One compression (the new side only; the old root
`H(memIn ‖ Z)` is never needed).  MPATH's own root row (`top`, `lvl = D_out`) cannot coexist:
both would receive a `[0] ++ …` RCH message and SEGB sends one.  With `lift = 0` SEGG's root part
is inactive and MPATH is exactly `wasmBaseSegAirMP`'s.

MPATH (table 20) and SEGB (table 0) are unchanged: MPATH's level range `[1, D]` reads pub 103,
which is `D_out` here; SEGB's RCH messages are the same.

## Cost

* `memory.grow` by `k` pages: one MEMG row; untouched grown blocks: 0 compressions;
* a touched grown block: 9 compressions (out-leaf; MEMB: 18 for a written block) plus its
  multiproof nodes (2 per touched node, as for any block);
* a depth increase: 1 compression (SEGG's new root) instead of MPATH's root row (2), and every
  touched path is one level longer (≤ 2 compressions per touched node on the new level: at most
  the 2 children of the root, which SEGG hashes).  So a lift segment costs **at most +1 compression
  and 0 extra rows** over the same segment at depth 17.

## Lean

`Main/SegGrow.lean`: row lemmas for SEGG/MEMBG (MEMG reuses `Main/M3Facts.lean`), the size message
as a channel fact, the zero-subtree root (`zrootW`, `zleafW`) as SHA-384 values, and the Merkle
lift lemma (`root (D+1) (l ++ zeros) = nodeH (root D l) (Z_D)`).
-/
namespace WasmBase
namespace Chips
namespace Seg
open Expr

/-- Public values added by `wasmBaseSegAirG`. -/
def pubNblkOut : Nat := 105
def pubDepthIn : Nat := 106
def numPubG : Nat := 107

namespace Grow

/-! ## SHA-384 constants: the zero leaf and the zero-subtree roots (64-bit words) -/

/-- The big-endian byte values of a word list (`SegSha.wbv`). -/
def wbv (ws : List Nat) : List Nat := (ws.flatMap (ArenaCore.Bytes.beN 8)).map UInt8.toNat
/-- The chip's compression on words (`SegSha.compressW`). -/
def cW (h ws : List Nat) : List Nat := NearSpecV3.SHA512.compress h (wbv ws)
/-- SHA-384 padding block of a whole-block message of `x` bits (`SegSha.padBlk`). -/
def padBlk (x : Nat) : List Nat := 2 ^ 63 :: List.replicate 13 0 ++ [x / 2 ^ 64 % 2 ^ 64, x % 2 ^ 64]
/-- The node padding words (`StateM5a.Sha512If.padW`). -/
def padN : List Nat := [2 ^ 63, 0, 0, 768]

/-- `zleaf = sha384 0¹⁰²⁴` as 6 words: 8 zero blocks and the padding block. -/
def zleafW : List Nat :=
  (cW ((List.replicate 8 (List.replicate 16 0)).foldl cW IV384) (padBlk 8192)).take 6

/-- The zero-subtree roots: `Z_0 = zleaf`, `Z_{k+1} = SHA-384 (Z_k ‖ Z_k)`. -/
def zrootW : Nat → List Nat
  | 0 => zleafW
  | k + 1 => let z := zrootW k; (cW IV384 (z ++ z ++ padN)).take 6

/-- A digest's 18 limbs as constant expressions. -/
def digC (ws : List Nat) : List Expr := (ws.flatMap wl).map Expr.c

/-- NEAR's only lift: from depth 16 (1024 pages) to 17. -/
def liftFrom : Nat := 16

end Grow

/-! ## SEGG (33): the size message across the cut, and the lift root -/

namespace SegG
def cols : List String :=
  ["pin", "pout", "tz", "lift", "ndL", "ndR", "cidN"] ++
  names "oL" 18 ++ names "nL" 18 ++ names "nR" 18 ++ names "pn" 18 ++ names "xn" 6
def c (s : String) : Expr := v (ix cols s)
def dig (pre : String) : List Expr := (names pre 18).map c
/-- `Z_16`'s limbs. -/
def zR : List Expr := Grow.digC (Grow.zrootW Grow.liftFrom)
def constraints : List Expr :=
  let lift := c "lift"
  [.first * (64 * c "pin" - pv pubNblk),
   .first * (64 * c "pout" - pv pubNblkOut),
   .first * (lift - pv pubDepth + pv pubDepthIn),
   (1 - Expr.first) * lift,
   bool lift, lift * (pv pubDepthIn - Expr.c Grow.liftFrom),
   bool (c "ndL"), bool (c "ndR"), c "ndL" * (1 - lift), c "ndR" * (1 - lift)] ++
  ((List.range 18).flatMap fun l =>
    [lift * (1 - c "ndL") * (c s!"nL{l}" - c s!"oL{l}"),
     lift * (1 - c "ndR") * (c s!"nR{l}" - zR.getD l 0)])
def inters : List Inter :=
  let lift := c "lift"
  [chSend (Expr.c memSizeSpace) 0 0 [c "pin", 0, 0, 0] (pv pubTIn) .first,
   chRecv (Expr.c memSizeSpace) 0 0 [c "pout", 0, 0, 0] (c "tz") .first,
   ⟨busRch, false, lift, [0] ++ dig "oL"⟩,
   ⟨busRch, true, lift, [1] ++ dig "pn"⟩,
   ⟨busNode, false, c "ndL", [pv pubDepthIn, 0] ++ dig "oL" ++ dig "nL"⟩,
   ⟨busNode, false, c "ndR", [pv pubDepthIn, 1] ++ zR ++ dig "nR"⟩] ++
  comp (c "cidN") (MpathMP.ivW ++ wordsAt c "nL" 6 ++ wordsAt c "nR" 6 ++
      [constW (2 ^ 63), zeroW, zeroW, constW 768] ++ wordsAt c "pn" 6 ++ wordsAt c "xn" 2) lift
def table : Table := ⟨"SEGG", cols, constraints, inters⟩
theorem cols_len : cols.length = 85 := by decide
end SegG

/-! ## MEMBG (34): touched grown blocks -/

namespace MembG
def cols : List String :=
  ["act"] ++ names "p" 9 ++ ["blk", "cidO", "tg", "gold", "gnew"] ++ names "bo" 128 ++ names "tq" 128 ++
  names "so5_" 16 ++ names "so2_" 16 ++ names "hiO" 24 ++ names "hoO" 24
def c (s : String) : Expr := v (ix cols s)
def n (s : String) : Expr := nv (ix cols s)
def p (i : Nat) : Expr := c s!"p{i}"
def kD : Expr := sumE ((List.range 8).map p)
def kP : Expr := p 8
def kk : Expr := sumE ((List.range 9).map fun i => Expr.c i * p i)
def addr (i : Nat) : Expr := 1024 * c "blk" + 128 * kk + Expr.c i

/-- The out-block words (MEMB's `blockW` on the `bo` columns). -/
def blockW : List W3 :=
  (List.range 16).map fun w =>
    let d := Memb.dataW (fun i => c s!"bo{i}") (c s!"so5_{w}") (c s!"so2_{w}") w
    (List.range 3).map fun l => kD * d.getD l 0 + kP * Expr.c ((Memb.padW w).getD l 0)

/-- MEMB's `splitR16` on the `bo` columns. -/
def splitR16 (cnt : Expr) : List Inter :=
  (List.range 16).flatMap fun w =>
    [r16 (8192 * c s!"so5_{w}") cnt, r16 (2048 * (c s!"bo{8 * w + 5}" - 32 * c s!"so5_{w}")) cnt,
     r16 (1024 * c s!"so2_{w}") cnt, r16 (16384 * (c s!"bo{8 * w + 2}" - 4 * c s!"so2_{w}")) cnt,
     byteQ 0 (c s!"so5_{w}") (c s!"so2_{w}") 0 cnt]

def constraints : List Expr :=
  let act := c "act"
  [bool act] ++ ((List.range 9).map fun i => bool (p i)) ++
  [sumE ((List.range 9).map p) - act,
   .first * act * (1 - p 0),
   .trans * p 8 * n "act" * (1 - n "p0"),
   .trans * (1 - act) * n "act",
   .last * act * (1 - p 8),
   .trans * n "act" * (1 - n "p0") * (n "blk" - c "blk"),
   .trans * n "act" * (1 - n "p0") * (n "tg" - c "tg")] ++
  ((List.range 8).map fun i => .trans * p i * (1 - nv (ix cols s!"p{i + 1}"))) ++
  ((List.range 24).map fun l => .trans * (1 - p 8) * act * (n s!"hiO{l}" - c s!"hoO{l}")) ++
  ((List.range 24).map fun l => p 0 * (c s!"hiO{l}" - Expr.c (ivLimbs.getD l 0)))

def inters : List Inter :=
  let act := c "act"
  ((List.range 128).flatMap fun i =>
    [chSend 3 (addr i) 0 [0, 0, 0, 0] (c "tg") kD,
     chRecv 3 (addr i) 0 [c s!"bo{i}", 0, 0, 0] (c s!"tq{i}") kD]) ++
  splitR16 kD ++
  comp (c "cidO") (wordsAt c "hiO" 8 ++ blockW ++ wordsAt c "hoO" 8) act ++
  [⟨busLeaf, true, p 8, [c "blk", 0] ++ Grow.digC Grow.zleafW ++ (names "hoO" 18).map c⟩,
   ⟨busGrow, true, p 8, [c "tg", c "gold", c "gnew"]⟩,
   r16 (n "blk" - c "blk" - 1) (.trans * p 8 * n "p0"),
   r16 (c "blk" - 64 * c "gold") (p 8),
   r16 (64 * c "gnew" - 1 - c "blk") (p 8),
   r16 (c "blk" - pv pubNblk) (p 8)]
def table : Table := ⟨"MEMBG", cols, constraints, inters⟩
set_option maxRecDepth 20000 in
theorem cols_len : cols.length = 351 := by decide
end MembG

end Seg
end Chips

open Chips in
/-- **The E2E M4c segment AIR with `memory.grow`**: `wasmBaseSegAirMP` (tables 0–31 unchanged) with
MEMG (32, `wasmBaseM3Air`'s), SEGG (33) and MEMBG (34) appended; 107 public values. -/
def wasmBaseSegAirG (nloc ngl : Nat) : Air where
  tables := (wasmBaseSegAirMP nloc ngl).tables ++ [MemG.table, Seg.SegG.table, Seg.MembG.table]
  numPub := Seg.numPubG

theorem segG_len (nloc ngl : Nat) : (wasmBaseSegAirG nloc ngl).tables.length = 35 := by
  simp [wasmBaseSegAirG, segMP_len]

/-- Every table of `wasmBaseSegAirMP` keeps its index. -/
theorem segG_same (nloc ngl t : Nat) (ht : t < 32) :
    (wasmBaseSegAirG nloc ngl).tables[t]? = (wasmBaseSegAirMP nloc ngl).tables[t]? := by
  simp only [wasmBaseSegAirG]
  rw [List.getElem?_append_left (by rw [segMP_len]; exact ht)]

theorem segG_t32 (nloc ngl : Nat) : (wasmBaseSegAirG nloc ngl).tables[32]? = some Chips.MemG.table := by
  simp only [wasmBaseSegAirG]
  rw [List.getElem?_append_right (by simp [segMP_len]), segMP_len]; rfl
theorem segG_t33 (nloc ngl : Nat) : (wasmBaseSegAirG nloc ngl).tables[33]? = some Chips.Seg.SegG.table := by
  simp only [wasmBaseSegAirG]
  rw [List.getElem?_append_right (by simp [segMP_len]), segMP_len]; rfl
theorem segG_t34 (nloc ngl : Nat) : (wasmBaseSegAirG nloc ngl).tables[34]? = some Chips.Seg.MembG.table := by
  simp only [wasmBaseSegAirG]
  rw [List.getElem?_append_right (by simp [segMP_len]), segMP_len]; rfl

end WasmBase
