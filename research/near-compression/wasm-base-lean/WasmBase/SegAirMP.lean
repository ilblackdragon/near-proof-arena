import WasmBase.SegAir
/-!
# WasmBase.SegAirMP — the segment AIR with a batched Merkle multiproof (`wasmBaseSegAirMP`, E2E M4b)

`wasmBaseSegAir` (M4) updates the memory root block by block: `MPATH` (table 20) has one row per
touched block and tree level, re-hashing the block's whole old and new path, chained by the root
chain RCH (bus 16).  For `segbench(24000)` (32 touched blocks, depth `D = 16`) that is
`32 · 2 · 16 = 1,024` of the segment's 1,610 SHA-512 compressions.

`wasmBaseSegAirMP` is the same AIR except table 20, which becomes **`MPATH` as a multiproof**: one
row per *touched tree node* `(lvl, idx)` (`1 ≤ lvl ≤ D`), hashing it once with its old children and
once with its new children.  The upper levels are shared: 32 contiguous blocks touch
`16 + 8 + 4 + 2 + 1 + 11 = 42` nodes, i.e. 84 compressions instead of 1,024.

## The node row

Columns: `act`, `top` (the root), `ro` (unchanged node), `lvl`, `idx`, per child `X ∈ {L, R}` the
flags `lfX` (touched leaf) / `ndX` (touched inner node), the leaf's read-only flag `rX` (a message
field only), the old/new child digests `oX`/`nX` (18 limbs each), the old/new output `po`/`pn`
(+ the two truncated SHA-512 words `xo`/`xn`), and the compression ids `cidO`/`cidN`.

* a touched child `X` (side `s = 0` for `L`, `1` for `R`) is **received**: at `lvl = 1` from MEMB's
  padding row on bus 15 (`[2·idx + s, rX] ++ oX ++ nX`, MEMB's message unchanged), above from the
  child's node row on the new node bus 17 (`[lvl − 1, 2·idx + s] ++ oX ++ nX`);
* an untouched child is a **witness digest used for both trees**: `(1 − lfX − ndX)·(nX − oX) = 0`;
* every non-root node row **sends** `[lvl, idx] ++ po ++ pn` on bus 17 (count `act − top`);
* the root row (`top`: `lvl = D`, `idx = 0`) receives `[0] ++ po` and sends `[1] ++ pn` on RCH
  (bus 16), so `SEGB` is unchanged: it sends `[0] ++ memIn` and receives `[nbt] ++ memOut`; with a
  root row `nbt = 1`, without one (no touched block) `nbt = 0` and `memOut = memIn`;
* `po = H(oL ‖ oR)` always, `pn = H(nL ‖ nR)` unless `ro`, and `ro` forces `nL = oL`, `nR = oR`,
  `pn = po`;
* `lvl` is range-checked to `[1, D]` by two 5-bit decompositions on the row itself,
  `lvl − 1 = Σ 2^i·a_i`, `D − lvl = Σ 2^i·b_i` (local, so the Lean argument needs no R16 lookup;
  `D ≤ 30`); a touched leaf needs `lvl = 1`.

No transition constraint: the rows may be in any order.

## Soundness sketch (the Lean statement is `WasmBase/Main/SegMP.lean`)

* *Unique root.*  On RCH the only senders are SEGB's `[0] ++ memIn` and the root rows' `[1] ++ pn`;
  the only receivers SEGB's `[nbt] ++ memOut` and the root rows' `[0] ++ po`.  A root row's
  `[1] ++ pn` can only be received by SEGB, so there is at most one root row; with one, `po = memIn`,
  `nbt = 1`, `pn = memOut`.
* *Every node row hangs below the root, at a unique position.*  A non-root row's message must be
  received by a row one level up (no receiver has level `> D` or `< 1`), whose child index is
  `2·idx + s`; top-down, `idx < 2^(D − lvl)` (as naturals) and two rows at the same `(lvl, idx)`
  would send two copies of a message only one receive (the unique parent's side `s`) takes.
* *Touched cannot be marked untouched*: the child's message (MEMB's leaf, or the child row's) would
  not be received.  *Duplicated nodes* are unbalanced, as above.  *Levels* are fixed by the
  messages (`lvl − 1` in the receive).
* So the rows form a partial tree whose leaves are exactly MEMB's touched blocks and whose stubs are
  the untouched-child witnesses; the old root is its digest with the old leaves, the new root with
  the new leaves (`mp_tree`).
-/
namespace WasmBase
namespace Chips
namespace Seg

/-- The node bus of the multiproof: `[lvl, idx] ++ old ++ new`. -/
def busNode : Nat := 17

namespace MpathMP
def cols : List String :=
  ["act", "top", "ro", "lvl", "idx", "lfL", "ndL", "lfR", "ndR", "rL", "rR", "cidO", "cidN"] ++
  names "oL" 18 ++ names "nL" 18 ++ names "oR" 18 ++ names "nR" 18 ++ names "po" 18 ++ names "pn" 18 ++
  names "xo" 6 ++ names "xn" 6 ++ names "a" 5 ++ names "b" 5
def c (s : String) : Expr := v (ix cols s)
def dig (pre : String) : List Expr := (names pre 18).map c
/-- The inner-node block `left48 ‖ right48` with its SHA-384 padding (96 bytes = 768 bits). -/
def nodeBlock (l r : String) : List W3 :=
  wordsAt c l 6 ++ wordsAt c r 6 ++ [constW (2 ^ 63), zeroW, zeroW, constW 768]
def ivW : List W3 := IV384.map constW
/-- `Σ_{i<5} 2^i · x_i` over the bit columns `x0 … x4`. -/
def bits5 (x : String) : Expr := sumE ((List.range 5).map fun i => Expr.c (2 ^ i) * c s!"{x}{i}")
def constraints : List Expr :=
  let act := c "act"
  [bool act, bool (c "top"), bool (c "ro"), bool (c "lfL"), bool (c "ndL"), bool (c "lfR"), bool (c "ndR"),
   (1 - act) * c "top", (1 - act) * c "ro", (1 - act) * c "lfL", (1 - act) * c "ndL",
   (1 - act) * c "lfR", (1 - act) * c "ndR",
   c "lfL" * c "ndL", c "lfR" * c "ndR",
   c "lfL" * (c "lvl" - 1), c "lfR" * (c "lvl" - 1),
   c "top" * (c "lvl" - pv pubDepth), c "top" * c "idx",
   c "act" * (c "lvl" - 1 - bits5 "a"), c "act" * (pv pubDepth - c "lvl" - bits5 "b")] ++
  ((List.range 5).flatMap fun i => [bool (c s!"a{i}"), bool (c s!"b{i}")]) ++
  ((List.range 18).flatMap fun l =>
    [(1 - c "lfL" - c "ndL") * (c s!"nL{l}" - c s!"oL{l}"),
     (1 - c "lfR" - c "ndR") * (c s!"nR{l}" - c s!"oR{l}"),
     c "ro" * (c s!"nL{l}" - c s!"oL{l}"), c "ro" * (c s!"nR{l}" - c s!"oR{l}"),
     c "ro" * (c s!"pn{l}" - c s!"po{l}")])
def inters : List Inter :=
  let act := c "act"; let top := c "top"; let i2 := 2 * c "idx"
  [⟨busLeaf, false, c "lfL", [i2, c "rL"] ++ dig "oL" ++ dig "nL"⟩,
   ⟨busLeaf, false, c "lfR", [i2 + 1, c "rR"] ++ dig "oR" ++ dig "nR"⟩,
   ⟨busNode, false, c "ndL", [c "lvl" - 1, i2] ++ dig "oL" ++ dig "nL"⟩,
   ⟨busNode, false, c "ndR", [c "lvl" - 1, i2 + 1] ++ dig "oR" ++ dig "nR"⟩,
   ⟨busNode, true, act - top, [c "lvl", c "idx"] ++ dig "po" ++ dig "pn"⟩,
   ⟨busRch, false, top, [0] ++ dig "po"⟩,
   ⟨busRch, true, top, [1] ++ dig "pn"⟩] ++
  comp (c "cidO") (ivW ++ nodeBlock "oL" "oR" ++ wordsAt c "po" 6 ++ wordsAt c "xo" 2) act ++
  comp (c "cidN") (ivW ++ nodeBlock "nL" "nR" ++ wordsAt c "pn" 6 ++ wordsAt c "xn" 2) (act * (1 - c "ro"))
def table : Table := ⟨"MPATH", cols, constraints, inters⟩
end MpathMP

end Seg
end Chips

open Chips in
/-- **The E2E M4b segment AIR**: `wasmBaseSegAir` with table 20 (`MPATH`) replaced by the batched
Merkle multiproof `Seg.MpathMP.table`. -/
def wasmBaseSegAirMP (nloc ngl : Nat) : Air where
  tables := (wasmBaseSegAir nloc ngl).tables.set 20 Seg.MpathMP.table
  numPub := Seg.numPub

theorem segMP_len (nloc ngl : Nat) : (wasmBaseSegAirMP nloc ngl).tables.length = 32 := by
  simp [wasmBaseSegAirMP, seg_air_len]

/-- Every table but 20 is `wasmBaseSegAir`'s, at the same index. -/
theorem segMP_same (nloc ngl t : Nat) (ht : t ≠ 20) :
    (wasmBaseSegAirMP nloc ngl).tables[t]? = (wasmBaseSegAir nloc ngl).tables[t]? := by
  simp [wasmBaseSegAirMP, Ne.symm ht]

theorem segMP_t20 (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables[20]? = some Chips.Seg.MpathMP.table := by
  simp [wasmBaseSegAirMP, seg_air_len]

end WasmBase
