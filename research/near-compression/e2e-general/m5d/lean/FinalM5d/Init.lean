import FinalM5d.Final

/-!
# FinalM5d.Init — the M5d INIT template AIR (claim intake → the `init` boundary)

`B_0 = view (init cb wb)` (lane E, `View.split`: phase 0, `ctxRoot = ctxD (.raw cb wb)`, every
other field empty). The template computes the two digests of `B_0` that depend on the chunk:

* `claimDigest = bdigest (pre ‖ u32 0 ‖ post)` — lane E's canonical statement encoding
  (`StmtEnc.claimDigest`, `encode_splice`: `pre = stmtPre`, `post = stmtPost`, the claim with an
  empty section B); the same message the FINAL template hashes, and what V_d recomputes;
* `ctxRoot = bdigest (0x00 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` with `cb = pre ‖ blocks ‖ post`
  (`= assemble ci secB secC` when `blocks = encList BlockRec.encode secB`) and `ℓ_B = |blocks|`.

Tables: `S384`, `RNG` (as in FINAL), `CLM` (one row per byte of `pre ‖ blocks ‖ post ‖ wb`, kinds in
that order; it feeds both messages: the statement message skips the `blocks` rows), `INI` (one row:
the counts, the length prefixes, the digests, the public values).

Public values: `claimDigest` (14 limbs), `ctxRoot` (14 limbs).
-/

namespace FinalM5d.InitT

open ZkFormal.Air

def ID_CTX : Nat := 3
def CTX_TAG : Nat := 0
/-- `(n_pre, n_blocks, n_claim, n_total, n_stmt)` from the last stream row. -/
def B_END : Nat := 7

def PV_CLAIM : Nat := 0
def PV_CTX : Nat := 14
/-- G-2: the main chunk's `prev_state_root` (`slotB2.prevStateRoot`), 16 big-endian byte pairs
(lane B's `pack2`), until the `.init` join carries it on `B_PSR`. -/
def PV_PSR : Nat := 28
def NUM_PUB : Nat := 44

/-! G-2 buses (INIT-local numbering, after the shared ones). -/
/-- `(pos, byte)`: a claim byte read by the section-B framing walk or the slot read. -/
def B_CB : Nat := 19
/-- `(start, end)` of section B: `(|pre|, |pre| + ℓ_B)`. -/
def B_LB : Nat := 20
/-- `(block, slot, inner start, inner length)` of every chunk slot of section B. -/
def B_SLOT : Nat := 21
/-- `(j, byte)`, `j < 32`: the main chunk's `prev_state_root` for lane B's INTAKE (the `.init` join;
documented in the leaf spec, not used by the standalone template). -/
def B_PSR : Nat := 22
/-- G-4: `(start, shard limbs (3), index)`: `INI` → `LAY` (the layout walk's start, the claim's shard
id, the main slot index `L.index shard`). -/
def B_LAY : Nat := 23
/-- G-4: `(index)`: `INI` → `BLK` (the main slot index the walk selects with). -/
def B_IX : Nat := 24
def NUM_BUSES_INIT : Nat := 25

/-! G-4 positions (claim-v3 framing, `ClaimV3.decodeClaimE`; `WalkSel.p_ch_eq` checks `P_CH`). -/
/-- The `u32` length of `chain_id`: after `borshBytes claimTag ‖ borshBytes statementIdV3 ‖ u32 pv`. -/
def P_CH : Nat := 60
/-- The chunk inner starts at `P_CH + 4 + |chain_id| + 32 + 4` (`chain_id`, `epoch_id`, `u32` length). -/
def P_CI : Nat := P_CH + 40
/-- `shard_id` (`u64`) inside a V4 / V5 chunk inner (`Wire.pChunkInner`: tag, 4 hashes, 2 `u64`). -/
def CI_SHARD : Nat := 145
/-- In section C: `u16 d ‖ u16 t ‖ u32 #epochs ‖ epoch₀ (hash ‖ u32 pv ‖ u64 height ‖ u32 ℓ ‖ layout…)`. -/
def POST_NEP : Nat := 4
def POST_LAY : Nat := 56

/-- Three little-endian limbs (`< 2^24`) of an 8-byte value: bytes 0..2, 3..5, 6..7. -/
def lim8 (b : Nat → Expr) (q : Nat) : Expr :=
  if q == 0 then b 0 + K 256 * b 1 + K 65536 * b 2
  else if q == 1 then b 3 + K 256 * b 4 + K 65536 * b 5
  else b 6 + K 256 * b 7

namespace Clm
def L : Layout :=
  [("act", 1), ("kc", 1), ("ks", 1), ("b", 1), ("ka", 1), ("kb", 1), ("kp", 1), ("kw", 1),
   ("na", 1), ("nb", 1), ("nc", 1), ("rd", 1)]
def T : Cols := ⟨L⟩
def act := T.c "act"
def ka := T.c "ka"
def kb := T.c "kb"
def kp := T.c "kp"
def kw := T.c "kw"
def constraints : List Expr :=
  actPrefix T ++ (["ka", "kb", "kp", "kw"].map fun s => bool (T.c s)) ++
  [ ka + kb + kp + kw - act,
    .isFirst * (ka - 1), .isFirst * T.c "kc", .isFirst * T.c "ks",
    .isFirst * T.c "na", .isFirst * T.c "nb", .isFirst * T.c "nc",
    contRow T * (T.n "kc" - T.c "kc" - 1),
    contRow T * (T.n "ks" - T.c "ks" - ka - kp),
    contRow T * (T.n "na" - T.c "na" - ka),
    contRow T * (T.n "nb" - T.c "nb" - kb),
    contRow T * (T.n "nc" - T.c "nc" - ka - kb - kp),
    -- kinds in the order pre, blocks, post, witness; pre, blocks, post are non-empty
    contRow T * ka * (1 - T.n "ka" - T.n "kb"),
    contRow T * kb * (1 - T.n "kb" - T.n "kp"),
    contRow T * kp * (1 - T.n "kp" - T.n "kw"),
    contRow T * kw * (1 - T.n "kw"),
    endRow T * (ka + kb),
    -- G-2: claim bytes may be read by the walks (G-4: also `pre` and `post`), never witness bytes
    bool (T.c "rd"), T.c "rd" * (1 - ka - kb - kp) ]
def interactions : List Interaction :=
  [ snd B_SB (ka + kp) [K ID_CLAIM, T.c "ks" + K 4 * kp, T.c "b"],
    snd B_CB (T.c "rd") [T.c "kc", T.c "b"],
    snd B_SB act [K ID_CTX, K 9 + T.c "kc", T.c "b"],
    snd B_END (endRow T) [T.c "na" + ka, T.c "nb" + kb, T.c "nc" + ka + kb + kp, T.c "kc" + 1,
      T.c "ks" + ka + kp] ]
def table : Table := { width := L.width, constraints, interactions, maxLog := 24 }
end Clm

/-! ## `BLK`: the framing walk over section B (G-2)

`blocks = encList BlockRec.encode secB` (`ClaimV3`): `u32 n ‖ (u8 hv ‖ prev_hash[32] ‖ u32 l₁ ‖ lite ‖
u32 l₂ ‖ rest ‖ u32 m ‖ (u32 lₛ ‖ inner ‖ u64 h)^m)^n`. One row per field group: the count row `kn`
(first row), a block-header row `kh` (`hv`, `prev_hash`, both length-prefixed byte strings, the slot
count: end = start + 45 + l₁ + l₂), a slot row `ks` (end = start + 12 + lₛ). Rows are contiguous
(next start = end), the first starts at `|pre|`, the last ends at `|pre| + ℓ_B` (`B_LB` from `INI`):
so `ℓ_B` is exactly the span of the block vector `decodeClaimE` reads (`dBlock`, `dSlot`). Lengths
are read through `B_CB` from `CLM`'s section-B bytes (`u32`, top byte 0: lengths `< 2^24`); the
remaining-block / remaining-slot counters `rb`, `rs` with zero flags force the grammar. Every slot
row may send `SLOT (block, slot, inner start, inner length)` (bit `sel`; `INI` receives the main
slot's once). -/
namespace Blk
def L : Layout :=
  [("act", 1), ("kn", 1), ("kh", 1), ("ks", 1), ("s", 1), ("e", 1), ("E", 1), ("y", 12), ("rb", 1),
   ("rs", 1), ("zr", 1), ("ir", 1), ("zs", 1), ("is", 1), ("bi", 1), ("si", 1), ("sp", 3), ("sel", 1),
   ("ix", 1), ("hb", 3), ("z", 8), ("tgt", 1), ("itg", 1), ("eq", 1), ("dv", 3), ("g", 1)]
def T : Cols := ⟨L⟩
def act := T.c "act"
def kn := T.c "kn"
def kh := T.c "kh"
def ks := T.c "ks"
/-- The `u32` read `q` (bytes `y[4q..4q+3]`, top byte 0). -/
def v (q : Nat) : Expr := T.c "y" (4 * q) + K 256 * T.c "y" (4 * q + 1) + K 65536 * T.c "y" (4 * q + 2)
def vn (q : Nat) : Expr := T.n "y" (4 * q) + K 256 * T.n "y" (4 * q + 1) + K 65536 * T.n "y" (4 * q + 2)
def s := T.c "s"
/-- Read positions: `s` (count / slot length) or `s + 33` (`l₁`), `s + 37 + l₁`, `s + 41 + l₁ + l₂`. -/
def pos (q : Nat) : Expr :=
  if q == 0 then s + K 33 * kh else if q == 1 then s + K 37 + v 0 else s + K 41 + v 0 + v 1
/-- G-4: the 8 bytes `z` are a block's height (`inner_lite[0..8]`, at `s + 37`) on a header row and
a slot's `height_included` (after its inner, at `s + 4 + lₛ`) on a slot row. -/
def zpos : Expr := kh * (s + K 37) + ks * (s + K 4 + v 0)
def zl (q : Nat) : Expr := lim8 (fun j => T.c "z" j) q
/-- Slot row: `height_included − height` of its block, limb `q`. -/
def dl (q : Nat) : Expr := zl q - T.c "hb" q
/-- Slot row: `slot index − main index` (`si` is 1-based). -/
def ti : Expr := T.c "si" - 1 - T.c "ix"
def eq := T.c "eq"
def tgt := T.c "tgt"
def g := T.c "g"
def sel := T.c "sel"
/-- **G-4: the main-slot selection (`walkSegment` on a single-epoch segment, `WalkSel`).** `tgt`: a
slot row whose index is `ix` (`= L.index shard`, from `INI` on `B_IX`); `eq`: a target slot that is
new (`height_included = height` of its block, all three limbs); `g`: a slot was selected on an
earlier row; `sel = eq · (1 − g)`: the first new target slot; exactly one row is selected. -/
def selConstraints : List Expr :=
  ((List.range 3).map fun q => kh * (T.c "hb" q - zl q)) ++
  ((List.range 3).map fun q => contRow T * T.n "ks" * (T.n "hb" q - T.c "hb" q)) ++
  [ bool tgt, tgt * (1 - ks), tgt * ti, ks * (1 - tgt) * (ti * T.c "itg" - 1),
    bool eq, eq * (1 - tgt) ] ++
  ((List.range 3).map fun q => eq * dl q) ++
  [ tgt * (1 - eq) * (sumE ((List.range 3).map fun q => dl q * T.c "dv" q) - 1),
    sel - eq * (1 - g), .isFirst * g, contRow T * (T.n "g" - g - sel), endRow T * (g + sel - 1),
    contRow T * (T.n "ix" - T.c "ix") ]
def constraints : List Expr :=
  actPrefix T ++ (["kn", "kh", "ks", "zr", "zs"].map fun c => bool (T.c c)) ++
  [ kn + kh + ks - act,
    .isFirst * (kn - act), contRow T * T.n "kn",
    act * T.c "y" 3, kh * T.c "y" 7, kh * T.c "y" 11,
    -- field ends
    act * (T.c "e" - s - (K 4 * kn + kh * (K 45 + v 0 + v 1) + ks * (K 12 + v 0))),
    contRow T * (T.n "s" - T.c "e"), contRow T * (T.n "E" - T.c "E"),
    s - (T.c "sp" 0 + K 256 * T.c "sp" 1 + K 65536 * T.c "sp" 2),
    -- counters
    kn * (T.c "rb" - v 0), kn * T.c "rs",
    contRow T * (T.n "rb" - T.c "rb" + T.n "kh"),
    contRow T * (T.n "rs" - T.n "kh" * vn 2 - T.n "ks" * (T.c "rs" - 1)),
    T.c "zr" * T.c "rb", act * (1 - T.c "zr") * (T.c "rb" * T.c "ir" - 1),
    T.c "zs" * T.c "rs", act * (1 - T.c "zs") * (T.c "rs" * T.c "is" - 1),
    -- the grammar: a slot follows iff slots remain; otherwise a block header, iff blocks remain
    contRow T * (1 - T.c "zs") * (1 - T.n "ks"), contRow T * T.c "zs" * T.n "ks",
    contRow T * T.c "zs" * T.c "zr",
    endRow T * (1 - T.c "zs"), endRow T * (1 - T.c "zr"), endRow T * (T.c "e" - T.c "E"),
    -- block / slot indices (1-based on their rows)
    .isFirst * T.c "bi", contRow T * (T.n "bi" - T.c "bi" - T.n "kh"),
    kh * T.c "si", contRow T * (T.n "si" - T.n "ks" * (T.c "si" + 1)) ] ++ selConstraints
def interactions : List Interaction :=
  [ rcv B_LB kn [s, T.c "E"], rcv B_IX kn [T.c "ix"] ] ++
  (List.range 4).map (fun j => rcv B_CB act [pos 0 + K j, T.c "y" j]) ++
  (List.range 4).map (fun j => rcv B_CB kh [pos 1 + K j, T.c "y" (4 + j)]) ++
  (List.range 4).map (fun j => rcv B_CB kh [pos 2 + K j, T.c "y" (8 + j)]) ++
  [ snd B_SLOT (T.c "sel") [T.c "bi" - 1, T.c "si" - 1, s + K 4, v 0] ] ++
  (List.range 3).map (fun j => rcv B_R8 act [T.c "sp" j]) ++
  (List.range 8).map (fun j => rcv B_CB (kh + ks) [zpos + K j, T.c "z" j])
def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Blk

/-! ## `LAY`: `L.index shard` from the layout bytes (G-4)

The claim's single epoch record (section C, `INI` checks `#epochs = 1`) carries the shard layout
at `|pre| + ℓ_B + 56`. `decodeLayout` (V2 / V3, `Layout.lean`) reads `u8 tag ‖ boundary_accounts ‖
shard_ids ‖ id_to_index_map ‖ …`; `Layout.index s` is the value of the **first** `id_to_index` pair
with key `s`. One row per field group: head `k0` (`tag ∈ {2, 3}`, `u32` count), a boundary account
`kb` (`u32 ℓ ‖ bytes`), the shard ids `ki` (`u32 n ‖ 8n bytes`), the map count `km`, a pair `kp`
(`u64 key ‖ u64 value`). Rows are contiguous from the start `INI` sends on `B_LAY`; the grammar is
forced by the remaining-count flags; the walk ends after the last pair. `eq`: a pair whose key equals
the claim's shard id (three limbs, `sh`); `hit = eq · (1 − g)` is the first one (exactly one), and
its value is `ix` (`< 256`, a completeness bound). -/
namespace Lay
def L : Layout :=
  [("act", 1), ("k0", 1), ("kb", 1), ("ki", 1), ("km", 1), ("kp", 1), ("s", 1), ("e", 1), ("y", 16),
   ("rb", 1), ("rp", 1), ("zr", 1), ("ir", 1), ("zp", 1), ("ip", 1), ("sh", 3), ("ix", 1), ("eq", 1),
   ("dv", 3), ("hit", 1), ("g", 1), ("sp", 3)]
def T : Cols := ⟨L⟩
def act := T.c "act"
def k0 := T.c "k0"
def kb := T.c "kb"
def ki := T.c "ki"
def km := T.c "km"
def kp := T.c "kp"
def s := T.c "s"
def y (j : Nat) : Expr := T.c "y" j
/-- The `u32` at `s` (`kb`, `ki`, `km`) and at `s + 1` (`k0`), top byte 0. -/
def u : Expr := y 0 + K 256 * y 1 + K 65536 * y 2
def w : Expr := y 1 + K 256 * y 2 + K 65536 * y 3
/-- A pair row: key limb `q` minus the shard id's. -/
def dl (q : Nat) : Expr := lim8 y q - T.c "sh" q
def eq := T.c "eq"
def g := T.c "g"
def hit := T.c "hit"
def constraints : List Expr :=
  actPrefix T ++ (["k0", "kb", "ki", "km", "kp", "zr", "zp", "eq"].map fun c => bool (T.c c)) ++
  [ k0 + kb + ki + km + kp - act,
    .isFirst * (k0 - 1), contRow T * T.n "k0",
    k0 * (y 0 - 2) * (y 0 - 3), k0 * y 4, (kb + ki + km) * y 3,
    act * (T.c "e" - s - (K 5 * k0 + kb * (K 4 + u) + ki * (K 4 + K 8 * u) + K 4 * km + K 16 * kp)),
    contRow T * (T.n "s" - T.c "e"),
    s - (T.c "sp" 0 + K 256 * T.c "sp" 1 + K 65536 * T.c "sp" 2),
    -- counters and the grammar: head, boundaries (while `rb > 0`), shard ids, map count, pairs
    k0 * (T.c "rb" - w), contRow T * (T.n "rb" - T.c "rb" + T.n "kb"),
    km * (T.c "rp" - u), contRow T * (1 - T.n "km") * (T.n "rp" - T.c "rp" + T.n "kp"),
    T.c "zr" * T.c "rb", act * (1 - T.c "zr") * (T.c "rb" * T.c "ir" - 1),
    T.c "zp" * T.c "rp", act * (1 - T.c "zp") * (T.c "rp" * T.c "ip" - 1),
    contRow T * (k0 + kb) * (1 - T.c "zr") * (1 - T.n "kb"),
    contRow T * (k0 + kb) * T.c "zr" * (1 - T.n "ki"),
    contRow T * ki * (1 - T.n "km"),
    contRow T * (km + kp) * (1 - T.c "zp") * (1 - T.n "kp"),
    contRow T * (km + kp) * T.c "zp",
    endRow T * (1 - km - kp), endRow T * (1 - T.c "zp"),
    -- the first pair with key = shard id
    eq * (1 - kp) ] ++
  ((List.range 3).map fun q => eq * dl q) ++
  [ kp * (1 - eq) * (sumE ((List.range 3).map fun q => dl q * T.c "dv" q) - 1),
    hit - eq * (1 - g), .isFirst * g, contRow T * (T.n "g" - g - hit), endRow T * (g + hit - 1),
    hit * (y 8 - T.c "ix") ] ++
  ((List.range 7).map fun j => hit * y (9 + j)) ++
  ((List.range 3).map fun q => contRow T * (T.n "sh" q - T.c "sh" q)) ++
  [ contRow T * (T.n "ix" - T.c "ix") ]
def interactions : List Interaction :=
  [ rcv B_LAY k0 [s, T.c "sh" 0, T.c "sh" 1, T.c "sh" 2, T.c "ix"] ] ++
  (List.range 4).map (fun j => rcv B_CB act [s + K j, y j]) ++
  [ rcv B_CB (k0 + kp) [s + K 4, y 4] ] ++
  (List.range 11).map (fun j => rcv B_CB kp [s + K (5 + j), y (5 + j)]) ++
  (List.range 3).map (fun j => rcv B_R8 act [T.c "sp" j])
def table : Table := { width := L.width, constraints, interactions, maxLog := 12 }
end Lay

namespace Ini
def L : Layout :=
  [("act", 1), ("na", 1), ("nb", 1), ("nc", 1), ("nt", 1), ("ns", 1), ("pa", 3), ("lb", 3),
   ("lc", 3), ("cd", 48), ("xd", 48), ("b2i", 1), ("mi", 1), ("sst", 1), ("sln", 1), ("slx", 3),
   ("psr", 32), ("cy", 4), ("sh", 8)]
def T : Cols := ⟨L⟩
def act := T.c "act"
def le3 (s : String) : Expr := T.c s 0 + K 256 * T.c s 1 + K 65536 * T.c s 2
def b4 (s : String) (j : Nat) : Expr := if j < 3 then T.c s j else 0
def constraints : List Expr :=
  [bool act, .isFirst * (act - 1), .isTransition * T.n "act",
   act * (T.c "na" - le3 "pa"), act * (T.c "nb" - le3 "lb"), act * (T.c "nc" - le3 "lc")] ++
  eqs act ((List.range 14).map fun i => P (PV_CLAIM + i)) (limbs3 (T.cs "cd" 42)) ++
  eqs act ((List.range 14).map fun i => P (PV_CTX + i)) (limbs3 (T.cs "xd" 42)) ++
  -- G-2: the main chunk slot's `prev_state_root` (inner bytes 33..65, V5), `sln ≥ 65`
  [act * (T.c "sln" - K 65 - (T.c "slx" 0 + K 256 * T.c "slx" 1 + K 65536 * T.c "slx" 2))] ++
  (List.range 16).map (fun t => act * (P (PV_PSR + t) - (K 256 * T.c "psr" (2 * t) + T.c "psr" (2 * t + 1)))) ++
  [act * T.c "cy" 3]
/-- G-4: `|chain_id|` (the `u32` at `P_CH`). -/
def lc : Expr := T.c "cy" 0 + K 256 * T.c "cy" 1 + K 65536 * T.c "cy" 2
/-- G-4: the first byte of section C. -/
def post : Expr := T.c "na" + T.c "nb"
def interactions : List Interaction :=
  [ rcv B_END act [T.c "na", T.c "nb", T.c "nc", T.c "nt", T.c "ns"] ] ++
  (List.range 4).map (fun j => snd B_SB act [K ID_CLAIM, T.c "na" + K j, K 0]) ++
  [ snd B_SB act [K ID_CTX, K 0, K CTX_TAG] ] ++
  (List.range 4).map (fun j => snd B_SB act [K ID_CTX, K (1 + j), b4 "lb" j]) ++
  (List.range 4).map (fun j => snd B_SB act [K ID_CTX, K (5 + j), b4 "lc" j]) ++
  [ rcv B_SD act ([K ID_CLAIM, K 4 + T.c "ns"] ++ T.cs "cd" 48),
    rcv B_SD act ([K ID_CTX, K 9 + T.c "nt"] ++ T.cs "xd" 48) ] ++
  (["pa", "lb", "lc"].flatMap fun s => (List.range 3).map fun j => rcv B_R8 act [T.c s j]) ++
  [ snd B_LB act [T.c "na", T.c "na" + T.c "nb"],
    rcv B_SLOT act [T.c "b2i", T.c "mi", T.c "sst", T.c "sln"] ] ++
  (List.range 32).map (fun j => rcv B_CB act [T.c "sst" + K (33 + j), T.c "psr" j]) ++
  (List.range 3).map (fun j => rcv B_R8 act [T.c "slx" j]) ++
  -- G-4: the claim's shard id, `#epochs = 1`, the layout walk and the main index
  (List.range 4).map (fun j => rcv B_CB act [K (P_CH + j), T.c "cy" j]) ++
  (List.range 8).map (fun j => rcv B_CB act [lc + K (P_CI + CI_SHARD + j), T.c "sh" j]) ++
  (List.range 4).map (fun j => rcv B_CB act [post + K (POST_NEP + j), K (if j == 0 then 1 else 0)]) ++
  [ snd B_LAY act [post + K POST_LAY, lim8 (fun j => T.c "sh" j) 0, lim8 (fun j => T.c "sh" j) 1, lim8 (fun j => T.c "sh" j) 2, T.c "mi"],
    snd B_IX act [T.c "mi"] ]
def table : Table := { width := L.width, constraints, interactions, maxLog := 4 }
end Ini

def initNames : List String := ["S384", "RNG", "CLM", "BLK", "INI", "LAY"]

def initAir : Air :=
  { tables := [S384.table, Rng.table, Clm.table, Blk.table, Ini.table, Lay.table],
    numBuses := NUM_BUSES_INIT, numPub := NUM_PUB }

def initLayouts : List (String × Layout) :=
  [("S384", S384.L), ("RNG", Rng.L), ("CLM", Clm.L), ("BLK", Blk.L), ("INI", Ini.L), ("LAY", Lay.L)]

end FinalM5d.InitT
