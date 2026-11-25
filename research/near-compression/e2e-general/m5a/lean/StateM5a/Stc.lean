import StateM5a.Tmpl

/-!
# StateM5a.Stc — B-T3: the `STC` table (open / close the 42-B `stRoot` in-circuit)

The state half of a STATE / RT-resume leaf (`StHalfC.StcOK`, plan §3.5 "the `stRoot` interface")
needs lane B's rows to **open** the input boundary's `stRoot` and **close** the output's. `stRoot`
is `bdigest (ser c)` (`StateView.StCommit.ser`, 139 bytes: `[tag] ‖ ws(48) ‖ u64 wsLen ‖ trie(32) ‖
u64 idx ‖ rest(42)`), i.e. SHA-384 of 139 bytes (2 blocks after FIPS padding) truncated to 42 B.
One active `STC` row does both:

* **input side**: the message bytes `b` (139 columns), the padded message's 32 words built from them
  (`wordW`), two compressions on `IF384` (`IV384 → hi → di ‖ xi`), the digest's 48 bytes `ri`;
* **output side**: the output message is the input's with the tag, `ws` and `rest` replaced
  (`ot`, `ow`, `or`; bytes 49–96 = `u64 wsLen ‖ trie ‖ u64 idx` are the input's columns), two
  compressions (`ho`, `do ‖ xo`), digest bytes `ro`;
* `ws` of the input = the segment's public `R_in` (values 17–34, the chip limbs of 6 words), `ws` of
  the output = `R_out` (35–52); `wsLen` (u64 LE, bytes 49–56) = public value 16, and
  **`wsLen ≤ 2^D`**: `2^D − wsLen = g₀ + 256 g₁ + 65536 g₂` with bytes `g`; B-T4: the opened `trie`
  (bytes 57–88) = the public `prev_state_root` (values 0–15, `trieEqs`);
* **B-T5: the `done` close** (finding M14-1; `modeEqs`): a boolean `fin` is `1` exactly when the
  output tag is `3`; then the output record is the no-overlay one — `ws` = the empty depth-24 tree's
  root (constant bytes `emptyB`), `wsLen = 0`, trie `0^32` (the output's bytes 49–88 are the columns
  `om` = `(act − fin) · b`), `idx` and `rest` as before — instead of `close c R_out`;
* **`STMQ`** (211, engine → state, received): `[r_in (14 limbs), tag_out, rest_out (14 limbs)]` —
  `r_in` = the first 42 bytes of the input digest, `tag_out = ot`, `rest_out` = `or`;
* **`STMA`** (212, state → engine, sent): `[r_out (14 limbs), tag_in, rest_in (14 limbs)]`.

A limb of a 42-B digest is 3 bytes big-endian (`65536·b₃ᵢ + 256·b₃ᵢ₊₁ + b₃ᵢ₊₂`, lane E's U-10 /
lane F's `engF.stRoot` bytes in order).

**Bytes and chip limbs.** The chip reads a 64-bit word as limbs `[0,21) [21,42) [42,64)`; byte 5
(bits 16–23, big-endian byte index) and byte 2 (bits 40–47) straddle limb boundaries, so every
word whose bytes are columns has 4 split columns `lo5, hi3` (byte 5 = `lo5 + 32·hi3`) and `lo2, hi6`
(byte 2 = `lo2 + 4·hi6`). Ranges come from the table's own byte table `SRNG` (bus 31; a copy of
`RNG`, so the M5a theorems' premise "extra tables never touch `RNG`" still holds): a byte column
`x` is looked up once (`x < 256`), a high part once (`< 256`; the split equation then bounds it),
a low `k`-bit part twice (`x < 256` and `2^(8−k)·x < 256`).

Constraints are gated by `act` (degree 2); interactions have multiplicity `act`.
-/

namespace StateM5a

open ZkFormal.Air

/-- `STC`'s byte table bus. -/
def B_SRNG : Nat := NUM_BUSES_ST
/-- Cross-lane `stRoot` buses (plan §3.5, lane B's B-T2 proposal). -/
def B_STMQ : Nat := 211
def B_STMA : Nat := 212

namespace Stc

/-- Length of the serialized commitment. -/
def NB : Nat := 139
/-- Words of the 2-block padded message that hold message bytes (bytes `0 … 143`). -/
def NWD : Nat := 18

/-- The SHA-384 padding bytes of a 139-byte message (positions `139 … 255`): `0x80`, zeros, the
128-bit big-endian bit length `1112 = 0x0458`. -/
def padByte (p : Nat) : Nat :=
  if p = 139 then 128 else if p = 254 then 4 else if p = 255 then 88 else 0

/-- The constant split parts of a padding word `w` (`q`: `lo5, hi3, lo2, hi6`). -/
def padSplit (w q : Nat) : Nat :=
  if q = 0 then padByte (8 * w + 5) % 32 else if q = 1 then padByte (8 * w + 5) / 32
  else if q = 2 then padByte (8 * w + 2) % 4 else padByte (8 * w + 2) / 4

def L : Layout :=
  [("act", 1), ("b", 139), ("ot", 1), ("ow", 48), ("or", 42),
   ("si", 4 * 18), ("so", 4 * 18),
   ("hi", 24), ("di", 18), ("xi", 6), ("ho", 24), ("do", 18), ("xo", 6),
   ("ci1", 1), ("ci2", 1), ("co1", 1), ("co2", 1),
   ("ri", 48), ("rsi", 24), ("ro", 48), ("rso", 24),
   ("wsi", 24), ("wso", 24), ("g", 3),
   ("fin", 1), ("tinv", 1), ("om", 40)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

/-- **A word from its 8 big-endian bytes** as the chip's 3 limbs, with the split parts `sp 0 … 3`
(`lo5, hi3` of byte 5, `lo2, hi6` of byte 2). -/
def wordW (byte : Nat → Expr) (sp : Nat → Expr) : W3 :=
  (byte 7 + K 256 * byte 6 + K 65536 * sp 0,
   sp 1 + K 8 * byte 4 + K 2048 * byte 3 + K 524288 * sp 2,
   sp 3 + K 64 * byte 1 + K 16384 * byte 0)

/-- Limb `l` of a triple. -/
def w3l (x : W3) (l : Nat) : Expr := if l = 0 then x.1 else if l = 1 then x.2.1 else x.2.2

/-- The input message byte at position `p` of the padded message. -/
def mI (p : Nat) : Expr := if p < NB then c "b" p else K (padByte p)

/-- The output message byte: tag `ot`, `ws` = `ow`, `u64 wsLen ‖ trie` (bytes 49–88) = `om` (B-T5: the
input's bytes, or zeros in the `done` mode), `u64 idx` (89–96) shared with the input, `rest` = `or`. -/
def mO (p : Nat) : Expr :=
  if p = 0 then c "ot" else if p < 49 then c "ow" (p - 1) else if p < 89 then c "om" (p - 49)
  else if p < 97 then c "b" p else if p < NB then c "or" (p - 97) else K (padByte p)

/-- Split parts of message word `w` (columns `s` for `w < 18`, constants after). -/
def spM (s : String) (w q : Nat) : Expr := if w < NWD then c s (4 * w + q) else K (padSplit w q)

/-- The 16 words of block `k` (0 or 1) of a padded message. -/
def blockW (m : Nat → Expr) (s : String) (k : Nat) : List W3 :=
  (List.range 16).map fun i => wordW (fun j => m (8 * (16 * k + i) + j)) (spM s (16 * k + i))

/-- A 42-B digest limb: bytes `3i, 3i+1, 3i+2` big-endian. -/
def limb3 (byte : Nat → Expr) (i : Nat) : Expr :=
  K 65536 * byte (3 * i) + K 256 * byte (3 * i + 1) + byte (3 * i + 2)

def limbs14 (byte : Nat → Expr) : List Expr := (List.range 14).map (limb3 byte)

/-- The split equations of a word whose byte `j` is `byte j`. -/
def splitEqs (byte : Nat → Expr) (sp : Nat → Expr) : List Expr :=
  [byte 5 - (sp 0 + K 32 * sp 1), byte 2 - (sp 2 + K 4 * sp 3)]

/-- Every split equation of the table (ungated). -/
def splits : List Expr :=
  ((List.range NWD).flatMap fun w => splitEqs (fun j => mI (8 * w + j)) (spM "si" w)) ++
  ((List.range NWD).flatMap fun w => splitEqs (fun j => mO (8 * w + j)) (spM "so" w)) ++
  ((List.range 6).flatMap fun k => splitEqs (fun j => c "ri" (8 * k + j)) (fun q => c "rsi" (4 * k + q))) ++
  ((List.range 6).flatMap fun k => splitEqs (fun j => c "ro" (8 * k + j)) (fun q => c "rso" (4 * k + q))) ++
  ((List.range 6).flatMap fun k => splitEqs (fun j => mI (1 + 8 * k + j)) (fun q => c "wsi" (4 * k + q))) ++
  ((List.range 6).flatMap fun k => splitEqs (fun j => mO (1 + 8 * k + j)) (fun q => c "wso" (4 * k + q)))

/-- The limb equations: each digest limb column is its bytes' limb; the public `R_in` is the opened
`ws` bytes' limbs (the output's `ws`: `wsOutEqs`, mode-dependent). -/
def limbEqs : List Expr :=
  ((List.range 18).map fun t => c "di" t -
    w3l (wordW (fun j => c "ri" (8 * (t / 3) + j)) (fun q => c "rsi" (4 * (t / 3) + q))) (t % 3)) ++
  ((List.range 18).map fun t => c "do" t -
    w3l (wordW (fun j => c "ro" (8 * (t / 3) + j)) (fun q => c "rso" (4 * (t / 3) + q))) (t % 3)) ++
  ((List.range 18).map fun t => Expr.pub (PUB_WSA + t) -
    w3l (wordW (fun j => mI (1 + 8 * (t / 3) + j)) (fun q => c "wsi" (4 * (t / 3) + q))) (t % 3))

/-- `wsLen`: bytes 49–56 are the public count (little-endian, `< 2^24`), and `2^D − wsLen` is three
bytes `g`. -/
def lenEqs (D : Nat) : List Expr :=
  ((List.range 5).map fun k => c "b" (52 + k)) ++
  [c "b" 49 + K 256 * c "b" 50 + K 65536 * c "b" 51 - .pub PUB_WSLEN,
   c "g" 0 + K 256 * c "g" 1 + K 65536 * c "g" 2 - (K (2 ^ D) - .pub PUB_WSLEN)]

/-- B-T4: the opened `trie` bytes (57–88) are the public `prev_state_root` (values 0–15, 16-bit
limbs big-endian, `pack2`): byte pair `(57 + 2i, 58 + 2i)` is limb `i`. A STATE leaf's trie is the
one its INTAKE revealed, and the IF's FINAL (`FinHalfB`) runs on the trie the commitment carries. -/
def trieEqs : List Expr :=
  (List.range 16).map fun i => c "b" (58 + 2 * i) + K 256 * c "b" (57 + 2 * i) - .pub i

/-- B-T5 (finding M14-1): the empty depth-24 working-set tree's root, byte `j` (`zeroDig 24`,
`= zd nodeH zero48 24`: the `ws` of a commitment without overlay). -/
def emptyB (j : Nat) : Nat := ((zeroDig WS_DEPTH).getD j 0).toNat

/-- **B-T5: the two close modes** (degree 2, ungated; all-zero padding rows satisfy them). `fin`
(boolean) is `1` exactly when the output tag `ot` is `3` (`done`): `fin · (ot − 3) = 0` and
`(ot − 3) · tinv = act − fin`. In the **step mode** (`fin = 0`) the output is `close c R_out`:
`ws` = the public `R_out` (values 35–52) and `om` = the input's `u64 wsLen ‖ trie`; in the **`done`
mode** (`fin = 1`, M14-1: at `done` the view has no overlay) the output is the no-overlay record:
`ws` = the empty tree's root (`emptyB`), `wsLen = 0`, trie `0^32` (`om = 0`); `idx` and the
input side are the same in both modes. -/
def modeEqs : List Expr :=
  [bool (c "fin"), c "fin" * (c "ot" - K 3), (c "ot" - K 3) * c "tinv" - (c "act" - c "fin")] ++
  ((List.range 18).map fun t => (c "act" - c "fin") * (Expr.pub (PUB_WSB + t) -
    w3l (wordW (fun j => mO (1 + 8 * (t / 3) + j)) (fun q => c "wso" (4 * (t / 3) + q))) (t % 3))) ++
  ((List.range 48).map fun j => c "fin" * (c "ow" j - K (emptyB j))) ++
  ((List.range 40).map fun j => c "om" j - (c "act" - c "fin") * c "b" (49 + j))

def constraints (D : Nat) : List Expr :=
  bool (c "act") :: ((splits ++ limbEqs ++ lenEqs D ++ trieEqs).map fun e => c "act" * e) ++ modeEqs

/-- The byte columns (each looked up once). -/
def byteCols : List Expr :=
  ((List.range NB).map fun p => c "b" p) ++ [c "ot"] ++ ((List.range 48).map fun j => c "ow" j) ++
  ((List.range 42).map fun j => c "or" j) ++ ((List.range 48).map fun j => c "ri" j) ++
  ((List.range 48).map fun j => c "ro" j) ++ ((List.range 3).map fun j => c "g" j) ++
  ((List.range 40).map fun j => c "om" j)

/-- The split column groups (name, words). -/
def grps : List (String × Nat) :=
  [("si", NWD), ("so", NWD), ("rsi", 6), ("rso", 6), ("wsi", 6), ("wso", 6)]

/-- The high split parts (`hi3`, `hi6`): one byte lookup each suffices (`lo + 2^k·hi` is then an
integer `< P`, so it is the byte and `hi < 2^(8−k)`). -/
def hiCols : List Expr :=
  grps.flatMap fun (s, n) => (List.range n).flatMap fun w => [c s (4 * w + 1), c s (4 * w + 3)]

/-- The low split parts with their widths (`lo5`, `lo2`): `x < 256` and `2^(8−k)·x < 256`. -/
def loCols : List (Expr × Nat) :=
  grps.flatMap fun (s, n) => (List.range n).flatMap fun w => [(c s (4 * w), 5), (c s (4 * w + 2), 2)]

def ranges : List Interaction :=
  let A := c "act"
  (byteCols.map fun x => rcv B_SRNG A [x]) ++ (hiCols.map fun x => rcv B_SRNG A [x]) ++
  (loCols.flatMap fun (x, k) => [rcv B_SRNG A [x], rcv B_SRNG A [K (2 ^ (8 - k)) * x]])

/-- The four compressions (two per side). -/
def comps : List Interaction :=
  let A := c "act"
  comp A (c "ci1") (ivW ++ blockW mI "si" 0 ++ wordsOf (fun t => c "hi" t) 8) ++
  comp A (c "ci2") (wordsOf (fun t => c "hi" t) 8 ++ blockW mI "si" 1 ++ digW (fun t => c "di" t) ++
    wordsOf (fun t => c "xi" t) 2) ++
  comp A (c "co1") (ivW ++ blockW mO "so" 0 ++ wordsOf (fun t => c "ho" t) 8) ++
  comp A (c "co2") (wordsOf (fun t => c "ho" t) 8 ++ blockW mO "so" 1 ++ digW (fun t => c "do" t) ++
    wordsOf (fun t => c "xo" t) 2)

/-- `STMQ` / `STMA`. -/
def stmqMsg : List Expr := limbs14 (fun j => c "ri" j) ++ [c "ot"] ++ limbs14 (fun j => c "or" j)
def stmaMsg : List Expr := limbs14 (fun j => c "ro" j) ++ [c "b" 0] ++ limbs14 (fun j => c "b" (97 + j))

def interactions : List Interaction :=
  [rcv B_STMQ (c "act") stmqMsg, snd B_STMA (c "act") stmaMsg] ++ comps ++ ranges

def table (D : Nat) : Table :=
  { width := L.width, constraints := constraints D, interactions, maxLog := 4 }

end Stc

/-! `SRNG`: the `STC` table's byte table (`RNG`'s constraints, its own bus). -/
namespace Srng
def L : Layout := [("v", 1), ("m", 20)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def interactions : List Interaction :=
  [sndBits B_SRNG ((List.range 20).map fun t => c "m" t) [c "v"]]
def table : Table := { width := L.width, constraints := Rng.constraints, interactions, maxLog := 8 }
end Srng

/-- **The STATE segment template with the `stRoot` opening** (B-T3): `m5tSeg`'s tables, then `STC`
and `SRNG`. -/
def stcTables (D : Nat) : List Table := [Stc.table D, Srng.table]

def m5tSegC (D : Nat) : Air :=
  { tables := (m5tSeg D).tables ++ stcTables D, numBuses := B_STMA + 1, numPub := NUM_PUB_SEG }

def tableNamesSegC : List String := tableNamesSeg ++ ["STC", "SRNG"]

/-- **B-T4: INTAKE + FINAL with the `stRoot` openings** (`m5tIF D`'s tables, then `STC` and `SRNG`).
The `STC` row's input is the commitment the INTAKE half closes at `start` (`c1`: tag 1, `ws = R_0`,
public values 17–34) and its output the `done` record `c9` (B-T5: tag 3, the `done` mode — empty
tree, `wsLen 0`, trie `0^32`; the FINAL half's working-set root `R_n`, values 35–52, is committed
by `c8`'s `stRoot`, which the finalize leaf opens with `ws = R_in = R_n`, not by `c9`).
The public values are `m5tIF`'s (the indices `STC` reads are the same: 0–15, 16, 17–34, 35–52). -/
def m5tIFC (D : Nat) : Air :=
  { tables := (m5tIF D).tables ++ stcTables D, numBuses := B_STMA + 1, numPub := NUM_PUB_IF }

def tableNamesIFC : List String := tableNamesIF ++ ["STC", "SRNG"]

def namesJsonC (D : Nat) (names : List String := tableNamesSegC) : String :=
  let q (s : String) := "\"" ++ s ++ "\""
  let ls := layoutsB D ++ [("WSX", Wsx.L), ("STC", Stc.L), ("SRNG", Srng.L)]
  "{" ++ ",".intercalate (ls.map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++
  s!",\"D\":{D},\"ws_depth\":{WS_DEPTH},\"zero_limbs\":[" ++
    ",".intercalate ((zeroLimbs D).map toString) ++ "],\"tables\":[" ++
    ",".intercalate (names.map q) ++ "]}"

end StateM5a
