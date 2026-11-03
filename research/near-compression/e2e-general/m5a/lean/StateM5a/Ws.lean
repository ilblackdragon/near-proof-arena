import StateM5a.Dsl

/-!
# StateM5a.Ws — the SHA-384 working-set tree: `WSB` (leaves), `WSN` (inner nodes), `WSA` (writes)

The working set of a segment is the key-sorted list of every key the chunk touches, each entry
`(sha256 key, pre-value ref, current value ref, written)`; a value ref is `(present, len,
sha256 value)`.  Entries are leaves of a complete binary Merkle tree of depth `D` (indices `≥ n`
hold the zero digest).  Hashing is SHA-384 (FIPS 180-4) through the native SHA-512 compression
chip: every compression is 16 messages `(cid, pair m, limbs(w_{2m}), limbs(w_{2m+1}))` over the
32 words `h_in ‖ block ‖ h_out`, each word as limbs `[0,21) [21,42) [42,64)`.

* leaf digest: the first 6 words of `compress(compress(IV384, B1), B2)`, `B1 ‖ B2 = leafWords e`
  (`wsLeafWords`, 16-bit fields in the low two limbs, flags and lengths in the high limb);
* inner node: SHA-384 of the 96 bytes `left48 ‖ right48` (one block with its padding).

`WSB` hashes all `2^D` leaves twice: phase 0 is the INTAKE state (`cur = pre`, not written), each
real leaf's pre-value proved by a find walk from `prev_state_root`; phase 1 is the final state,
each written leaf applied by an upsert / delete walk, in index (= key) order, chaining the trie root
from `prev_state_root` to the post-state root.  `WSN` builds both trees; the phase-0 root starts the
`RCH` chain, every `WSA` row (one write access: old leaf → new leaf along one Merkle path) advances
it, and the phase-1 root must close it.
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

/-- The 32 leaf words: `kd` in words 0..7, the pre / current value hashes in words 8..15 / 16..23
(low two limbs), `[pp, pl, cp, cl, wr]` in the high limb of words 0..4. -/
def leafWords (kd : Nat → Expr) (pp pl : Expr) (pv : Nat → Expr) (cp cl : Expr) (cv : Nat → Expr)
    (wr : Expr) : List W3 :=
  let hi : Nat → Expr := fun t => [pp, pl, cp, cl, wr].getD t 0
  ((List.range 8).map fun t => (kd (2 * t), kd (2 * t + 1), hi t)) ++
  ((List.range 8).map fun t => (pv (2 * t), pv (2 * t + 1), 0)) ++
  ((List.range 8).map fun t => (cv (2 * t), cv (2 * t + 1), 0)) ++
  (List.replicate 8 zeroW)

/-- The SHA-384 block of `left48 ‖ right48` (96 bytes: padding `0x80`, length 768 bits). -/
def nodeBlock (l r : List W3) : List W3 :=
  l ++ r ++ [constW (2 ^ 63), zeroW, zeroW, constW 768]

def ivW : List W3 := IV384.map constW

/-! ## WSB: leaves, both phases (`2^(D+1)` rows: phase 0 indices `0..2^D`, then phase 1) -/

namespace Wsb
def L : Layout :=
  [("ph", 1), ("i", 1), ("e", 1), ("real", 1), ("kid", 1), ("kd", 16), ("pp", 1), ("pl", 1),
   ("pv", 16), ("cp", 1), ("cl", 1), ("cv", 16), ("wr", 1), ("mid", 24), ("dg", 18), ("dx", 6),
   ("cid1", 1), ("cid2", 1), ("so", 1), ("j", 1), ("rin", 16), ("rout", 16), ("rk", 1),
   ("rnm", 4), ("rom", 4)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def vec (s : String) (n : Nat) : List Expr := (List.range n).map fun t => c s t

def leaf : List W3 :=
  leafWords (fun t => c "kd" t) (c "pp") (c "pl") (fun t => c "pv" t) (c "cp") (c "cl")
    (fun t => c "cv" t) (c "wr")

def constraints (D : Nat) : List Expr :=
  let ph := c "ph"; let e := c "e"; let real := c "real"
  (["ph", "e", "real", "pp", "cp", "wr", "so"].map fun s => bool (c s)) ++
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
   ph * c "wr" * (c "rk" - K RK_H) * (c "rk" - K RK_HB) * (c "rk" - K RK_HE)] ++
  ((List.range 16).flatMap fun t =>
    [(1 - ph) * (c "cv" t - c "pv" t), (1 - c "pp") * c "pv" t, (1 - c "cp") * c "cv" t,
     (1 - real) * c "kd" t]) ++
  ((List.range 18).map fun t => (1 - real) * c "dg" t)

def interactions : List Interaction :=
  let ph := c "ph"; let real := c "real"; let gw := ph * c "wr"; let g0 := (1 - ph) * real
  [rcv B_KDIG real (c "kid" :: vec "kd" 16),
   rcv B_ORD (c "so") [c "kid", nx "kid"]] ++
  comp real (c "cid1") (ivW ++ leaf.take 16 ++ wordsOf (fun t => c "mid" t) 8) ++
  comp real (c "cid2") (wordsOf (fun t => c "mid" t) 8 ++ leaf.drop 16 ++ digW (fun t => c "dg" t) ++
    wordsOf (fun t => c "dx" t) 2) ++
  [snd B_TREE 1 ([ph, 0, c "i"] ++ vec "dg" 18),
   -- INTAKE: the pre-value is the trie's answer at `prev_state_root` (public values 0..15)
   snd B_DOWN g0 ([c "i", 0] ++ ((List.range 16).map fun t => Expr.pub t) ++ [c "kid", 0, 0] ++
     List.replicate 16 0),
   rcv B_UP g0 ([c "i", 0, 0] ++ List.replicate 16 0 ++ List.replicate 4 0 ++ List.replicate 4 0 ++
     [0, 0, c "pl"] ++ vec "pv" 16 ++ [c "pp"]),
   -- FINAL: apply the written leaf's final value (upsert if present, else delete)
   snd B_DOWN gw ([K W_FINAL + c "i", 0] ++ vec "rin" 16 ++ [c "kid", 2 - c "cp", c "cl"] ++ vec "cv" 16),
   rcv B_UP gw ([K W_FINAL + c "i", 0, c "rk"] ++ vec "rout" 16 ++ vec "rnm" 4 ++ vec "rom" 4 ++
     [0, 0, 0] ++ List.replicate 16 0 ++ [0]),
   rcv B_TCH gw (c "j" :: vec "rin" 16),
   snd B_TCH gw ((c "j" + 1) :: vec "rout" 16)]

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

/-! ## WSA: one write access (old leaf → new leaf along a depth-`D` Merkle path) -/

namespace Wsa
def L (D : Nat) : Layout :=
  [("act", 1), ("jj", 1), ("kd", 16), ("pp", 1), ("pl", 1), ("pv", 16), ("cp", 1), ("cl", 1),
   ("cv", 16), ("wr", 1), ("ncp", 1), ("ncl", 1), ("ncv", 16),
   ("midO", 24), ("dgO", 18), ("dxO", 6), ("midN", 24), ("dgN", 18), ("dxN", 6), ("cidL", 4),
   ("side", D), ("sib", 18 * D), ("pO", 18 * D), ("xO", 6 * D), ("pN", 18 * D), ("xN", 6 * D),
   ("cO", D), ("cN", D)]
def T (D : Nat) : Cols := ⟨L D⟩

def constraints (D : Nat) : List Expr :=
  let c : String → (j : optParam Nat 0) → Expr := fun s j => (T D).c s j
  ([c "act", c "pp", c "cp", c "wr", c "ncp"].map bool) ++
  ((List.range D).map fun l => bool (c "side" l)) ++
  [(1 - c "ncp") * c "ncl"] ++ (List.range 16).map fun t => (1 - c "ncp") * c "ncv" t

def interactions (D : Nat) : List Interaction :=
  let c : String → (j : optParam Nat 0) → Expr := fun s j => (T D).c s j
  let A := c "act"
  let vec (s : String) (o n : Nat) : List Expr := (List.range n).map fun t => c s (o + t)
  let oldLeaf := leafWords (fun t => c "kd" t) (c "pp") (c "pl") (fun t => c "pv" t) (c "cp") (c "cl")
    (fun t => c "cv" t) (c "wr")
  let newLeaf := leafWords (fun t => c "kd" t) (c "pp") (c "pl") (fun t => c "pv" t) (c "ncp") (c "ncl")
    (fun t => c "ncv" t) 1
  let lw (s : String) (o : Nat) : List W3 := wordsOf (fun t => c s (o + t)) 6
  let leafComps (cid0 cid1 : Expr) (words : List W3) (mid dg dx : String) :=
    comp A cid0 (ivW ++ words.take 16 ++ wordsOf (fun t => c mid t) 8) ++
    comp A cid1 (wordsOf (fun t => c mid t) 8 ++ words.drop 16 ++ lw dg 0 ++ wordsOf (fun t => c dx t) 2)
  let level (l : Nat) (cur : List W3) (pS xS cS : String) : List Interaction :=
    let s := c "side" l
    let sibw := lw "sib" (18 * l)
    let left := (cur.zip sibw).map fun ((a0, a1, a2), (b0, b1, b2)) =>
      (a0 + s * (b0 - a0), a1 + s * (b1 - a1), a2 + s * (b2 - a2))
    let right := (cur.zip sibw).map fun ((a0, a1, a2), (b0, b1, b2)) =>
      (b0 + s * (a0 - b0), b1 + s * (a1 - b1), b2 + s * (a2 - b2))
    comp A (c cS l) (ivW ++ nodeBlock left right ++ lw pS (18 * l) ++ wordsOf (fun t => c xS (6 * l + t)) 2)
  let curO (l : Nat) : List W3 := if l = 0 then lw "dgO" 0 else lw "pO" (18 * (l - 1))
  let curN (l : Nat) : List W3 := if l = 0 then lw "dgN" 0 else lw "pN" (18 * (l - 1))
  [rcv B_WRITE A (vec "kd" 0 16 ++ [c "ncp", c "ncl"] ++ vec "ncv" 0 16),
   rcv B_RCH A (c "jj" :: vec "pO" (18 * (D - 1)) 18),
   snd B_RCH A ((c "jj" + 1) :: vec "pN" (18 * (D - 1)) 18)] ++
  leafComps (c "cidL" 0) (c "cidL" 1) oldLeaf "midO" "dgO" "dxO" ++
  leafComps (c "cidL" 2) (c "cidL" 3) newLeaf "midN" "dgN" "dxN" ++
  ((List.range D).flatMap fun l => level l (curO l) "pO" "xO" "cO" ++ level l (curN l) "pN" "xN" "cN")

def table (D : Nat) : Table :=
  { width := (L D).width, constraints := constraints D, interactions := interactions D, maxLog := 20 }
end Wsa

end StateM5a
