import StateM5a.Dsl

/-!
# StateM5a.Trie — the trie-side tables: `KEY`, `BR`, `SN`, `KCMP`

A *walk* is one spec trie operation along one key: `PTrie.findRef` (INTAKE, mode 0),
`PTrie.upsert` (FINAL, mode 1) or `PTrie.del` (FINAL, mode 2).  Each node the operation visits is
one row of `BR` (branch) or `SN` (leaf / extension).  A row holds the node's full content, sends
the node's serialization (`PTrie.hashOf`'s preimage, `RawTrieNodeWithSize`) to the SHA-256 table
and receives its digest; for an updating operation it also sends the rewritten node and receives
that digest.  Rows of one walk are linked by `DOWN` (parent → child: the child hash the parent
holds, which the child row must hash to) and `UP` (child → parent: the child's result).
Keys are nibble strings of the `KEY` table, read by `NIB` lookups.

Operation codes (one-hot per row):
* `BR`: `oFD` find-descend, `oFA` find-absent (empty slot), `oUD` upsert-descend, `oUN` upsert into
  an empty slot (new leaf, materialized by `SN.oLM`), `oDH`/`oDL`/`oDN` delete-descend whose child
  result is a hashed node / a leaf descriptor (materialized) / nothing, and the branch keeps
  (`squashBranch`'s last case), `oD1` delete-descend whose child vanished and one sibling leaf is left
  (`squashBranch` → `extendChild [i] sibling`).
* `SN`: leaf `oLF` find-present, `oLR` upsert-replace, `oLD` delete, `oLS` sibling read (for `oD1`),
  `oLM` materialize a leaf descriptor; extension `oEF`/`oEU`/`oED` find/upsert/delete-descend (the
  delete child result must be a leaf descriptor: `extendChild k (leaf …)`).

Cases outside this menu (leaf/extension splits, deletes reaching an absent key, squash onto a
branch/extension sibling, keys longer than `KMAX` nibbles in one node) have no row and so are not
provable: a completeness gap, never a soundness one.
-/

namespace StateM5a

open ZkFormal.Air

/-- Maximum key nibbles held by one `SN` row. -/
def KMAX : Nat := 64
/-- `hexPrefix` bytes of a `KMAX`-nibble key: `1 + KMAX/2`. -/
def HPMAX : Nat := 33

/-! ## KEY: one row per key byte -/

namespace Key
def L : Layout :=
  [("kid", 1), ("j", 1), ("hi", 1), ("lo", 1), ("hib", 4), ("lob", 4), ("act", 1), ("first", 1),
   ("last", 1), ("mh", 4), ("ml", 4), ("mlen", 4), ("mdig", 4), ("dg", 32)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

def nx (s : String) (j : Nat := 0) : Expr := T.n s j

def bits (s : String) : List Expr := (List.range 4).map fun k => c s k

def constraints : List Expr :=
  let act := c "act"; let first := c "first"; let last := c "last"
  [bool act, bool first, bool last] ++
  ((List.range 4).flatMap fun k => [bool (c "hib" k), bool (c "lob" k)]) ++
  [c "hi" - sumE ((List.range 4).map fun k => sm (2 ^ k) (c "hib" k)),
   c "lo" - sumE ((List.range 4).map fun k => sm (2 ^ k) (c "lob" k)),
   -- first row starts key 0
   .isFirst * (first - 1), .isFirst * c "kid", .isFirst * c "j", .isFirst * (act - 1),
   -- active rows first, then padding
   .isTransition * nx "act" * (1 - act),
   .isTransition * nx "act" * (nx "first" - last),
   .isTransition * nx "act" * (nx "kid" - c "kid" - last),
   .isTransition * nx "act" * (nx "j" - c "j" - 1 + last * (c "j" + 1)),
   .isTransition * act * (1 - nx "act") * (1 - last),
   .isLast * act * (1 - last),
   (1 - act) * first, (1 - act) * last] ++
  -- multiplicity bits only on active rows; length / digest only on last rows
  ((List.range 4).flatMap fun k =>
    [(1 - act) * c "mh" k, (1 - act) * c "ml" k, (1 - last) * c "mlen" k, (1 - last) * c "mdig" k])

def interactions : List Interaction :=
  let kid := c "kid"; let j := c "j"
  [snd B_SHA_BYTES (c "act") [K ID_KEY + kid, j, sm 16 (c "hi") + c "lo"],
   rcv B_SHA_DIGEST (c "last") ([K ID_KEY + kid, j + 1] ++ (List.range 32).map fun b => c "dg" b),
   sndBits B_NIB (bits "mh") [kid, sm 2 j, c "hi"],
   sndBits B_NIB (bits "ml") [kid, sm 2 j + 1, c "lo"],
   sndBits B_KLEN (bits "mlen") [kid, sm 2 (j + 1)],
   sndBits B_KDIG (bits "mdig") (kid :: pack2 fun b => c "dg" b)]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Key

/-! ## Shared node-row helpers -/

/-- 8 little-endian bytes as 4 limbs of 16 bits. -/
def memLimbs (T : Cols) (s : String) : List Expr := (List.range 4).map fun k => limb16 (fun b => T.c s b) k

/-- `nw = m + plus − minus` on 4 limbs of 16 bits, carries `cy ∈ {−1,0,1}`, no final carry; gated. -/
def memChain (g : Expr) (nw m plus minus : List Expr) (cy : Nat → Expr) : List Expr :=
  ((List.range 4).map fun k =>
    g * (nw.getD k 0 + sm 65536 (cy k) - m.getD k 0 - plus.getD k 0 + minus.getD k 0 -
      (if k = 0 then 0 else cy (k - 1)))) ++
  [g * cy 3] ++ (List.range 4).map fun k => cy k * (cy k - 1) * (cy k + 1)

/-! ## BR: one row per branch node visited -/

namespace Br
def L : Layout :=
  [("act", 1), ("rid", 1), ("w", 1), ("d", 1), ("kid", 1), ("mF", 1), ("mU", 1), ("mD", 1),
   ("oFD", 1), ("oFA", 1), ("oUD", 1), ("oUN", 1), ("oDH", 1), ("oDL", 1), ("oDN", 1), ("oD1", 1),
   ("hasv", 1), ("vl", 4), ("vh", 32), ("f", 16), ("ch", 512), ("mem", 8),
   ("sel", 16), ("sr", 16), ("nf", 16), ("gnew", 1), ("gdn", 1),
   ("ho", 32), ("hn", 32), ("nh", 32), ("nm", 4), ("om", 4), ("nmem", 8), ("cy", 4),
   ("inv1", 1), ("inv2", 1), ("dvlen", 1), ("dvh", 16),
   ("rk", 1), ("kid2", 1), ("st2", 1), ("lvlen", 1), ("lvh", 16), ("fpres", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def ch (i b : Nat) : Expr := c "ch" (32 * i + b)
def ops : List String := ["oFD", "oFA", "oUD", "oUN", "oDH", "oDL", "oDN", "oD1"]

def nk : Expr := sumE ((List.range 16).map fun i => c "f" i)
def nkn : Expr := sumE ((List.range 16).map fun i => c "nf" i)
def rank (i : Nat) : Expr := sumE ((List.range i).map fun i' => c "f" i')
def nrank (i : Nat) : Expr := sumE ((List.range i).map fun i' => c "nf" i')
def nib : Expr := sumE ((List.range 16).map fun i => sm i (c "sel" i))
def sib : Expr := sumE ((List.range 16).map fun i => sm i (c "sr" i))
def mode : Expr := c "mU" + sm 2 (c "mD")
def gKeep : Expr := c "oDH" + c "oDL" + c "oDN"
/-- Child hash byte `b` of the selected slot / of the remaining sibling. -/
def chSel (b : Nat) : Expr := sumE ((List.range 16).map fun i => c "sel" i * ch i b)
def chSib (b : Nat) : Expr := sumE ((List.range 16).map fun i => c "sr" i * ch i b)
def M : List Expr := memLimbs T "mem"
def NM : List Expr := memLimbs T "nmem"
def bmLo (f : Nat → Expr) : Expr := sumE ((List.range 8).map fun i => sm (2 ^ i) (f i))
def bmHi (f : Nat → Expr) : Expr := sumE ((List.range 8).map fun i => sm (2 ^ i) (f (i + 8)))

def constraints : List Expr :=
  let A := c "act"
  let flags := ["act", "mF", "mU", "mD", "hasv", "gnew", "gdn"] ++ ops
  (flags.map fun s => bool (c s)) ++
  ((List.range 16).flatMap fun i => [bool (c "f" i), bool (c "sel" i), bool (c "sr" i), bool (c "nf" i)]) ++
  [c "mF" + c "mU" + c "mD" - A,
   c "oFD" + c "oFA" - c "mF",
   c "oUD" + c "oUN" - c "mU",
   c "oDH" + c "oDL" + c "oDN" + c "oD1" - c "mD",
   (1 - A) * c "hasv",
   sumE ((List.range 16).map fun i => c "sel" i) - A,
   sumE ((List.range 16).map fun i => c "sr" i) - c "oD1",
   c "gdn" - (c "oFD" + c "oUD" + c "oDH" + c "oDL" + c "oDN" + c "oD1"),
   sumE ((List.range 16).map fun i => c "sel" i * c "f" i) - c "gdn",
   c "gnew" - (c "oUD" + c "oUN" + c "oDH" + c "oDL" + c "oDN"),
   -- squash: keep needs ≥ 1 child and (a value or ≥ 2 children); `oD1` has 2 children, no value
   gKeep * (c "inv1" * nkn - 1),
   gKeep * (c "inv2" * (nkn - 1) - (1 - c "hasv")),
   c "oD1" * (nk - 2), c "oD1" * c "hasv",
   -- the child result kind
   c "oFD" * c "rk", c "oUD" * (c "rk" - K RK_H),
   c "oDH" * (c "rk" - K RK_HB) * (c "rk" - K RK_HE),
   c "oDL" * (c "rk" - K RK_LD), c "oDN" * (c "rk" - K RK_NONE), c "oD1" * (c "rk" - K RK_NONE),
   -- a new leaf in an empty slot: materialize `K[d+1..]` with the walk's value
   c "oUN" * (c "kid2" - c "kid"), c "oUN" * (c "st2" - c "d" - 1),
   c "oUN" * (c "lvlen" - c "dvlen"),
   .isFirst * c "rid", .isTransition * (nx "rid" - c "rid" - 1)] ++
  ((List.range 16).flatMap fun i =>
    [(1 - A) * c "f" i, c "sr" i * (1 - c "f" i), c "sr" i * c "sel" i,
     c "nf" i - c "gnew" * c "f" i - c "sel" i * c "oUN" + c "sel" i * c "oDN",
     c "oUN" * (c "lvh" i - c "dvh" i)]) ++
  ((List.range 4).flatMap fun k => [c "oDN" * c "nm" k, c "oUN" * c "om" k]) ++
  memChain (c "gnew") NM M ((List.range 4).map fun k => c "nm" k) ((List.range 4).map fun k => c "om" k)
    (fun k => c "cy" k)

def idO : Expr := K ID_BR + sm 2 (c "rid")
def idN : Expr := K ID_BR + sm 2 (c "rid") + 1

/-- Serialization bytes of a branch (`PTrie.hashOf`): tag, optional value ref, bitmap, child hashes
in slot order, memory usage.  `fl` are the child flags, `cb i b` the child bytes, `mb b` the
memory bytes, `g` the multiplicity of the fixed parts. -/
def serBytes (id : Expr) (g gv : Expr) (fl : Nat → Expr) (rk : Nat → Expr) (cb : Nat → Nat → Expr)
    (mb : Nat → Expr) : List Interaction :=
  let hv := c "hasv"
  let base := 3 + sm 36 hv
  [snd B_SHA_BYTES g [id, 0, 1 + hv]] ++
  ((List.range 4).map fun t => snd B_SHA_BYTES gv [id, K (1 + t), c "vl" t]) ++
  ((List.range 32).map fun t => snd B_SHA_BYTES gv [id, K (5 + t), c "vh" t]) ++
  [snd B_SHA_BYTES g [id, 1 + sm 36 hv, bmLo fl], snd B_SHA_BYTES g [id, 2 + sm 36 hv, bmHi fl]] ++
  ((List.range 16).flatMap fun i => (List.range 32).map fun b =>
    snd B_SHA_BYTES (fl i) [id, base + sm 32 (rk i) + K b, cb i b]) ++
  ((List.range 8).map fun b =>
    snd B_SHA_BYTES g [id, base + sm 32 (sumE ((List.range 16).map fl)) + K b, mb b])

def serLen (fl : Nat → Expr) : Expr := 11 + sm 36 (c "hasv") + sm 32 (sumE ((List.range 16).map fl))

def interactions : List Interaction :=
  let A := c "act"; let w := c "w"; let d := c "d"
  let gh := c "oUD" + c "oDH"
  let gmat := c "oDL" + c "oUN"
  -- old node
  serBytes idO A (c "hasv") (fun i => c "f" i) rank (fun i b => ch i b) (fun b => c "mem" b) ++
  [rcv B_SHA_DIGEST A ([idO, serLen fun i => c "f" i] ++ (List.range 32).map fun b => c "ho" b)] ++
  -- new node
  serBytes idN (c "gnew") (c "gnew" * c "hasv") (fun i => c "nf" i) nrank
    (fun i b => ch i b + c "sel" i * (c "nh" b - ch i b)) (fun b => c "nmem" b) ++
  [rcv B_SHA_DIGEST (c "gnew") ([idN, serLen fun i => c "nf" i] ++ (List.range 32).map fun b => c "hn" b),
   -- this node's walk step
   rcv B_DOWN A ([w, d] ++ pack2 (fun b => c "ho" b) ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_NIB A [c "kid", d, nib],
   snd B_DOWN (c "gdn") ([w, d + 1] ++ pack2 chSel ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_UP (c "gdn") ([w, d + 1, c "rk"] ++ (pack2 (fun b => c "nh" b)).map (gh * ·) ++
     ((List.range 4).map fun k => gh * c "nm" k) ++ ((List.range 4).map fun k => c "om" k) ++
     [c "oDL" * c "kid2", c "oDL" * c "st2", (c "oFD" + c "oDL") * c "lvlen"] ++
     ((List.range 16).map fun i => (c "oFD" + c "oDL") * c "lvh" i) ++ [c "oFD" * c "fpres"]),
   -- the one remaining sibling (`oD1`) is a revealed leaf; its key continues with nibble `sib`
   snd B_SIBQ (c "oD1") ([w, d + 1] ++ pack2 chSib),
   rcv B_SIBA (c "oD1") ([w, d + 1, c "kid2", c "lvlen"] ++ (List.range 16).map fun i => c "lvh" i),
   rcv B_NIB (c "oD1") [c "kid2", d, sib],
   -- materialized child leaf (`oDL`: the child's descriptor; `oUN`: a new leaf)
   snd B_MATQ gmat ([w, d + 1, c "kid2", c "st2", c "lvlen"] ++ (List.range 16).map fun i => c "lvh" i),
   rcv B_MATR gmat ([w, d + 1] ++ pack2 (fun b => c "nh" b) ++ (List.range 4).map fun k => c "nm" k),
   -- result to the parent
   snd B_UP A ([w, d, c "oUD" + c "oUN" + sm 2 gKeep + sm 4 (c "oD1")] ++
     (pack2 (fun b => c "hn" b)).map (c "gnew" * ·) ++ NM.map (c "gnew" * ·) ++
     M.map ((c "mU" + c "mD") * ·) ++
     [c "oD1" * c "kid2", c "oD1" * d, (c "oFD" + c "oD1") * c "lvlen"] ++
     ((List.range 16).map fun i => (c "oFD" + c "oD1") * c "lvh" i) ++ [c "oFD" * c "fpres"])]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Br

/-! ## SN: one row per leaf / extension node visited (or a leaf materialized) -/

namespace Sn
def L : Layout :=
  [("act", 1), ("rid", 1), ("w", 1), ("d", 1), ("kid", 1), ("mF", 1), ("mU", 1), ("mD", 1),
   ("oLF", 1), ("oLR", 1), ("oLD", 1), ("oLS", 1), ("oLM", 1), ("oEF", 1), ("oEU", 1), ("oED", 1),
   ("isL", 1), ("isE", 1), ("gold", 1), ("gnew", 1), ("gdn", 1),
   ("klen", 1), ("odd", 1), ("hplen", 1), ("k", KMAX), ("a", KMAX), ("ha", HPMAX), ("hp", HPMAX),
   ("x", 36), ("mem", 8), ("ho", 32), ("hn", 32), ("nx", 36), ("nmem", 8), ("cy", 4),
   ("unm", 4), ("uom", 4), ("kid2", 1), ("rkc", 1), ("alen", 1), ("avh", 16), ("fpres", 1),
   ("dvlen", 1), ("dvh", 16)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def ops : List String := ["oLF", "oLR", "oLD", "oLS", "oLM", "oEF", "oEU", "oED"]
def a (j : Nat) : Expr := if j < KMAX then c "a" j else 0
def k (j : Nat) : Expr := if j < KMAX then c "k" j else 0
def mode : Expr := c "mU" + sm 2 (c "mD")
def M : List Expr := memLimbs T "mem"
def NM : List Expr := memLimbs T "nmem"
def vlenOf (x : Nat → Expr) : Expr := x 0 + sm 256 (x 1) + sm 65536 (x 2)

def constraints : List Expr :=
  let A := c "act"; let odd := c "odd"
  let flags := ["act", "mF", "mU", "mD", "isL", "isE", "gold", "gnew", "gdn", "odd"] ++ ops
  (flags.map fun s => bool (c s)) ++
  [c "oLF" + c "oEF" - c "mF", c "oLR" + c "oEU" - c "mU", c "oLD" + c "oED" - c "mD",
   c "mF" + c "mU" + c "mD" + c "oLS" + c "oLM" - A,
   c "isL" - (c "oLF" + c "oLR" + c "oLD" + c "oLS" + c "oLM"),
   c "isE" - (c "oEF" + c "oEU" + c "oED"),
   c "gold" - (A - c "oLM"), c "gnew" - (c "oLR" + c "oLM" + c "oEU"),
   c "gdn" - (c "oEF" + c "oEU" + c "oED"),
   -- key: prefix-active flags, length, parity
   (1 - A) * a 0, c "isE" * (1 - a 0),
   c "klen" - sumE ((List.range KMAX).map a),
   odd - sumE ((List.range (KMAX / 2)).map fun m => a (2 * m) - a (2 * m + 1)),
   c "ha" 0 - A,
   c "hplen" - sumE ((List.range HPMAX).map fun m => c "ha" m),
   c "hp" 0 - (sm 32 (c "isL") + odd * (16 + k 0)),
   -- result kinds of the child (extension rows)
   c "oEF" * c "rkc", c "oEU" * (c "rkc" - K RK_H), c "oED" * (c "rkc" - K RK_LD),
   -- leaf value length fits 3 bytes
   c "isL" * c "x" 3,
   -- new leaf value from `DOWN` (`oLR`) or `MATQ` (`oLM`)
   (c "oLR" + c "oLM") * (c "dvlen" - vlenOf fun t => c "nx" t),
   (c "oLR" + c "oLM") * c "nx" 3,
   -- new leaf memory usage `leafMem k |v| = 100 + 2·|hp| + |v|`
   (c "oLR" + c "oLM") * (limb16 (fun b => c "nmem" b) 0 + sm 65536 (limb16 (fun b => c "nmem" b) 1)
     - 100 - sm 2 (c "hplen") - vlenOf fun t => c "nx" t),
   .isFirst * c "rid", .isTransition * (nx "rid" - c "rid" - 1)] ++
  ((List.range 16).map fun i =>
    (c "oLR" + c "oLM") * (c "dvh" i - (sm 256 (c "nx" (4 + 2 * i)) + c "nx" (5 + 2 * i)))) ++
  ((List.range 4).map fun t => (c "oLR" + c "oLM") * c "nmem" (4 + t)) ++
  ((List.range KMAX).flatMap fun j =>
    [bool (a j), a (j + 1) * (1 - a j), (1 - a j) * k j]) ++
  ((List.range HPMAX).flatMap fun m =>
    [bool (c "ha" m)] ++
    (if m = 0 then [] else
      [c "ha" m - odd * a (2 * m) - (1 - odd) * a (2 * m - 1),
       c "hp" m - odd * (sm 16 (k (2 * m - 1)) + k (2 * m)) -
         (1 - odd) * (sm 16 (k (2 * m - 2)) + k (2 * m - 1))])) ++
  memChain (c "oEU") NM M ((List.range 4).map fun t => c "unm" t) ((List.range 4).map fun t => c "uom" t)
    (fun t => c "cy" t)

def idO : Expr := K ID_SN + sm 2 (c "rid")
def idN : Expr := K ID_SN + sm 2 (c "rid") + 1

/-- Serialization of a leaf (`[0] ++ u32 |hp| ++ hp ++ u32 vlen ++ vh ++ u64 mem`) or an
extension (`[3] ++ u32 |hp| ++ hp ++ child ++ u64 mem`); `x` is the 36 (leaf) / 32 (ext) payload
bytes. -/
def serBytes (id g : Expr) (x : Nat → Expr) (mb : Nat → Expr) : List Interaction :=
  let hpl := c "hplen"
  [snd B_SHA_BYTES g [id, 0, sm 3 (c "isE")], snd B_SHA_BYTES g [id, 1, hpl],
   snd B_SHA_BYTES g [id, 2, 0], snd B_SHA_BYTES g [id, 3, 0], snd B_SHA_BYTES g [id, 4, 0]] ++
  ((List.range HPMAX).map fun m => snd B_SHA_BYTES (g * c "ha" m) [id, K (5 + m), c "hp" m]) ++
  ((List.range 36).map fun t =>
    snd B_SHA_BYTES (if t < 32 then g else g * c "isL") [id, 5 + hpl + K t, x t]) ++
  ((List.range 8).map fun b => snd B_SHA_BYTES g [id, 37 + hpl + sm 4 (c "isL") + K b, mb b])

def serLen : Expr := 45 + c "hplen" + sm 4 (c "isL")

def interactions : List Interaction :=
  let w := c "w"; let d := c "d"
  let gwalk := c "mF" + c "mU" + c "mD"
  serBytes idO (c "gold") (fun t => c "x" t) (fun b => c "mem" b) ++
  [rcv B_SHA_DIGEST (c "gold") ([idO, serLen] ++ (List.range 32).map fun b => c "ho" b)] ++
  serBytes idN (c "gnew") (fun t => c "nx" t) (fun b => c "nmem" b) ++
  [rcv B_SHA_DIGEST (c "gnew") ([idN, serLen] ++ (List.range 32).map fun b => c "hn" b)] ++
  -- the key: `K[d .. d+klen)` of `kid`, and for a leaf the key ends there
  ((List.range KMAX).map fun j => rcv B_NIB (a j) [c "kid", d + K j, k j]) ++
  [rcv B_KLEN (c "isL") [c "kid", d + c "klen"]] ++
  -- `oED`: the child's leaf descriptor key `kid2` continues this extension's nibbles
  ((List.range KMAX).map fun j => rcv B_NIB (c "oED" * a j) [c "kid2", d + K j, k j]) ++
  [rcv B_DOWN gwalk ([w, d] ++ pack2 (fun b => c "ho" b) ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_SIBQ (c "oLS") ([w, d] ++ pack2 fun b => c "ho" b),
   snd B_SIBA (c "oLS") ([w, d, c "kid", vlenOf fun t => c "x" t] ++ pack2 fun b => c "x" (4 + b)),
   rcv B_MATQ (c "oLM") ([w, d, c "kid", d, c "dvlen"] ++ (List.range 16).map fun i => c "dvh" i),
   snd B_MATR (c "oLM") ([w, d] ++ pack2 (fun b => c "hn" b) ++ NM),
   -- extension: descend
   snd B_DOWN (c "gdn") ([w, d + c "klen"] ++ pack2 (fun b => c "x" b) ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_UP (c "gdn") ([w, d + c "klen", c "rkc"] ++ (pack2 (fun b => c "nx" b)).map (c "oEU" * ·) ++
     ((List.range 4).map fun t => c "oEU" * c "unm" t) ++ ((List.range 4).map fun t => c "uom" t) ++
     [c "oED" * c "kid2", c "oED" * (d + c "klen"), (c "oEF" + c "oED") * c "alen"] ++
     ((List.range 16).map fun i => (c "oEF" + c "oED") * c "avh" i) ++ [c "oEF" * c "fpres"]),
   -- result to the parent
   snd B_UP gwalk ([w, d, c "oLR" + c "oEU" + sm RK_LD (c "oED") + sm RK_NONE (c "oLD")] ++
     (pack2 (fun b => c "hn" b)).map ((c "oLR" + c "oEU") * ·) ++ NM.map ((c "oLR" + c "oEU") * ·) ++
     M.map ((c "oLR" + c "oLD" + c "oEU" + c "oED") * ·) ++
     [c "oED" * c "kid2", c "oED" * d,
      c "oLF" * vlenOf (fun t => c "x" t) + (c "oEF" + c "oED") * c "alen"] ++
     ((pack2 fun b => c "x" (4 + b)).zip ((List.range 16).map fun i => c "avh" i)).map
       (fun (p, q) => c "oLF" * p + (c "oEF" + c "oED") * q) ++
     [c "oLF" + c "oEF" * c "fpres"])]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Sn

/-! ## KCMP: strict byte-lexicographic order of two keys -/

namespace Kcmp
def L : Layout :=
  [("act", 1), ("first", 1), ("fin", 1), ("pre", 1), ("ka", 1), ("kb", 1), ("j", 1), ("x", 1),
   ("xa", 1), ("xb", 1), ("db", 4)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j

def constraints : List Expr :=
  let A := c "act"; let fin := c "fin"
  ([A, c "first", fin, c "pre"].map bool) ++ ((List.range 4).map fun t => bool (c "db" t)) ++
  [.isFirst * (c "first" - A),
   .isTransition * nx "act" * (1 - A),
   .isTransition * nx "act" * (nx "first" - fin),
   .isTransition * nx "act" * (1 - fin) * (nx "ka" - c "ka"),
   .isTransition * nx "act" * (1 - fin) * (nx "kb" - c "kb"),
   .isTransition * nx "act" * (1 - fin) * (nx "j" - c "j" - 1),
   .isTransition * A * (1 - nx "act") * (1 - fin),
   .isLast * A * (1 - fin),
   c "first" * c "j", (1 - A) * fin, (1 - fin) * c "pre",
   fin * (1 - c "pre") * (c "xb" - c "xa" - 1 - sumE ((List.range 4).map fun t => sm (2 ^ t) (c "db" t)))]

def interactions : List Interaction :=
  let A := c "act"; let fin := c "fin"
  [rcv B_NIB (A * (1 - fin)) [c "ka", c "j", c "x"],
   rcv B_NIB (A * (1 - fin)) [c "kb", c "j", c "x"],
   rcv B_NIB (fin * (1 - c "pre")) [c "ka", c "j", c "xa"],
   rcv B_NIB fin [c "kb", c "j", c "xb"],
   rcv B_KLEN (fin * c "pre") [c "ka", c "j"],
   snd B_ORD fin [c "ka", c "kb"]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Kcmp

end StateM5a
