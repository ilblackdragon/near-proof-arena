import StateM5a.Dsl

/-!
# StateM5a.Trie — the trie-side tables: `KEY`, `BR`, `SN`, `SNC`, `RNG`, `KCMP`

A *walk* is one spec trie operation along one key: `PTrie.findRef` (INTAKE, mode 0),
`PTrie.upsert` (FINAL, mode 1) or `PTrie.del` (FINAL, mode 2).  Each node the operation visits is
one row of `BR` (branch) or `SN` (leaf / extension).  A row holds the node's full content, sends
the node's serialization (`PTrie.hashOf`'s preimage, `RawTrieNodeWithSize`) to the SHA-256 table
and receives its digest; for an updating operation it also sends the rewritten node and receives
that digest.  Rows of one walk are linked by `DOWN` (parent → child: the child hash the parent
holds, which the child row must hash to) and `UP` (child → parent: the child's result).
Keys are nibble strings of the `KEY` table, read by `NIB` lookups.

Operation codes (one-hot per row):
* `BR`: `oFD` find-descend, `oFA` find-absent (empty slot), `oFV` find ending at the branch (its
  value), `oUD` upsert-descend, `oUN` upsert into an empty slot (new leaf, materialized by
  `SN.oLM`), `oDH`/`oDL`/`oDN` delete-descend whose child result is a hashed node / a leaf
  descriptor (materialized) / nothing, and the branch keeps (`squashBranch`'s last case), `oD1`
  delete-descend whose child vanished and one sibling leaf is left (`squashBranch` →
  `extendChild [i] sibling`), `oDA` delete at an empty slot (absent: `SAME`), `oDS` delete-descend
  whose child is unchanged (`SAME`), `oSL` the new branch of a split (`splitLeaf` / `splitExt`,
  two children: the old-side child and the walk's new leaf).
* `SN`: leaf `oLF` find-present, `oLA` find-absent (key differs), `oLR` upsert-replace, `oLX`
  upsert-split (`splitLeaf`), `oLD` delete, `oLZ` delete-absent, `oLS` sibling read (for `oD1`),
  `oLM` materialize a leaf descriptor; extension `oEF`/`oEU`/`oED` find/upsert/delete-descend
  (`oED`: the child result is a leaf descriptor, `extendChild k (leaf …)`), `oEA`/`oEZ`
  find/delete with the extension not a prefix of the key, `oES` delete-descend with the child
  unchanged, `oEB` delete-descend whose child result is a kept branch (`extendChild k (branch …)`),
  `oEX` upsert-split (`splitExt`), `oEP` the new extension over a split's common prefix
  (`wrapExt`), `oEM` a split's re-keyed extension `xs ↦ c`.

An absent row proves a mismatch at nibble `jm` of its key: the nibbles before `jm` are looked up
against the walk key, and at `jm` the walk key holds another nibble (`mN`, with an inverse), ends
(`mK`), or (leaf) continues past the leaf's key (`mL`).  Nibbles not looked up are range-checked
(`RNG`) or looked up against a second key `kid2` (a split's old key, padded to bytes).  A node key
longer than the head's capacity continues in `SNC` rows (64 nibbles each).

Cases outside this menu (`splitLeaf`/`splitExt` where a key ends at the split, squash to a value
leaf or onto an extension sibling, a mismatch beyond the head's 63 nibbles, the empty trie) have
no row and so are not provable: a completeness gap, never a soundness one.
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

/-- The carry into limb `k` (none into limb 0). -/
def cprev (cy : Nat → Expr) : Nat → Expr
  | 0 => 0
  | k + 1 => cy k

/-- `nw = m + plus − minus` on 4 limbs of 16 bits, carries `cy ∈ {−1,0,1}`, no final carry; gated. -/
def memChain (g : Expr) (nw m plus minus : List Expr) (cy : Nat → Expr) : List Expr :=
  ((List.range 4).map fun k =>
    g * (nw.getD k 0 + sm 65536 (cy k) - m.getD k 0 - plus.getD k 0 + minus.getD k 0 - cprev cy k)) ++
  [g * cy 3] ++ (List.range 4).map fun k => cy k * (cy k - 1) * (cy k + 1)

/-! ## BR: one row per branch node visited (or built by a split) -/

namespace Br
def L : Layout :=
  [("act", 1), ("rid", 1), ("w", 1), ("d", 1), ("kid", 1), ("mF", 1), ("mU", 1), ("mD", 1),
   ("oFD", 1), ("oFA", 1), ("oUD", 1), ("oUN", 1), ("oDH", 1), ("oDL", 1), ("oDN", 1), ("oD1", 1),
   ("oFV", 1), ("oDA", 1), ("oDS", 1), ("oSL", 1),
   ("hasv", 1), ("vl", 4), ("vh", 32), ("f", 16), ("ch", 512), ("mem", 8),
   ("sel", 16), ("sr", 16), ("nf", 16), ("gnew", 1), ("gdn", 1),
   ("ho", 32), ("hn", 32), ("nh", 32), ("nm", 4), ("om", 4), ("nmem", 8), ("cy", 4),
   ("inv1", 1), ("inv2", 1), ("dvlen", 1), ("dvh", 16),
   ("rk", 1), ("kid2", 1), ("st2", 1), ("lvlen", 1), ("lvh", 16), ("fpres", 1),
   ("xl", 1), ("xk", 1), ("lvlen2", 1), ("lvh2", 16), ("nh2", 32), ("nm2", 4),
   ("gsha", 1), ("oref", 1), ("vm", VBITS), ("isn", 16), ("nref", 1), ("vmn", VBITS), ("nhf", 1),
   ("nh2f", 1), ("oUV", 1), ("oDV", 1), ("oDZ", 1), ("nhv", 1), ("nvl", 4), ("nvh", 32),
   ("dm", 8), ("cyd", 4)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def ch (i b : Nat) : Expr := c "ch" (32 * i + b)
def bitsOf (s : String) : List Expr := (List.range VBITS).map fun t => c s t
def ops : List String :=
  ["oFD", "oFA", "oUD", "oUN", "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oSL", "oUV", "oDV",
   "oDZ"]

def nk : Expr := sumE ((List.range 16).map fun i => c "f" i)
def nkn : Expr := sumE ((List.range 16).map fun i => c "nf" i)
def rank (i : Nat) : Expr := sumE ((List.range i).map fun i' => c "f" i')
def nrank (i : Nat) : Expr := sumE ((List.range i).map fun i' => c "nf" i')
def nib : Expr := sumE ((List.range 16).map fun i => sm i (c "sel" i))
def sib : Expr := sumE ((List.range 16).map fun i => sm i (c "sr" i))
def mode : Expr := c "mU" + sm 2 (c "mD")
def gKeep : Expr := c "oDH" + c "oDL" + c "oDN"
/-- The row hashes an old node (every row but a split's new branch). -/
def gold : Expr := c "act" - c "oSL"
/-- Results `SAME` (an absent delete: the subtree is unchanged). -/
def gSame : Expr := c "oDA" + c "oDS" + c "oDZ"
/-- The walk key ends at this branch (its value is read, replaced or deleted). -/
def gEnd : Expr := c "oFV" + c "oUV" + c "oDV" + c "oDZ"
/-- Child hash byte `b` of the selected slot / of the remaining sibling. -/
def chSel (b : Nat) : Expr := sumE ((List.range 16).map fun i => c "sel" i * ch i b)
def chSib (b : Nat) : Expr := sumE ((List.range 16).map fun i => c "sr" i * ch i b)
def M : List Expr := memLimbs T "mem"
def NM : List Expr := memLimbs T "nmem"
/-- Ref flag of the selected slot / of the remaining sibling (`1`: a version id). -/
def isnSel : Expr := sumE ((List.range 16).map fun i => c "sel" i * c "isn" i)
def isnSib : Expr := sumE ((List.range 16).map fun i => c "sr" i * c "isn" i)
/-- The rewritten branch's slot `i`: bytes and ref flag (slot `sel` takes the child result, slot
`sr` a split's old-side child). -/
def newch (i b : Nat) : Expr := ch i b + c "sel" i * (c "nh" b - ch i b) + c "sr" i * (c "nh2" b - ch i b)
def nisn (i : Nat) : Expr :=
  c "isn" i + c "sel" i * (c "nhf" - c "isn" i) + c "sr" i * (c "nh2f" - c "isn" i)
/-- The new node is final: hashed here (`gnew` and not a version id). -/
def gfin : Expr := c "gnew" - c "nref"
/-- The new node's version id (= its SHA-256 message id, unique per row). -/
def nidN : Expr := K ID_BR + sm 2 (c "rid") + 1
/-- A branch record on `VER`, in 17 parts (a message holds ≤ 63 fields), each led by
`(tag, part, ref flag, ref limbs)`: part `i < 16` is slot `i` as `(f, f·isn, f·32 bytes)`; part 16
is the value (`hasv`, the length as two 16-bit limbs, the 32 hash bytes) and the memory usage
(`memLimbs`).  Limbs are used where the row reads the field only through those limbs. -/
def rec (rf : Expr) (ref : List Expr) (fl : Nat → Expr) (isn : Nat → Expr) (cb : Nat → Nat → Expr)
    (hv : Expr) (vl vh : Nat → Expr) (mem : List Expr) : List (List Expr) :=
  let hd (part : Nat) : List Expr := [K VT_BR, K part, rf] ++ ref
  ((List.range 16).map fun i =>
    hd i ++ [fl i, fl i * isn i] ++ (List.range 32).map fun b => fl i * cb i b) ++
  [hd 16 ++ [hv, limb16 vl 0, limb16 vl 1] ++ (List.range 32).map vh ++ mem]
def bmLo (f : Nat → Expr) : Expr := sumE ((List.range 8).map fun i => sm (2 ^ i) (f i))
def bmHi (f : Nat → Expr) : Expr := sumE ((List.range 8).map fun i => sm (2 ^ i) (f (i + 8)))
/-- The branch value length (4 little-endian bytes). -/
def vlen : Expr := c "vl" 0 + sm 256 (c "vl" 1) + sm 65536 (c "vl" 2) + sm 16777216 (c "vl" 3)

/-- Memory of the rewritten branch: `nmem = m' + nm + oSL·nm2 − om` on 4 limbs of 16 bits, where
`m' = mem` (an updated branch) or `50` (a split's new branch, `50 + both children`); carries
`cy ∈ {−1, 0, 1, 2}`, no final carry. -/
def memNew : List Expr :=
  let g := c "gnew"; let s := c "oSL"
  let mEff (k : Nat) : Expr := (1 - s) * M.getD k 0 + (if k = 0 then sm 50 s else 0)
  -- a value written (`oUV`) / removed (`oUV` over an old value, `oDV`): `valueMem = len + 50`
  let vmem (vl : Nat → Expr) (k : Nat) : Expr :=
    if k = 0 then limb16 vl 0 + 50 else if k = 1 then limb16 vl 1 else 0
  ((List.range 4).map fun k =>
    g * (NM.getD k 0 + sm 65536 (c "cy" k) - mEff k - c "nm" k - s * c "nm2" k + c "om" k -
      c "oUV" * vmem (fun t => c "nvl" t) k + (c "oUV" * c "hasv" + c "oDV") * vmem (fun t => c "vl" t) k -
      (if k = 0 then 0 else c "cy" (k - 1)))) ++
  [g * c "cy" 3] ++
  (List.range 4).map fun k => c "cy" k * (c "cy" k - 1) * (c "cy" k + 1) * (c "cy" k - 2)

def constraints : List Expr :=
  let A := c "act"
  let flags := ["act", "mF", "mU", "mD", "hasv", "gnew", "gdn", "xl", "gsha", "oref", "nref", "nhf",
    "nh2f"] ++ ops
  (flags.map fun s => bool (c s)) ++
  -- versions: the old node is hashed here (`gsha`) or read from `VER` by its ref (`oref`: a
  -- version id); the new node is hashed (final) or published under its version id (`nref`)
  [c "gsha" * (1 - gold), c "oref" * (1 - gold), c "gsha" * c "oref", c "nref" * (1 - c "gnew"),
   c "nref" * (c "hn" 0 - nidN)] ++
  ((List.range 31).map fun b => c "nref" * c "hn" (b + 1)) ++
  ((List.range VBITS).flatMap fun t => [(1 - c "gsha") * c "vm" t, (1 - c "gnew") * c "vmn" t]) ++
  ((List.range 4).map fun t => (1 - c "hasv") * c "vl" t) ++
  ((List.range 32).map fun t => (1 - c "hasv") * c "vh" t) ++
  ((List.range 16).flatMap fun i => [bool (c "f" i), bool (c "sel" i), bool (c "sr" i), bool (c "nf" i)]) ++
  [c "mF" + c "mU" + c "mD" + c "oSL" - A,
   c "oFD" + c "oFA" + c "oFV" - c "mF",
   c "oUD" + c "oUN" + c "oUV" - c "mU",
   c "oDH" + c "oDL" + c "oDN" + c "oD1" + c "oDA" + c "oDS" + c "oDV" + c "oDZ" - c "mD",
   (1 - A) * c "hasv",
   sumE ((List.range 16).map fun i => c "sel" i) - (A - gEnd),
   sumE ((List.range 16).map fun i => c "sr" i) - c "oD1" - c "oSL",
   c "gdn" - (c "oFD" + c "oUD" + c "oDH" + c "oDL" + c "oDN" + c "oD1" + c "oDS"),
   sumE ((List.range 16).map fun i => c "sel" i * c "f" i) - c "gdn",
   c "gnew" - (c "oUD" + c "oUN" + c "oDH" + c "oDL" + c "oDN" + c "oSL" + c "oUV" + c "oDV"),
   -- the key ends here: write the value (`oUV`), delete it keeping ≥ 2 children (`oDV`,
   -- `squashBranch`'s last case), or an absent delete (`oDZ`: no value)
   bool (c "nhv"), c "oUV" * (1 - c "nhv"),
   c "oUV" * (c "dvlen" - (c "nvl" 0 + sm 256 (c "nvl" 1) + sm 65536 (c "nvl" 2) + sm 16777216 (c "nvl" 3))),
   c "oDV" * (1 - c "hasv"), c "oDV" * c "nhv",
   c "oDV" * (c "inv1" * nkn - 1), c "oDV" * (c "inv2" * (nkn - 1) - 1),
   c "oDZ" * c "hasv",
   -- squash: keep needs ≥ 1 child and (a value or ≥ 2 children); `oD1` has 2 children, no value
   gKeep * (c "inv1" * nkn - 1),
   gKeep * (c "inv2" * (nkn - 1) - (1 - c "hasv")),
   c "oD1" * (nk - 2), c "oD1" * c "hasv",
   -- the child result kind
   c "oFD" * c "rk", c "oUD" * (c "rk" - K RK_H),
   c "oDH" * (c "rk" - K RK_HB) * (c "rk" - K RK_HE),
   c "oDL" * (c "rk" - K RK_LD), c "oDN" * (c "rk" - K RK_NONE), c "oD1" * (c "rk" - K RK_NONE),
   c "oDS" * (c "rk" - K RK_SAME),
   -- a new leaf in an empty slot (`oUN`) or the walk's leaf of a split (`oSL`): materialize
   -- `K[d+1..]` with the walk's value
   (c "oUN" + c "oSL") * (c "kid2" - c "kid"), (c "oUN" + c "oSL") * (c "st2" - c "d" - 1),
   (c "oUN" + c "oSL") * (c "lvlen" - c "dvlen"),
   -- a split's new branch: no value, no old children
   c "oSL" * c "hasv",
   .isFirst * c "rid", .isTransition * (nx "rid" - c "rid" - 1)] ++
  -- a find ending at this branch answers its value (zero fields when there is none)
  ((List.range 4).map fun t => c "oFV" * (1 - c "hasv") * c "vl" t) ++
  ((List.range 32).map fun t => c "oFV" * (1 - c "hasv") * c "vh" t) ++
  ((List.range 16).flatMap fun i =>
    [(1 - A) * c "f" i, c "oSL" * c "f" i, c "sr" i * (1 - c "f" i - c "oSL"), c "sr" i * c "sel" i,
     c "nf" i - c "gnew" * c "f" i - c "sel" i * c "oUN" + c "sel" i * c "oDN" -
       c "oSL" * (c "sel" i + c "sr" i),
     (c "oUN" + c "oSL") * (c "lvh" i - c "dvh" i),
     bool (c "isn" i), c "isn" i * (1 - c "f" i), c "gsha" * c "isn" i, gfin * nisn i]) ++
  ((List.range 4).flatMap fun k => [c "oDN" * c "nm" k, (c "oUN" + c "oSL") * c "om" k,
    (c "oUV" + c "oDV") * c "nm" k, (c "oUV" + c "oDV") * c "om" k]) ++
  -- the rewritten node's value: written (`oUV`), removed (`oDV`) or kept
  ((List.range 16).map fun i =>
    c "oUV" * (c "dvh" i - (sm 256 (c "nvh" (2 * i)) + c "nvh" (2 * i + 1)))) ++
  [(c "gnew" - c "oUV" - c "oDV") * (c "nhv" - c "hasv")] ++
  ((List.range 4).flatMap fun t =>
    [(c "gnew" - c "oUV" - c "oDV") * (c "nvl" t - c "vl" t), (1 - c "nhv") * c "nvl" t]) ++
  ((List.range 32).flatMap fun t =>
    [(c "gnew" - c "oUV" - c "oDV") * (c "nvh" t - c "vh" t), (1 - c "nhv") * c "nvh" t]) ++
  memNew ++
  -- M5a-5: a delete-descend keeping the branch (`oDH`/`oDL`) computes the spec's truncated
  -- `m − old + new` (`Kids.delAt` / `squashBranch`); the row checks `old ≤ m` (`dm = mem − om`,
  -- 8 bytes in `RNG`, no final borrow), so the exact chain `memNew` is the spec's value
  memChain (c "oDH" + c "oDL") (memLimbs T "dm") M [] ((List.range 4).map fun k => c "om" k)
    (fun k => c "cyd" k) ++
  -- M5a-5: a written branch value's length is `< 2^24` (as `SN`'s 3 length bytes), so its four
  -- `RNG` bytes are the walk's `dvlen` without wrap-around (`2^32 > P`)
  [c "oUV" * c "nvl" 3]

def idO : Expr := K ID_BR + sm 2 (c "rid")
def idN : Expr := K ID_BR + sm 2 (c "rid") + 1

/-- Serialization bytes of a branch (`PTrie.hashOf`): tag, optional value ref, bitmap, child hashes
in slot order, memory usage.  `fl` are the child flags, `cb i b` the child bytes, `mb b` the
memory bytes, `g` the multiplicity of the fixed parts. -/
def serBytes (id : Expr) (g gv : Expr) (hv : Expr) (vl vh : Nat → Expr) (fl : Nat → Expr) (rk : Nat → Expr)
    (cb : Nat → Nat → Expr) (mb : Nat → Expr) : List Interaction :=
  let base := 3 + sm 36 hv
  [snd B_SHA_BYTES g [id, 0, 1 + hv]] ++
  ((List.range 4).map fun t => snd B_SHA_BYTES gv [id, K (1 + t), vl t]) ++
  ((List.range 32).map fun t => snd B_SHA_BYTES gv [id, K (5 + t), vh t]) ++
  [snd B_SHA_BYTES g [id, 1 + sm 36 hv, bmLo fl], snd B_SHA_BYTES g [id, 2 + sm 36 hv, bmHi fl]] ++
  ((List.range 16).flatMap fun i => (List.range 32).map fun b =>
    snd B_SHA_BYTES (g * fl i) [id, base + sm 32 (rk i) + K b, cb i b]) ++
  ((List.range 8).map fun b =>
    snd B_SHA_BYTES g [id, base + sm 32 (sumE ((List.range 16).map fl)) + K b, mb b])

def serLen (hv : Expr) (fl : Nat → Expr) : Expr := 11 + sm 36 hv + sm 32 (sumE ((List.range 16).map fl))

def interactions : List Interaction :=
  let A := c "act"; let w := c "w"; let d := c "d"
  let gh := c "oUD" + c "oDH"
  let gmat := c "oDL" + c "oUN" + c "oSL"
  let xl := c "xl"; let s := c "oSL"
  let gsha := c "gsha"
  -- old node: hashed here (`gsha`, then published on `VER` under its digest for the other readers)
  -- or read from `VER` by its ref
  let vl := fun t => c "vl" t; let vh := fun t => c "vh" t
  let nvl := fun t => c "nvl" t; let nvh := fun t => c "nvh" t
  serBytes idO gsha (gsha * c "hasv") (c "hasv") vl vh (fun i => c "f" i) rank (fun i b => ch i b)
    (fun b => c "mem" b) ++
  [rcv B_SHA_DIGEST gsha ([idO, serLen (c "hasv") fun i => c "f" i] ++ (List.range 32).map fun b => c "ho" b)] ++
  ((rec (c "oref") (pack2 fun b => c "ho" b) (fun i => c "f" i) (fun i => c "isn" i) ch (c "hasv") vl vh M).map
    fun m => rcv B_VER (gold - gsha) m) ++
  ((rec 0 (pack2 fun b => c "ho" b) (fun i => c "f" i) (fun i => c "isn" i) ch (c "hasv") vl vh M).map
    fun m => sndBits B_VER (bitsOf "vm") m) ++
  -- new node (slot `sel` takes the child result, slot `sr` a split's old-side child): hashed when
  -- final, published on `VER` under its ref (digest or version id)
  serBytes idN gfin (gfin * c "nhv") (c "nhv") nvl nvh (fun i => c "nf" i) nrank newch
    (fun b => c "nmem" b) ++
  [rcv B_SHA_DIGEST gfin ([idN, serLen (c "nhv") fun i => c "nf" i] ++ (List.range 32).map fun b => c "hn" b)] ++
  ((rec (c "nref") (pack2 fun b => c "hn" b) (fun i => c "nf" i) nisn newch (c "nhv") nvl nvh NM).map
    fun m => sndBits B_VER (bitsOf "vmn") m) ++
  -- a written value's length bytes are bytes (it enters the memory chain as limbs)
  ((List.range 4).map fun t => rcv B_RNG (c "oUV") [c "nvl" t]) ++
  -- a published (unhashed) node's memory bytes are bytes (the SHA-256 table checks a hashed one's)
  ((List.range 8).map fun b => rcv B_RNG (c "nref") [c "nmem" b]) ++
  -- this node's walk step
  [rcv B_DOWN gold ([w, d, c "oref"] ++ pack2 (fun b => c "ho" b) ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_NIB (A - gEnd) [c "kid", d, nib],
   rcv B_KLEN gEnd [c "kid", d],
   snd B_DOWN (c "gdn") ([w, d + 1, isnSel] ++ pack2 chSel ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_UP (c "gdn") ([w, d + 1, c "rk", gh * c "nhf" + c "oDS" * isnSel] ++
     ((pack2 (fun b => c "nh" b)).zip (pack2 chSel)).map (fun (p, q) => gh * p + c "oDS" * q) ++
     ((List.range 4).map fun k => gh * c "nm" k) ++ ((List.range 4).map fun k => c "om" k) ++
     [c "oDL" * c "kid2", c "oDL" * c "st2", (c "oFD" + c "oDL") * c "lvlen"] ++
     ((List.range 16).map fun i => (c "oFD" + c "oDL") * c "lvh" i) ++ [c "oFD" * c "fpres"]),
   -- the one remaining sibling (`oD1`) is a revealed leaf; its key continues with nibble `sib`
   snd B_SIBQ (c "oD1") ([w, d + 1, isnSib] ++ pack2 chSib),
   rcv B_SIBA (c "oD1") ([w, d + 1, c "kid2", c "lvlen"] ++ (List.range 16).map fun i => c "lvh" i),
   rcv B_NIB (c "oD1") [c "kid2", d, sib],
   -- a split: the old-side child sits at slot `sib` = nibble `d` of the old key `xk`
   rcv B_NIB s [c "xk", d, sib],
   -- materialized child leaf (`oDL`: the child's descriptor; `oUN`, `oSL`: a new leaf)
   snd B_MATQ gmat ([w, d + 1, c "kid2", c "st2", c "lvlen"] ++ (List.range 16).map fun i => c "lvh" i),
   rcv B_MATR gmat ([w, d + 1, c "kid2", c "nhf"] ++ pack2 (fun b => c "nh" b) ++
     (List.range 4).map fun k => c "nm" k),
   -- a split's old-side child: a leaf to materialize (`xl`) or a given node
   snd B_MATQ (s * xl) ([w, d + 1, c "xk", d + 1, c "lvlen2"] ++ (List.range 16).map fun i => c "lvh2" i),
   rcv B_MATR (s * xl) ([w, d + 1, c "xk", c "nh2f"] ++ pack2 (fun b => c "nh2" b) ++
     (List.range 4).map fun k => c "nm2" k),
   rcv B_SPQ s ([w, d, c "kid", c "xk", xl] ++
     ((List.range 16).zip (pack2 fun b => c "nh2" b)).map
       (fun (i, p) => xl * c "lvh2" i + (1 - xl) * p) ++
     [(1 - xl) * c "nh2f", xl * c "lvlen2"] ++ ((List.range 4).map fun k => (1 - xl) * c "nm2" k) ++
     [c "dvlen"] ++ (List.range 16).map fun i => c "dvh" i),
   snd B_SPR s ([w, d, c "nref"] ++ pack2 (fun b => c "hn" b) ++ NM),
   -- result to the parent
   snd B_UP gold ([w, d, c "oUD" + c "oUN" + c "oUV" + sm 2 (gKeep + c "oDV") + sm 4 (c "oD1") +
       sm RK_SAME gSame,
       c "gnew" * c "nref" + gSame * c "oref"] ++
     ((pack2 (fun b => c "hn" b)).zip (pack2 fun b => c "ho" b)).map
       (fun (p, q) => c "gnew" * p + gSame * q) ++
     NM.map (c "gnew" * ·) ++ M.map ((c "mU" + c "mD") * ·) ++
     [c "oD1" * c "kid2", c "oD1" * d, (c "oFD" + c "oD1") * c "lvlen" + c "oFV" * vlen] ++
     ((List.range 16).zip (pack2 fun b => c "vh" b)).map
       (fun (i, p) => (c "oFD" + c "oD1") * c "lvh" i + c "oFV" * p) ++
     [c "oFD" * c "fpres" + c "oFV" * c "hasv"])] ++
  -- M5a-5: the bytes of `mem − om` on `oDH`/`oDL` rows
  ((List.range 8).map fun b => rcv B_RNG (c "oDH" + c "oDL") [c "dm" b]) ++
  -- M5a-5: a version-published (unhashed) branch's value-hash bytes are bytes (a hashed one's are
  -- checked by the SHA-256 table)
  (List.range 32).map fun b => rcv B_RNG (c "nref") [c "nvh" b]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Br

/-! ## SN: one row per leaf / extension node visited, or built (head of the node's key) -/

namespace Sn
def L : Layout :=
  [("act", 1), ("rid", 1), ("w", 1), ("d", 1), ("kid", 1), ("kid2", 1), ("mF", 1), ("mU", 1), ("mD", 1),
   ("oLF", 1), ("oLR", 1), ("oLD", 1), ("oLS", 1), ("oLM", 1), ("oEF", 1), ("oEU", 1), ("oED", 1),
   ("oLA", 1), ("oEA", 1), ("oLZ", 1), ("oEZ", 1), ("oES", 1), ("oEB", 1), ("oLX", 1), ("oEX", 1),
   ("oEP", 1), ("oEM", 1),
   ("isL", 1), ("isE", 1), ("gold", 1), ("gnew", 1), ("gdn", 1), ("gA", 1), ("g2", 1), ("gfr", 1),
   ("klen", 1), ("odd", 1), ("hplen", 1), ("k", KMAX), ("a", KMAX), ("b", KMAX), ("ha", HPMAX),
   ("hp", HPMAX), ("cont", 1), ("rl", 1),
   ("jm", 1), ("kj", 1), ("ajm", 1), ("y", 1), ("iy", 1), ("mN", 1), ("mK", 1), ("mL", 1),
   ("j0", 1), ("ij0", 1),
   ("x", 36), ("mem", 8), ("ho", 32), ("hn", 32), ("nx", 36), ("nmem", 8), ("cy", 4),
   ("unm", 4), ("uom", 4), ("rkc", 1), ("alen", 1), ("avh", 16), ("fpres", 1),
   ("dvlen", 1), ("dvh", 16), ("sh", 16), ("sm", 4),
   ("z", 1), ("iz", 1), ("sxh", 16), ("sxm", 4), ("xh", 16), ("xm", 4), ("cmb", 8), ("cy2", 4),
   ("gsha", 1), ("oref", 1), ("vm", VBITS), ("xf", 1), ("nref", 1), ("vmn", VBITS), ("nxf", 1),
   ("shf", 1), ("sxhf", 1), ("xhf", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j
def bitsOf (s : String) : List Expr := (List.range VBITS).map fun t => c s t
/-- The new node is final: hashed here (`gnew` and not a version id). -/
def gfin : Expr := c "gnew" - c "nref"
def nidN : Expr := K ID_SN + sm 2 (c "rid") + 1
/-- A leaf / extension record on `VER`, in 3 parts led by `(tag, part, ref flag, ref limbs)`:
part 0 `(isL, klen, payload ref flag, 36 payload bytes, memLimbs)`, parts 1 and 2 the key nibbles
`0..31`, `32..63`.  Rows whose key continues (`cont`) never use `VER` (the record holds 64
nibbles). -/
def rec (rf : Expr) (ref : List Expr) (xfl : Expr) (x : Nat → Expr) (mem : List Expr) : List (List Expr) :=
  let hd (part : Nat) : List Expr := [K VT_SN, K part, rf] ++ ref
  [hd 0 ++ [c "isL", c "klen", xfl] ++ (List.range 36).map x ++ mem,
   hd 1 ++ (List.range 32).map (fun j => c "k" j),
   hd 2 ++ (List.range 32).map (fun j => c "k" (32 + j))]
def ops : List String :=
  ["oLF", "oLR", "oLD", "oLS", "oLM", "oEF", "oEU", "oED", "oLA", "oEA", "oLZ", "oEZ", "oES", "oEB",
   "oLX", "oEX", "oEP", "oEM"]
def a (j : Nat) : Expr := if j < KMAX then c "a" j else 0
def b (j : Nat) : Expr := if j < KMAX then c "b" j else 0
def k (j : Nat) : Expr := if j < KMAX then c "k" j else 0
/-- `e j = 1` iff `j` is the first nibble not looked up against the walk key (`jm`). -/
def e (j : Nat) : Expr := (if j = 0 then 1 else b (j - 1)) - b j
def mode : Expr := c "mU" + sm 2 (c "mD")
def M : List Expr := memLimbs T "mem"
def NM : List Expr := memLimbs T "nmem"
def CM : List Expr := memLimbs T "cmb"
def vlenOf (x : Nat → Expr) : Expr := x 0 + sm 256 (x 1) + sm 65536 (x 2)
/-- Results `SAME` (absent deletes). -/
def gS : Expr := c "oLZ" + c "oEZ" + c "oES"
/-- Splits. -/
def gX : Expr := c "oLX" + c "oEX"
/-- `extOwnMem` of this row's key: `50 + 2·|hp|`. -/
def own : Expr := 50 + sm 2 (c "hplen")

def constraints : List Expr :=
  let A := c "act"; let odd := c "odd"; let gfr := c "gfr"
  let flags := ["act", "mF", "mU", "mD", "isL", "isE", "gold", "gnew", "gdn", "odd", "cont", "mN",
    "mK", "mL", "j0", "z", "gsha", "oref", "xf", "nref", "nxf", "shf", "sxhf", "xhf"] ++ ops
  (flags.map fun s => bool (c s)) ++
  -- versions (as `BR`); a continued key is always hashed (old and new) and never on `VER`
  [c "gsha" * (1 - c "gold"), c "oref" * (1 - c "gold"), c "gsha" * c "oref", c "nref" * (1 - c "gnew"),
   c "nref" * (c "hn" 0 - nidN), c "gsha" * c "xf", c "isL" * c "xf", c "isL" * c "nxf", gfin * c "nxf",
   c "cont" * (c "gold" - c "gsha"), c "cont" * c "nref",
   c "xhf" - c "oEX" * (c "z" * c "xf" + (1 - c "z") * c "sxhf")] ++
  ((List.range 31).map fun b => c "nref" * c "hn" (b + 1)) ++
  ((List.range VBITS).flatMap fun t =>
    [(1 - c "gsha") * c "vm" t, (1 - c "gnew") * c "vmn" t, c "cont" * c "vm" t, c "cont" * c "vmn" t]) ++
  ((List.range 4).flatMap fun t => [(1 - c "isL") * c "x" (32 + t), (1 - c "isL") * c "nx" (32 + t)]) ++
  [c "oLF" + c "oEF" + c "oLA" + c "oEA" - c "mF",
   c "oLR" + c "oEU" + c "oLX" + c "oEX" - c "mU",
   c "oLD" + c "oED" + c "oLZ" + c "oEZ" + c "oES" + c "oEB" - c "mD",
   c "mF" + c "mU" + c "mD" + c "oLS" + c "oLM" + c "oEP" + c "oEM" - A,
   c "isL" - (c "oLF" + c "oLR" + c "oLD" + c "oLS" + c "oLM" + c "oLA" + c "oLZ" + c "oLX"),
   c "isE" - (c "oEF" + c "oEU" + c "oED" + c "oEA" + c "oEZ" + c "oES" + c "oEB" + c "oEX" +
     c "oEP" + c "oEM"),
   c "gold" - (A - c "oLM" - c "oEP" - c "oEM"),
   c "gnew" - (c "oLR" + c "oLM" + c "oEU" + c "oEB" + c "oEP" + c "oEM"),
   c "gdn" - (c "oEF" + c "oEU" + c "oED" + c "oES" + c "oEB"),
   c "gA" - (c "oLA" + c "oEA" + c "oLZ" + c "oEZ" + c "oLX" + c "oEX"),
   c "g2" - (c "oED" + c "oLX" + c "oEX"),
   gfr - (c "oEB" + c "oEP" + c "oEM"),
   -- key: prefix-active flags, length (head + continuation `rl`), parity
   (1 - A) * a 0, c "isE" * (1 - a 0),
   c "klen" - sumE ((List.range KMAX).map a) - c "rl",
   odd - sumE ((List.range (KMAX / 2)).map fun m => a (2 * m) - a (2 * m + 1)),
   c "ha" 0 - A,
   sm 2 (c "hplen") - sm 2 (sumE ((List.range HPMAX).map fun m => c "ha" m)) - c "rl",
   c "hp" 0 - (sm 32 (c "isL") + odd * (16 + k 0)),
   -- a continued head holds stream nibbles 2..63 exactly (`62 + odd` key nibbles)
   c "cont" * (1 - a 61), c "cont" * a 63, c "cont" * (a 62 - odd), (1 - c "cont") * c "rl",
   -- the first nibble not looked up against the walk key, and the mismatch there
   c "jm" - sumE ((List.range KMAX).map b),
   c "kj" - sumE ((List.range KMAX).map fun j => e j * k j),
   c "ajm" - sumE ((List.range KMAX).map fun j => e j * a j),
   c "gA" * b (KMAX - 1),
   c "mN" + c "mK" + c "mL" - c "gA",
   (c "mN" + c "mK") * (1 - c "ajm"), c "mL" * c "ajm", c "mL" * c "isE", c "mL" * c "cont",
   gX * (1 - c "mN"),
   c "mN" * ((c "y" - c "kj") * c "iy" - 1),
   gX * c "j0" * c "jm", gX * (1 - c "j0") * (c "jm" * c "ij0" - 1),
   -- result kinds of the child (extension rows)
   c "oEF" * c "rkc", c "oEU" * (c "rkc" - K RK_H), c "oED" * (c "rkc" - K RK_LD),
   c "oES" * (c "rkc" - K RK_SAME), c "oEB" * (c "rkc" - K RK_HB),
   -- leaf value length fits 3 bytes
   c "isL" * c "x" 3,
   -- new leaf value from `DOWN` (`oLR`) or `MATQ` (`oLM`)
   (c "oLR" + c "oLM") * (c "dvlen" - vlenOf fun t => c "nx" t),
   (c "oLR" + c "oLM") * c "nx" 3,
   -- new leaf memory usage `leafMem k |v| = 100 + 2·|hp| + |v|`
   (c "oLR" + c "oLM") * (limb16 (fun b => c "nmem" b) 0 + sm 65536 (limb16 (fun b => c "nmem" b) 1)
     - 100 - sm 2 (c "hplen") - vlenOf fun t => c "nx" t),
   -- an extension split: the old-side child is `c` itself (`z`: one nibble after the split) or a
   -- re-keyed extension `xs ↦ c`
   c "oEX" * c "z" * (c "klen" - c "jm" - 1),
   c "oEX" * (1 - c "z") * ((c "klen" - c "jm" - 1) * c "iz" - 1),
   .isFirst * c "rid", .isTransition * (nx "rid" - c "rid" - 1)] ++
  ((List.range 16).map fun i =>
    (c "oLR" + c "oLM") * (c "dvh" i - (sm 256 (c "nx" (4 + 2 * i)) + c "nx" (5 + 2 * i)))) ++
  ((List.range 16).map fun i =>
    c "xh" i - c "oEX" * (c "z" * (sm 256 (c "x" (2 * i)) + c "x" (2 * i + 1)) + (1 - c "z") * c "sxh" i)) ++
  ((List.range 4).map fun t => c "xm" t - c "oEX" * (c "z" * CM.getD t 0 + (1 - c "z") * c "sxm" t)) ++
  ((List.range 4).map fun t => (c "oLR" + c "oLM") * c "nmem" (4 + t)) ++
  ((List.range KMAX).flatMap fun j =>
    [bool (a j), a (j + 1) * (1 - a j), (1 - a j) * k j,
     bool (b j), b (j + 1) * (1 - b j), b j * (1 - a j), (1 - c "gA") * (b j - a j)]) ++
  ((List.range HPMAX).flatMap fun m =>
    [bool (c "ha" m)] ++
    (if m = 0 then [] else
      [c "ha" m - odd * a (2 * m) - (1 - odd) * a (2 * m - 1),
       c "hp" m - odd * (sm 16 (k (2 * m - 1)) + k (2 * m)) -
         (1 - odd) * (sm 16 (k (2 * m - 2)) + k (2 * m - 1))])) ++
  -- the new extension's memory: `m + unm − uom` (`oEU`) or `extOwnMem + unm` (a fresh node)
  memChain (c "oEU" + gfr) NM ((List.range 4).map fun t => (1 - gfr) * M.getD t 0)
    ((List.range 4).map fun t => c "unm" t + (if t = 0 then gfr * own else 0))
    ((List.range 4).map fun t => (1 - gfr) * c "uom" t) (fun t => c "cy" t) ++
  -- an extension split: `mem = cm + extOwnMem k` (`cm` = the child's usage `splitExt` uses)
  memChain (c "oEX") M CM [own, 0, 0, 0] [0, 0, 0, 0] (fun t => c "cy2" t)

def idO : Expr := K ID_SN + sm 2 (c "rid")
def idN : Expr := K ID_SN + sm 2 (c "rid") + 1

/-- Serialization of a leaf (`[0] ++ u32 |hp| ++ hp ++ u32 vlen ++ vh ++ u64 mem`) or an
extension (`[3] ++ u32 |hp| ++ hp ++ child ++ u64 mem`); `x` is the 36 (leaf) / 32 (ext) payload
bytes.  The head sends `hp` bytes `0..32`; continuation rows (`SNC`) send the rest. -/
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
  let gnu := c "oLR" + c "oEU" + c "oEB"
  let gsha := c "gsha"
  serBytes idO gsha (fun t => c "x" t) (fun b => c "mem" b) ++
  [rcv B_SHA_DIGEST gsha ([idO, serLen] ++ (List.range 32).map fun b => c "ho" b)] ++
  ((rec (c "oref") (pack2 fun b => c "ho" b) (c "xf") (fun t => c "x" t) M).map
    fun m => rcv B_VER (c "gold" - gsha) m) ++
  ((rec 0 (pack2 fun b => c "ho" b) (c "xf") (fun t => c "x" t) M).map
    fun m => sndBits B_VER (bitsOf "vm") m) ++
  serBytes idN gfin (fun t => c "nx" t) (fun b => c "nmem" b) ++
  [rcv B_SHA_DIGEST gfin ([idN, serLen] ++ (List.range 32).map fun b => c "hn" b)] ++
  ((rec (c "nref") (pack2 fun b => c "hn" b) (c "nxf") (fun t => c "nx" t) NM).map
    fun m => sndBits B_VER (bitsOf "vmn") m) ++
  ((List.range 8).map fun b => rcv B_RNG (c "nref") [c "nmem" b]) ++
  -- the key: `K[d .. d+klen)`: nibbles before `jm` against `kid`, all against `kid2` (`g2`), the
  -- others range-checked; a leaf's key ends there
  ((List.range KMAX).map fun j => rcv B_NIB (b j) [c "kid", d + K j, k j]) ++
  ((List.range KMAX).map fun j => rcv B_NIB (c "g2" * a j) [c "kid2", d + K j, k j]) ++
  ((List.range KMAX).flatMap fun j =>
    [rcv B_RNG ((a j - b j) * (1 - c "g2")) [k j],
     rcv B_RNG ((a j - b j) * (1 - c "g2")) [k j + 240]]) ++
  [rcv B_KLEN (c "isL" * (1 - c "gA")) [c "kid", d + c "klen"],
   rcv B_KLEN (c "oLX") [c "kid2", d + c "klen"],
   -- the mismatch at `jm`: another nibble of the walk key, or the walk key ends, or (leaf) the
   -- walk key continues past the leaf's key
   rcv B_NIB (c "mN" + c "mL") [c "kid", d + c "jm", c "y"],
   rcv B_KLEN (c "mK") [c "kid", d + c "jm"],
   -- the continuation of a long key
   snd B_KC (c "cont") [c "rid", 1, d + 62 + c "odd", c "kid", 1 - c "gA", c "kid2", c "g2",
     gsha, gfin],
   rcv B_KCR (c "cont") [c "rid", 1, c "rl"],
   rcv B_DOWN gwalk ([w, d, c "oref"] ++ pack2 (fun b => c "ho" b) ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_SIBQ (c "oLS") ([w, d, c "oref"] ++ pack2 fun b => c "ho" b),
   snd B_SIBA (c "oLS") ([w, d, c "kid", vlenOf fun t => c "x" t] ++ pack2 fun b => c "x" (4 + b)),
   rcv B_MATQ (c "oLM") ([w, d, c "kid", d, c "dvlen"] ++ (List.range 16).map fun i => c "dvh" i),
   snd B_MATR (c "oLM") ([w, d, c "kid", c "nref"] ++ pack2 (fun b => c "hn" b) ++ NM),
   -- extension: descend
   snd B_DOWN (c "gdn") ([w, d + c "klen", c "xf"] ++ pack2 (fun b => c "x" b) ++ [c "kid", mode, c "dvlen"] ++
     (List.range 16).map fun i => c "dvh" i),
   rcv B_UP (c "gdn") ([w, d + c "klen", c "rkc", (c "oEU" + c "oEB") * c "nxf" + c "oES" * c "xf"] ++
     ((pack2 (fun b => c "nx" b)).zip (pack2 fun b => c "x" b)).map
       (fun (p, q) => (c "oEU" + c "oEB") * p + c "oES" * q) ++
     ((List.range 4).map fun t => (c "oEU" + c "oEB") * c "unm" t) ++
     ((List.range 4).map fun t => c "uom" t) ++
     [c "oED" * c "kid2", c "oED" * (d + c "klen"), (c "oEF" + c "oED") * c "alen"] ++
     ((List.range 16).map fun i => (c "oEF" + c "oED") * c "avh" i) ++ [c "oEF" * c "fpres"]),
   -- splits: ask for the new branch at `d + jm`, an extension over `K[d..d+jm)` above it, and
   -- (extension split) the re-keyed old extension
   snd B_SPQ gX ([w, d + c "jm", c "kid", c "kid2", c "oLX"] ++
     ((pack2 fun b => c "x" (4 + b)).zip ((List.range 16).map fun i => c "xh" i)).map
       (fun (p, q) => c "oLX" * p + q) ++
     [c "xhf", c "oLX" * vlenOf (fun t => c "x" t)] ++ ((List.range 4).map fun t => c "xm" t) ++
     [c "dvlen"] ++ (List.range 16).map fun i => c "dvh" i),
   snd B_EPQ (gX * (1 - c "j0")) [w, d, d + c "jm", c "kid"],
   rcv B_SPR gX ([w, d, c "shf"] ++ ((List.range 16).map fun i => c "sh" i) ++ (List.range 4).map fun t => c "sm" t),
   snd B_SXQ (c "oEX" * (1 - c "z")) ([w, d + c "jm" + 1, c "kid2", d + c "klen", c "xf"] ++
     pack2 (fun b => c "x" b) ++ CM),
   rcv B_SXR (c "oEX" * (1 - c "z")) ([w, d + c "jm" + 1, c "kid2", c "sxhf"] ++
     ((List.range 16).map fun i => c "sxh" i) ++ (List.range 4).map fun t => c "sxm" t),
   -- a new extension above a split branch (`oEP`), a re-keyed extension (`oEM`)
   rcv B_EPQ (c "oEP") [w, d, d + c "klen", c "kid"],
   rcv B_SPR (c "oEP") ([w, d + c "klen", c "nxf"] ++ pack2 (fun b => c "nx" b) ++
     (List.range 4).map fun t => c "unm" t),
   snd B_SPR (c "oEP") ([w, d, c "nref"] ++ pack2 (fun b => c "hn" b) ++ NM),
   rcv B_SXQ (c "oEM") ([w, d, c "kid", d + c "klen", c "nxf"] ++ pack2 (fun b => c "nx" b) ++
     (List.range 4).map fun t => c "unm" t),
   snd B_SXR (c "oEM") ([w, d, c "kid", c "nref"] ++ pack2 (fun b => c "hn" b) ++ NM)] ++
  ((List.range 8).map fun t => rcv B_RNG (c "oEX") [c "cmb" t]) ++
  -- result to the parent
  [snd B_UP gwalk ([w, d, c "oLR" + c "oEU" + sm RK_H gX + sm RK_LD (c "oED") + sm RK_NONE (c "oLD") +
       sm RK_HE (c "oEB") + sm RK_SAME gS, gnu * c "nref" + gS * c "oref" + gX * c "shf"] ++
     (((pack2 (fun b => c "hn" b)).zip (pack2 fun b => c "ho" b)).zip ((List.range 16).map fun i => c "sh" i)).map
       (fun ((p, q), s) => gnu * p + gS * q + gX * s) ++
     ((NM.zip ((List.range 4).map fun t => c "sm" t)).map fun (p, s) => gnu * p + gX * s) ++
     M.map ((c "mU" + c "mD") * ·) ++
     [c "oED" * c "kid2", c "oED" * d,
      c "oLF" * vlenOf (fun t => c "x" t) + (c "oEF" + c "oED") * c "alen"] ++
     ((pack2 fun b => c "x" (4 + b)).zip ((List.range 16).map fun i => c "avh" i)).map
       (fun (p, q) => c "oLF" * p + (c "oEF" + c "oED") * q) ++
     [c "oLF" + c "oEF" * c "fpres"])] ++
  -- M5a-5: a version-published (unhashed) leaf's payload (value length and hash) is bytes (a
  -- hashed one's are checked by the SHA-256 table; an extension's payload is its child's ref)
  (List.range 36).map fun t => rcv B_RNG (c "nref" * c "isL") [c "nx" t]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Sn

/-! ## SNC: continuation rows of a node key longer than the head's `62 + odd` nibbles

Chunk `c ≥ 1` of row `rid`'s key holds the hex-prefix stream nibbles `64c .. 64c+63`, i.e. key
nibbles from `p` on, and sends `hp` bytes `32c .. 32c+31` (at serialization offset `5 + 32c + m`)
for the old (`gO`) and new (`gN`) node message.  Its nibbles are looked up against `kA` (`fA`) and
`kB` (`gB`), or range-checked; every chunk holds an even number of nibbles. -/

namespace Snc
def L : Layout :=
  [("act", 1), ("rid", 1), ("c", 1), ("p", 1), ("kA", 1), ("fA", 1), ("kB", 1), ("gB", 1),
   ("gO", 1), ("gN", 1), ("more", 1), ("rl", 1), ("n", 1), ("a", 64), ("k", 64), ("ha", 32),
   ("hp", 32)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def a (j : Nat) : Expr := if j < 64 then c "a" j else 0

def constraints : List Expr :=
  (["act", "more"].map fun s => bool (c s)) ++
  [a 0 - c "act", c "n" - sumE ((List.range 64).map a), c "more" * (1 - a 63),
   (1 - c "more") * c "rl"] ++
  ((List.range 64).flatMap fun j => [bool (a j), a (j + 1) * (1 - a j), (1 - a j) * c "k" j]) ++
  ((List.range 32).flatMap fun m =>
    [a (2 * m + 1) - a (2 * m), c "ha" m - a (2 * m),
     c "hp" m - sm 16 (c "k" (2 * m)) - c "k" (2 * m + 1)])

def interactions : List Interaction :=
  let A := c "act"
  let msg (cc : Expr) : List Expr :=
    [c "rid", cc, c "p", c "kA", c "fA", c "kB", c "gB", c "gO", c "gN"]
  [rcv B_KC A (msg (c "c"))] ++
  ((List.range 64).flatMap fun j =>
    [rcv B_NIB (c "fA" * a j) [c "kA", c "p" + K j, c "k" j],
     rcv B_NIB (c "gB" * a j) [c "kB", c "p" + K j, c "k" j],
     rcv B_RNG (a j * (1 - c "fA") * (1 - c "gB")) [c "k" j],
     rcv B_RNG (a j * (1 - c "fA") * (1 - c "gB")) [c "k" j + 240]]) ++
  ((List.range 32).flatMap fun m =>
    [snd B_SHA_BYTES (c "gO" * c "ha" m) [K ID_SN + sm 2 (c "rid"), 5 + sm 32 (c "c") + K m, c "hp" m],
     snd B_SHA_BYTES (c "gN" * c "ha" m) [K ID_SN + sm 2 (c "rid") + 1, 5 + sm 32 (c "c") + K m, c "hp" m]]) ++
  [snd B_KC (c "more") ([c "rid", c "c" + 1, c "p" + 64, c "kA", c "fA", c "kB", c "gB", c "gO", c "gN"]),
   rcv B_KCR (c "more") [c "rid", c "c" + 1, c "rl"],
   snd B_KCR A [c "rid", c "c", c "n" + c "rl"]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Snc

/-! ## RNG: the byte range `0 ≤ v < 256` (256 rows, `v` = row index) -/

namespace Rng
def L : Layout := [("v", 1), ("m", 20)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

def constraints : List Expr :=
  [.isFirst * c "v", .isTransition * (T.n "v" - c "v" - 1), .isLast * (c "v" - 255)]

def interactions : List Interaction :=
  [sndBits B_RNG ((List.range 20).map fun t => c "m" t) [c "v"]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 8 }
end Rng

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
