import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids

/-!
# ZkFormal.NearV3.Rcpt.Tables.Srcp — `srcpV3`: source receipt proofs

`verifyReceiptProof root e`: `rootFromPath (sha256 (sha256 (u64 to ‖ encodeReceipts rs))) path
= root`, with `rootFromPath acc ((h, d) :: rest) = rootFromPath (sha256 (if d = 0 then h ‖ acc
else acc ‖ h)) rest`.  `rcptV3` emits `RC(j) = u64 own ‖ u32 n_j ‖ Σ borsh(receipt)` (SHA id
`K_RC`, idx `j`) and announces its length on `RCL (j, len)`.

Per applied list `j` (consecutive from `0`), a block of rows:

* a **root row** (`rt`): receives `RCL (j, L)`, the public `SRC (j, dup, root)` (into `reg`) and
  `DIGEST (SRC(qe), le, reg)`: the last message of the block hashes to `root_j`.  A duplicate
  source key (`dup`, spec v0a §2.5: a later used slot with an earlier slot's chunk hash, which
  shares that slot's witness entry) must have an empty list: `L = 12`;
* the **leaf segment** (`lf`, 32 rows): message `SRC(q)` = the 32 bytes of `sha256(RC(j))`,
  loaded into `reg` by `DIGEST (RC(j), L, reg)` on its first row;
* one **path segment** per path item (64 rows, windows `wn = 0, 1`): message `SRC(q)` =
  `sibling ‖ acc` (`dir = 0`) or `acc ‖ sibling` (`dir = 1`); the accumulator window (`aw`)
  loads `reg` from the previous message's digest `DIGEST (SRC(q−1), pl, reg)` (`pl = 32` after
  the leaf segment, else `64`); sibling bytes are free.

`q` counts segments over the whole table (SHA ids `K_SRC + 16·q`, distinct).  The path length
is unconstrained, as in `rootFromPath`.
-/

namespace ZkFormal.NearV3.SrcpV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def rt : Nat := 0
def sg : Nat := 1
def lf : Nat := 2
def wf : Nat := 3
def wl : Nat := 4
def wn : Nat := 5
def sf : Nat := 6
def sl : Nat := 7
def pw : Nat := 8
def q : Nat := 9
def j : Nat := 10
def L : Nat := 11
def qe : Nat := 12
def le : Nat := 13
def dup : Nat := 14
def dir : Nat := 15
def aw : Nat := 16
def pl : Nat := 17
def b : Nat := 18
def cId : Nat := 19
def cLen : Nat := 20
def gD : Nat := 21
def reg (x : Nat) : Nat := 22 + x
/-- running size of the source proofs: `L` per list (its `RC` bytes) and `33` per path item
(hash and direction byte) -/
def sz : Nat := 54
/-- the last row of the last list (sends `SIZE (2, sz)`) -/
def gz : Nat := 55
def width : Nat := 56

/-- List constants (fixed on the root row, carried through the list's segments). -/
def listConst : List Nat := [j, L, qe, le]
/-- Segment constants. -/
def segConst : List Nat := [q, lf, dir, pl]

def actE : Expr := .add (c rt) (c sg)

def constraints : List Expr :=
  [rt, sg, lf, wf, wl, wn, sf, sl, dup, dir, aw, gD, gz].map (fun x => bool (c x)) ++
  [ .mul (c rt) (c sg),
    -- first row: the root row of list 0; the table ends after a complete segment
    .mul .isFirst (not (c rt)), .mul .isFirst (c j), .mul .isFirst (c q),
    .mul .isLast (c rt), .mul .isLast (.mul (c sg) (not (c sl))),
    -- a root row is followed by its leaf segment (next message id)
    .mul (c rt) (not (n sg)), .mul (c rt) (not (n lf)), .mul (c rt) (not (n sf)),
    .mul (c rt) (sub (n q) (.add (c q) (k 1))),
    -- duplicate source key: empty list
    mul3 (c rt) (c dup) (sub (c L) (k 12)),
    -- windows and segments
    .mul (c wf) (not (c sg)), .mul (c wl) (not (c sg)), .mul (c wf) (c pw),
    .mul (c wl) (sub (c pw) (k 31)),
    sub (c sf) (.mul (c wf) (not (c wn))),
    sub (c sl) (.mul (c wl) (.add (c wn) (c lf))),
    .mul (c lf) (c wn), .mul (c lf) (c dir), .mul (c lf) (not (c aw)),
    .mul (c lf) (not (c sg)),
    .mul (c sg) (sub (c aw) (.add (c lf) (.mul (not (c lf))
      (sub (.add (c wn) (c dir)) (smul 2 (.mul (c wn) (c dir))))))),
    mul3 (c sg) (not (c wl)) (not (n sg)),
    mul3 (c sg) (not (c wl)) (n wf),
    mul3 (c sg) (not (c wl)) (sub (n pw) (.add (c pw) (k 1))),
    mul3 (c sg) (not (c wl)) (sub (n wn) (c wn)),
    -- second window of a path segment
    mul3 (c wl) (not (c sl)) (not (n sg)),
    mul3 (c wl) (not (c sl)) (not (n wf)),
    mul3 (c wl) (not (c sl)) (not (n wn)),
    -- after a segment: a path segment of the same list, the next list, or padding
    mul3 (c sl) (n sg) (not (n sf)),
    mul3 (c sl) (n sg) (n lf),
    mul3 (c sl) (n sg) (sub (n q) (.add (c q) (k 1))),
    mul3 (c sl) (n sg) (sub (n pl) (sub (k 64) (smul 32 (c lf)))),
    .mul .isTransition (mul3 (c sl) (n rt) (sub (n q) (c q))),
    .mul .isTransition (mul3 (c sl) (n rt) (sub (n j) (.add (c j) (k 1)))),
    -- end of a list: its last message is `SRC(qe)` of length `le`
    mul3 (c sl) (not (n sg)) (sub (c q) (c qe)),
    mul3 (c sl) (not (n sg)) (sub (c le) (sub (k 64) (smul 32 (c lf)))),
    -- padding is followed by padding
    mul3 .isTransition (not actE) (.add (n rt) (n sg)),
    -- sizes: `L` per list, 33 per path segment; sent once, on the last active row
    .mul .isFirst (sub (c sz) (c L)),
    .mul .isTransition (sub (n sz) (sum [c sz, .mul (n rt) (n L),
      smul 33 (mul3 (n sf) (n sg) (not (n lf)))])),
    .mul (c gz) (not (c sl)),
    .mul .isTransition (.mul (c gz) (.add (n rt) (n sg))),
    .mul (mul3 .isTransition (c sl) (not (c gz))) (not (.add (n rt) (n sg))),
    .mul .isLast (.mul (c sl) (not (c gz))),
    -- accumulator window bytes
    mul3 (c sg) (c aw) (sub (c b) (c (reg 0))),
    -- digest lookups: root row, leaf load, accumulator loads
    sub (c gD) (.add (c rt) (.mul (c wf) (c aw))),
    .mul (c rt) (sub (c cId) (mid K_SRC (c qe))), .mul (c rt) (sub (c cLen) (c le)),
    mul3 (c wf) (c lf) (sub (c cId) (mid K_RC (c j))), mul3 (c wf) (c lf) (sub (c cLen) (c L)),
    .mul (mul3 (c wf) (c aw) (not (c lf))) (sub (c cId) (mid K_SRC (sub (c q) (k 1)))),
    .mul (mul3 (c wf) (c aw) (not (c lf))) (sub (c cLen) (c pl)) ] ++
  listConst.map (fun x => .mul (c rt) (sub (n x) (c x))) ++
  listConst.map (fun x => mul3 (c sg) (not (c sl)) (sub (n x) (c x))) ++
  listConst.map (fun x => mul3 (c sl) (n sg) (sub (n x) (c x))) ++
  segConst.map (fun x => mul3 (c sg) (not (c sl)) (sub (n x) (c x))) ++
  (List.range 31).map (fun x => mul3 (c sg) (not (c wl)) (sub (n (reg x)) (c (reg (x + 1)))))

def regs : List Expr := (List.range 32).map fun x => c (reg x)

def interactions : List Interaction :=
  [ send B_BYTES (c sg) [mid K_SRC (c q), .add (smul 32 (c wn)) (c pw), c b],
    recv B_DIGEST (c gD) ([c cId, c cLen] ++ regs),
    recv B_RCL (c rt) [c j, c L],
    recv B_SRC (c rt) ([c j, c dup] ++ regs),
    send B_SIZE (c gz) [k 2, c sz] ]

/-- `≤ 1984` lists × (`1 + 32 + 64·depth`), depth `≤ 6` on honest witnesses (`< 2^20`). -/
def maxLog : Nat := 20

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.SrcpV3
