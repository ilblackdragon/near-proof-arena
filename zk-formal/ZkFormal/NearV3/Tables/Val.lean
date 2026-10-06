import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.Tables.Val — `valV3`: revealed value records (pre-state bytes)

Lane `v3-trie`.  One segment per value record `vid` (tree-shaped: one record per revealed
value slot occurrence), one row per byte; an empty value (`vz`) is a single row without a
byte.  Then one `SUM` row, then padding.  A record
* hashes its bytes: `BYTES (VPRE(vid), pos, b)` (`sha_t`);
* receives the same bytes from the value's parser on `VBYTES (vid, pos, b)` (`acct`, `akey`,
  `sched`, `qvals`, or a public segment), so the parser and the trie see one value;
* receives `VPARENT (vid, len)` from the value window of its (unique) node record;
* takes part in weak uniqueness like a node record: `DUP` / `ENT` (an empty value sends
  the marker `ENT (eid, 0, 0, 0)` so that it can only equal another empty value);
* is counted (non-duplicates) in `sz`, sent as `SIZE (1, sz)`.
Ids are consecutive (`vid' = vid + 1`), hence distinct.
-/

namespace ZkFormal.NearV3.ValV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def act : Nat := 0
def vf : Nat := 1
def vl : Nat := 2
def vid : Nat := 3
def len : Nat := 4
def pos : Nat := 5
def b : Nat := 6
def vz : Nat := 7
def dup : Nat := 8
def hd : Nat := 9
def repE : Nat := 10
def sz : Nat := 11
def sumr : Nat := 12
/-- byte gate `act·(1 − vz)` and duplicate gate `vf·dup` as columns (degree 1) -/
def gb : Nat := 13
def gdu : Nat := 14
def width : Nat := 15

def valConst : List Nat := [vid, len, vz, dup, hd, repE]

def constraints : List Expr :=
  [act, vf, vl, vz, dup, hd, sumr, gb, gdu].map (fun x => bool (c x)) ++
  [ sub (c gb) (.mul (c act) (not (c vz))), sub (c gdu) (.mul (c vf) (c dup)),
    .mul (c dup) (not (c act)), .mul (c hd) (not (c act)) ] ++
  [ .mul (c vf) (not (c act)), .mul (c vl) (not (c act)), .mul (c act) (c sumr),
    .mul .isFirst (sub (.add (c act) (c sumr)) (k 1)), .mul .isFirst (sub (c act) (c vf)),
    .mul .isFirst (c sz),
    -- value ids start at 0 (so `VPRE(vid)` ids stay below `P` and apart from node ids)
    .mul .isFirst (c vid),
    .mul .isLast (c act),
    .mul (c vf) (c pos),
    -- an empty value is one row without a byte
    .mul (c vz) (not (c vf)), .mul (c vz) (not (c vl)), .mul (c vz) (c len), .mul (c vz) (c b),
    .mul (.mul (c vl) (not (c vz))) (sub (.add (c pos) (k 1)) (c len)),
    -- within a record
    mul3 (c act) (not (c vl)) (not (n act)),
    mul3 (c act) (not (c vl)) (n vf),
    mul3 (c act) (not (c vl)) (sub (n pos) (.add (c pos) (k 1))) ] ++
  valConst.map (fun x => mul3 (c act) (not (c vl)) (sub (n x) (c x))) ++
  [ -- after a record: the next record (next id) or the SUM row
    .mul (c vl) (sub (k 1) (.add (n act) (n sumr))),
    mul3 (c vl) (n act) (not (n vf)),
    mul3 (c vl) (n act) (sub (n vid) (.add (c vid) (k 1))),
    -- SUM and padding rows are followed by padding (not on the last row)
    mul3 .isTransition (c sumr) (n act), mul3 .isTransition (c sumr) (n sumr),
    mul3 .isTransition (not (.add (c act) (c sumr))) (n act),
    mul3 .isTransition (not (.add (c act) (c sumr))) (n sumr),
    -- bytes of non-duplicate records
    .mul .isTransition (sub (n sz) (.add (c sz) (mul3 (c act) (not (c vz)) (not (c dup))))) ]

def entMsg (e : Expr) : List Expr := [e, c len, c pos, c b]

def interactions : List Interaction :=
  [ send B_BYTES (c gb) [mid K_VPRE (c vid), c pos, c b],
    recv B_VBYTES (c gb) [c vid, c pos, c b],
    recv B_VPARENT (c vf) [c vid, c len],
    recv B_DUP (c gdu) [mid K_VPRE (c vid), c repE],
    send B_ENT (c hd) (entMsg (mid K_VPRE (c vid))),
    recv B_ENT (c dup) (entMsg (c repE)),
    send B_SIZE (c sumr) [k 1, c sz] ]

/-- Unfolded value bytes `≤ 3,000,000` (A7) plus the `SUM` row. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.ValV3
