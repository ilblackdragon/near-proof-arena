import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.Tables.Uniq — `uniqV3`: weak uniqueness of store digests

Lane `v3-trie`, V3-D0-DESIGN §3.3 as amended by §11 (A6 rejected, **weak** `uniq`).

One 32-row segment per store entry `eid` (a node record `NPRE(N)` or a value record
`VPRE(vid)` of instance `τ`), receiving the entry's digest byte by byte on
`DIGS (eid, τ, i, byte)` from the digest window that consumed it in `nodeV3`.  The key
of an entry is `(τ, digest)` with the digest read as a little-endian 256-bit integer.

Entries are sorted by key **non-strictly**:
* `τ` is segment-constant and steps by a bit `s` between consecutive segments
  (`τ_t = τ_{t−1} + s_t`), so the entries of one instance are contiguous;
* within an instance (`s = 0`), the flag `eq` selects
  * `eq = 0`: `digest_t = digest_{t−1} + diff + 1` (strictly larger), or
  * `eq = 1`: `diff = 0` and carry-in `0`, i.e. `digest_t = digest_{t−1}`; the segment then
    sends `DUP (eid_t, eid_{t−1})`, and `nodeV3` proves the two entries' messages
    byte-equal (`ENT` copy).

So equal keys ⇒ equal bytes along the sorted order, hence for any two entries
(`weakUniq_functional`): the store is hash-functional without assuming distinct digests.
Byte-serial comparison as v1 `sort` (delay line of 32 bytes, `diff` bits, carry bits).
-/

namespace ZkFormal.NearV3.Uniq

open ZkFormal.Air ZkFormal.Near.Dsl

def act : Nat := 0
def sf : Nat := 1
def sl : Nat := 2
def ft : Nat := 3
def eid : Nat := 4
def peid : Nat := 5
def tau : Nat := 6
def st : Nat := 7
def eq : Nat := 8
def i : Nat := 9
def bb : Nat := 10
def cin : Nat := 11
def cout : Nat := 12
def dbit (j : Nat) : Nat := 13 + j
def d (j : Nat) : Nat := 21 + j
def width : Nat := 53

def diffE : Expr := bits (fun j => c (dbit j)) 0 8

/-- Segment-constant columns. -/
def segConst : List Nat := [eid, peid, tau, st, eq, ft]

/-- Comparison gate: active, not the first segment, same instance. -/
def cmpG : Expr := mul3 (c act) (not (c ft)) (not (c st))

def constraints : List Expr :=
  ([act, sf, sl, ft, st, eq, cin, cout] ++ (List.range 8).map dbit).map (fun x => bool (c x)) ++
  [ .mul (c sf) (not (c act)), .mul (c sl) (not (c act)),
    .mul .isFirst (not (c sf)), .mul .isFirst (not (c ft)),
    .mul .isLast (.mul (c act) (not (c sl))),
    .mul (c sf) (c i), .mul (c sl) (sub (c i) (k 31)),
    -- carry-in at byte 0: 1 (strict) or 0 (equal); no carry out of byte 31
    .mul (c sf) (sub (c cin) (not (c eq))), .mul (c sl) (c cout),
    -- the first entry has no predecessor; an equal entry is in the same instance
    .mul (c ft) (c eq), .mul (c eq) (c st),
    -- equal: no difference bytes
    .mul (c eq) diffE,
    -- within a segment
    mul3 (c act) (not (c sl)) (not (n act)),
    mul3 (c act) (not (c sl)) (n sf),
    mul3 (c act) (not (c sl)) (sub (n i) (.add (c i) (k 1))),
    mul3 (c act) (not (c sl)) (sub (n cin) (c cout)) ] ++
  segConst.map (fun x => mul3 (c act) (not (c sl)) (sub (n x) (c x))) ++
  [ -- next segment or padding
    mul3 (c sl) (n act) (not (n sf)),
    .mul .isTransition (mul3 (c sl) (n act) (n ft)),
    .mul (mul3 (c sl) (n act) .isTransition) (sub (n peid) (c eid)),
    .mul (mul3 (c sl) (n act) .isTransition) (sub (n tau) (.add (c tau) (n st))),
    mul3 .isTransition (not (c act)) (n act),
    -- key_t = key_{t-1} + diff + cin (byte-serially)
    .mul cmpG (sub (c bb) (sub (.add (c (d 31)) (.add diffE (c cin))) (smul 256 (c cout)))),
    -- delay line
    .mul (c act) (sub (n (d 0)) (c bb)) ] ++
  (List.range 31).map (fun j => .mul (c act) (sub (n (d (j + 1))) (c (d j))))

def interactions : List Interaction :=
  [ recv B_DIGS (c act) [c eid, c tau, c i, c bb],
    send B_DUP (.mul (c sf) (c eq)) [c eid, c peid] ]

/-- `≤ 2^17` entries (nodes and values of all instances, A7 cap) × 32 rows. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Uniq
