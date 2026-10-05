import ZkFormal.Near.Tables.Dsl

/-!
# ZkFormal.Near.Tables.Sort — distinct receipt ids (NEAR-AIR.md §3.6)

One 32-row segment per receipt id, received byte by byte on
`RIDS (r, i, byte)` (from `rcpt`), least significant byte first (the id read
as a little-endian 256-bit integer).  The delay line `d` holds the bytes of
the previous 32 rows, so `d 31` is byte `i` of the previous segment's id.
Every segment after the first satisfies `id_t = id_{t−1} + diff + 1`
byte-serially (`diff` bytes as bits, carry bit `cout`, carry-in 1 at byte 0, no
final carry): the ids are strictly increasing, hence pairwise distinct.
-/

namespace ZkFormal.Near.Sort

open ZkFormal.Air ZkFormal.Near.Dsl

def act : Nat := 0
def sf : Nat := 1
def sl : Nat := 2
def ft : Nat := 3
def rr : Nat := 4
def i : Nat := 5
def bb : Nat := 6
def cin : Nat := 7
def cout : Nat := 8
def dbit (j : Nat) : Nat := 9 + j
def d (j : Nat) : Nat := 17 + j
def width : Nat := 49

def diffE : Expr := bits (fun j => c (dbit j)) 0 8

def constraints : List Expr :=
  ([act, sf, sl, ft, cin, cout] ++ (List.range 8).map dbit).map (fun x => bool (c x)) ++
  [ .mul (c sf) (not (c act)), .mul (c sl) (not (c act)),
    .mul .isFirst (not (c sf)), .mul .isFirst (not (c ft)),
    .mul .isLast (.mul (c act) (not (c sl))),
    .mul (c sf) (c i), .mul (c sl) (sub (c i) (k 31)),
    .mul (c sf) (not (c cin)), .mul (c sl) (c cout),
    -- within a segment
    mul3 (c act) (not (c sl)) (not (n act)),
    mul3 (c act) (not (c sl)) (n sf),
    mul3 (c act) (not (c sl)) (sub (n rr) (c rr)),
    mul3 (c act) (not (c sl)) (sub (n ft) (c ft)),
    mul3 (c act) (not (c sl)) (sub (n i) (.add (c i) (k 1))),
    mul3 (c act) (not (c sl)) (sub (n cin) (c cout)),
    -- next segment or padding
    mul3 (c sl) (n act) (not (n sf)),
    mul3 (c sl) (n act) (n ft),
    mul3 .isTransition (not (c act)) (n act),
    -- id_t = id_{t-1} + diff + 1
    .mul (.mul (c act) (not (c ft)))
      (sub (c bb) (sub (.add (c (d 31)) (.add diffE (c cin))) (smul 256 (c cout)))),
    -- delay line
    .mul (c act) (sub (n (d 0)) (c bb)) ] ++
  (List.range 31).map (fun j => .mul (c act) (sub (n (d (j + 1))) (c (d j))))

def interactions : List Interaction := [ recv B_RIDS (c act) [c rr, c i, c bb] ]

/-- `≤ 256` ids × 32 rows. -/
def maxLog : Nat := 13

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.Near.Sort
