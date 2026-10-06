import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids

/-!
# ZkFormal.NearV3.Rcpt.Tables.Bnd — `bndV3`: own-shard routing intervals (chained provider)

A2: every applied receipt routes to the own shard, i.e. its receiver lies in one of the own
shard's intervals `[lo_q, hi_q)` (`NearSpecV3.ownIntervals`; a missing `lo` is the empty
string, a missing `hi` is `+∞`).  The public data give, per interval `q` and position
`i ≤ 64`, the record `x = 65·q + i` with `lo_i`, `hi_i` (the byte, or `0` past the end:
account-id bytes are never `0`) and `hn` (`hi` missing).

One row per public record: receives `BNDP (x, lo, hi, hn)` from the public bus and is a chained
provider of `BND (x, lo, hi, hn, u)`: sends `u = 0`, receives the final use count `U`.  Each
routing lookup of `rcptV3` receives `u` and sends `u + 1`.
-/

namespace ZkFormal.NearV3.BndV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def act : Nat := 0
def x : Nat := 1
def lo : Nat := 2
def hi : Nat := 3
def hn : Nat := 4
def uu : Nat := 5
def width : Nat := 6

def constraints : List Expr :=
  [ bool (c act),
    -- active rows first, then padding
    mul3 .isTransition (not (c act)) (n act) ]

def rec4 : List Expr := [c x, c lo, c hi, c hn]

def interactions : List Interaction :=
  [ recv B_BNDP (c act) rec4,
    send B_BND (c act) (rec4 ++ [k 0]),
    recv B_BND (c act) (rec4 ++ [c uu]) ]

/-- `≤ 64` intervals × 65 positions. -/
def maxLog : Nat := 13

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.BndV3
