import ZkFormal.Air.Basic
import ZkFormal.Near.Ids

/-!
# ZkFormal.Near.Tables.Rcpt — the `rcpt` table (NEAR-AIR.md §3)

Skeleton: layout and constraints land with the table's sub-lane.
-/

namespace ZkFormal.Near.Rcpt

open ZkFormal.Air

def width : Nat := 1
def maxLog : Nat := 1

def table : Table := { width := width, constraints := [], interactions := [], maxLog := maxLog }

end ZkFormal.Near.Rcpt
