import ZkFormal.Sha.Table
import ZkFormal.Algebra.Fp
import ZkFormal.Near.Ids
import ZkFormal.Near.Tables.Node
import ZkFormal.Near.Tables.Walk
import ZkFormal.Near.Tables.Rcpt
import ZkFormal.Near.Tables.Acct
import ZkFormal.Near.Tables.Mrk
import ZkFormal.Near.Tables.Sort

/-!
# ZkFormal.Near.Air — the NEAR AIR value `nearAir` and `publicOf`

Table order (fixed; table index = position): `0 sha` (L5), `1 node`,
`2 walk`, `3 rcpt`, `4 acct`, `5 mrk`, `6 sort` (NEAR-AIR.md §3).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

def T_SHA : Nat := 0
def T_NODE : Nat := 1
def T_WALK : Nat := 2
def T_RCPT : Nat := 3
def T_ACCT : Nat := 4
def T_MRK : Nat := 5
def T_SORT : Nat := 6

def nearTables : List Table :=
  [Sha.Table.table B_BYTES B_DIGEST, Node.table, Walk.table, Rcpt.table, Acct.table, Mrk.table,
   Sort.table]

/-- **The NEAR AIR.** -/
def nearAir : Air := { tables := nearTables, numBuses := numBuses, numPub := numPub }

/-- Public inputs of a claim: its canonical bytes as field elements. -/
def publicOf (c : WfClaim) : List Fp := c.1.encode.map fun b => Fp.ofNat b.toNat

end ZkFormal.Near
