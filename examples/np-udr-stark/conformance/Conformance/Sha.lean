import ZkFormal.Sha.Table
import ZkFormal.Sha.Gen

/-!
# Conformance.Sha — the SHA-256 toy AIR of milestone M1 (second toy)

Lane L5's SHA-256 block table `ZkFormal.Sha.Table.table busBytes busDigest`
plus two minimal companion tables so that both buses balance:

* `bytesTable` (width 4, columns `Id, pos, byte, s`): **sends**
  `(Id, pos, byte)` on `busBytes` with multiplicity bit `s` (the SHA table
  receives every message byte there);
* `digestTable` (width 35, columns `Id, len, d0..d31, s`): **receives**
  `(Id, len, d0..d31)` on `busDigest` with multiplicity bit `s` (the SHA
  table sends each message's digest there).

The companions have no constraints of their own (only the generated
multiplicity-bit booleanity constraints): they model an arbitrary
producer/consumer.  `npudr` (src/sha.rs) mirrors this file term for term, so
`npudr export sha` equals `np-lean-export sha` byte for byte.

`toyMsgs lens` is the deterministic message family shared with the Rust side:
message `i` has id `i + 1`, digest multiplicity 1, and byte `j` equal to
`(37·j + 11·i + 5) mod 256`.
-/

namespace Conformance.Sha

open ZkFormal.Air

def busBytes : Nat := 0
def busDigest : Nat := 1

private def cur (c : Nat) : Expr := .col c false

def bytesTable : Table where
  width := 4
  constraints := []
  interactions := [{ bus := busBytes, mult := [cur 3], msg := [cur 0, cur 1, cur 2], send := true }]
  maxLog := 22

def digestTable : Table where
  width := 35
  constraints := []
  interactions := [{ bus := busDigest, mult := [cur 34], msg := (List.range 34).map cur, send := false }]
  maxLog := 22

def shaAir : Air :=
  { tables := [ZkFormal.Sha.Table.table busBytes busDigest, bytesTable, digestTable],
    numBuses := 2, numPub := 0 }

def toyByte (i j : Nat) : Nat := (37 * j + 11 * i + 5) % 256

def toyMsgs (lens : List Nat) : List ZkFormal.Sha.Gen.Msg :=
  (lens.zip (List.range lens.length)).map fun (n, i) =>
    { id := i + 1, bytes := (List.range n).map (toyByte i), dmult := true }

end Conformance.Sha
