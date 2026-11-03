import StateM5a.Trie
import StateM5a.Ws
import ZkFormal.Sha.Table
import ZkFormal.Air.Export

/-!
# StateM5a.Air — the assembled M5a AIR

Tables, in order: `SHA` (the unchanged SHA-256 block table of `ZkFormal.Sha.Table`, whose
soundness is `ZkFormal.Sha.sha_digest_contract_closed`), `KEY`, `BR`, `SN`, `KCMP`, `WSB`,
`WSN`, `WSA`, `SNC`, `RNG`.  The SHA-512 compression chip (native, `native/sha384-air4`) and the public tape are
added by the prover.  Public values `0..15`: `prev_state_root` as 16 limbs of 16 bits.
-/

namespace StateM5a

open ZkFormal.Air

def shaTable : Table := ZkFormal.Sha.Table.table B_SHA_BYTES B_SHA_DIGEST

def tableNames : List String := ["SHA", "KEY", "BR", "SN", "KCMP", "WSB", "WSN", "WSA", "SNC", "RNG"]

def m5aAir (D : Nat) : Air :=
  { tables := [shaTable, Key.table, Br.table, Sn.table, Kcmp.table, Wsb.table D, Wsn.table D,
      Wsa.table D, Snc.table, Rng.table],
    numBuses := NUM_BUSES, numPub := 16 }

def layouts (D : Nat) : List (String × Layout) :=
  [("KEY", Key.L), ("BR", Br.L), ("SN", Sn.L), ("KCMP", Kcmp.L), ("WSB", Wsb.L), ("WSN", Wsn.L),
   ("WSA", Wsa.L D), ("SNC", Snc.L), ("RNG", Rng.L)]

def namesJson (D : Nat) : String :=
  let q (s : String) := "\"" ++ s ++ "\""
  "{" ++ ",".intercalate ((layouts D).map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++
  s!",\"D\":{D},\"tables\":[" ++ ",".intercalate (tableNames.map q) ++ "]}"

end StateM5a
