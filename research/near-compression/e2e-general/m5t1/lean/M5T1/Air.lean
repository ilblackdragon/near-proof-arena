import M5T1.Rx
import ZkFormal.Sha.Table
import ZkFormal.Air.Export

/-!
# M5T1.Air — the assembled M5-T1 runtime AIR

Tables, in order: `SHA` (the unchanged SHA-256 block table of `ZkFormal.Sha.Table`), `RNG`,
`SCHT`, `MSG`, `DG`, `RX`. The two public tapes (`TAPE`: the statement's receipt-list digest,
outcome leaves and outgoing receipt hashes; `XTAPE`: on T1, the stand-ins for the lanes this
template talks to — lane A's Wasm call and lane B's account read / write) are added by the prover
as cached tables; in Lean they are `tapeTable`s appended to these (`fullAir`).
-/

namespace M5T1

open ZkFormal.Air

def shaTable : Table := ZkFormal.Sha.Table.table B_SHA_BYTES B_SHA_DIGEST

def tableNames : List String := ["SHA", "RNG", "SCHT", "MSG", "DG", "RX"]

def m5t1Air : Air :=
  { tables := [shaTable, Rng.table, Scht.table, Msg.table, Dg.table, Rx.table],
    numBuses := NUM_BUSES, numPub := Rx.NUM_PUB }

/-- A public tape: constant messages, sent / received once on the first row. -/
def tapeTable (tape : List (Nat × Bool × List Nat)) : Table :=
  { width := 0, constraints := [], maxLog := 22,
    interactions := tape.map fun e =>
      { bus := e.1, mult := [.isFirst], msg := e.2.2.map Expr.const, send := e.2.1 } }

/-- The AIR the prover runs: the exported tables, then the statement tape and the stand-in tape. -/
def fullAir (tape xtape : List (Nat × Bool × List Nat)) : Air :=
  { m5t1Air with tables := m5t1Air.tables ++ [tapeTable tape, tapeTable xtape] }

def layouts : List (String × Layout) :=
  [("RNG", Rng.L), ("SCHT", Scht.L), ("MSG", Msg.L), ("DG", Dg.L), ("RX", Rx.L)]

def q (s : String) : String := "\"" ++ s ++ "\""

def namesJson : String :=
  "{" ++ ",".intercalate (layouts.map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++
  ",\"tables\":[" ++ ",".intercalate (tableNames.map q) ++ "]" ++
  ",\"pub\":[" ++ ",".intercalate (Rx.PL.names.map q) ++ "]" ++
  s!",\"schNbits\":{Scht.NBITS}" ++
  ",\"rxBytes\":[" ++ ",".intercalate (Rx.byteGroups.map fun (g, _) => q g) ++ "]" ++
  ",\"rxBits\":[" ++ ",".intercalate (Rx.bitGroups.map fun (g, _) => q g) ++ "]}"

def jsonNat (l : List Nat) : String := "[" ++ ",".intercalate (l.map toString) ++ "]"

/-- The schema, for the trace generator: every entry's `SCH` message in table order. -/
def schemaJson : String :=
  "{\"fields\":[" ++ ",".intercalate (schFields.map q) ++ "],\"entries\":[" ++
  ",".intercalate (schema.map fun g => jsonNat g.msg) ++ "]," ++
  s!"\"buses\":\{\"SHA_BYTES\":{B_SHA_BYTES},\"SHA_DIGEST\":{B_SHA_DIGEST},\"RNG\":{B_RNG}," ++
  s!"\"SCH\":{B_SCH},\"FB\":{B_FB},\"FLEN\":{B_FLEN},\"MBEG\":{B_MBEG},\"MLEN\":{B_MLEN}," ++
  s!"\"HB\":{B_HB},\"SREQ\":{B_SREQ},\"SRQ\":{B_SRQ},\"SRS\":{B_SRS},\"HBR\":{B_HBR}," ++
  s!"\"VMCALL\":{B_VMCALL},\"VMRES\":{B_VMRES},\"OUTC\":{B_OUTC},\"OUTR\":{B_OUTR}}}"

end M5T1
