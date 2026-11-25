import M5T1.BndLay
import M5T1.Ids
import M5T1.Msg

/-!
# M5T1.Ent — the `rt` enter leaf (`eng I c → call I c [] q .pre`)

One table `ENT` (one zero column, height 4; F-6: plus `RNG`, `entAirB`) whose constraints are `BndLay.enterCons` on the public
boundary pair (`in`: `engF` at offset 0, `out`: `callF` at offset 450): the edge relabels the
boundary (phase, `inCall`, clock, Wasm part present), writes lane A's `.pre` Wasm record (`fbBnd`
constants and, S2, `codeRoot = code hash ‖ 0^10`), and carries every other field; `rPrepaid` and the
remainder digest `vmCtxDigest` are the query's (named checks of the leaf, `EnterC.EntChecks`).
-/

namespace M5T1.Ent

open ZkFormal.Air M5T1.BndLay

def PL : Layout := [("bin", 450), ("bout", 834)]
def NUM_PUB : Nat := PL.width

def table : Table :=
  { width := 1, constraints := enterCons ⟨engF, 0⟩ ⟨callF, 450⟩, interactions := [], maxLog := 2 }

def entAir : Air := { tables := [table], numBuses := NUM_BUSES_F3, numPub := NUM_PUB }

/-! ## F-6: the exported enter AIR — every public value a byte, in-circuit

`ENT` with one `RNG` receive per public value (`pubBytes`, row 0) and the `RNG` table. Its
constraints are `table`'s, so every lemma about `entAir` applies (`PubBytes.ent_core`: `Holds
entAirB → Holds entAir`), and the leaf predicate's byte premise is now a consequence of the
circuit (`PubBytes.ent_bytes`). This is the AIR the prover runs (`m5t1-tool air-ent`). -/

def tableB : Table := { table with interactions := pubBytes NUM_PUB }

def tableNamesB : List String := ["ENT", "RNG"]

def entAirB : Air := { tables := [tableB, Rng.table], numBuses := NUM_BUSES_F3, numPub := NUM_PUB }

end M5T1.Ent
