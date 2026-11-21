import M5T1.BndLay
import M5T1.Ids

/-!
# M5T1.Ent — the `rt` enter leaf (`eng I c → call I c [] q .pre`)

One table `ENT` (one zero column, height 4) whose constraints are `BndLay.enterCons` on the public
boundary pair (`in`: `engF` at offset 0, `out`: `callF` at offset 408): the edge only relabels the
boundary (phase, `inCall`, clock, Wasm part present), every other field carried; the prepaid gas the
call starts with is checked by the `resume` edge against the receipt (`RX.gas`).
-/

namespace M5T1.Ent

open ZkFormal.Air M5T1.BndLay

def PL : Layout := [("bin", 408), ("bout", 784)]
def NUM_PUB : Nat := PL.width

def table : Table :=
  { width := 1, constraints := enterCons ⟨engF, 0⟩ ⟨callF, 408⟩, interactions := [], maxLog := 2 }

def entAir : Air := { tables := [table], numBuses := NUM_BUSES, numPub := NUM_PUB }

end M5T1.Ent
