import ZkFormal.Air.Export
import ZkFormal.V2.Air

/-!
# ZkFormal.V2.Export — the v2 AIR description consumed by the Rust prover

`AirP.exportJson AP` is the text of format `np-air-v2` (`docs/zk-formal/FORMATS.md` §8).  It is
the v1 export of `AP.toAir` (same keys, same expression encoding, same table objects) with
`"format":"np-air-v2"` and two extra top-level keys:

* `"pubSegs"`: the public segments, in order, each
  `{"bus":b,"send":true|false,"width":w,"countAt":i,"start":s}`;
* `"maxPub"`: the static bound on the used part of the public vector.

Like v1's export, it is not part of soundness.  A mismatch can only make honest proofs fail.
-/

namespace ZkFormal.V2

open ZkFormal.Air

def PubSeg.toJson (s : PubSeg) : String :=
  s!"\{\"bus\":{s.bus},\"send\":{if s.send then "true" else "false"},\"width\":{s.width}," ++
  s!"\"countAt\":{s.countAt},\"start\":{s.start}}"

/-- **The v2 export.** -/
def AirP.exportJson (AP : AirP) : String :=
  s!"\{\"format\":\"np-air-v2\",\"numBuses\":{AP.numBuses},\"numPub\":{AP.numPub}," ++
  s!"\"tables\":{jsonList (AP.tables.map Table.toJson)}," ++
  s!"\"pubSegs\":{jsonList (AP.pubSegs.map PubSeg.toJson)},\"maxPub\":{AP.maxPub}}"

end ZkFormal.V2
