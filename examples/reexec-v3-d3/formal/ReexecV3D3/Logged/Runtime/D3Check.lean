import ReexecV3D3.Logged.D3L

namespace NearSpecV3.D3

open NearSpec NearSpecV3 NearSpecV3.D2 ReexecV3D3.Logged

/-- `checkD3` with every recorded-storage read through `SM` (tagged store `storesOf witnessBytes`). -/
def checkD3L (claimBytes witnessBytes : Bytes) : SM (Nat × Bytes) Unit :=
  checkD2CoreL (d3HooksL Wasm.pv86) true claimBytes witnessBytes (some gAlpha)

end NearSpecV3.D3

