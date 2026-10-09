import ReexecV3D3.Logged.Runtime.D3Check

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3

/-- `checkD3` and its recorded-storage reads, in one run. -/
def checkD3Reads (cb wb : Bytes) : Except String Unit × List (Nat × Bytes) :=
  SM.runR (storeFn (storesData wb)) (checkD3L cb wb)

/-- The keys `checkD3 cb wb` reads. -/
def d3Reads (cb wb : Bytes) : List (Nat × Bytes) := (checkD3Reads cb wb).2


def checkD2Reads (cb wb : Bytes) : Except String Unit × List (Nat × Bytes) :=
  SM.runR (storeFn (storesData wb)) (checkD2L cb wb)

def d2Reads (cb wb : Bytes) : List (Nat × Bytes) := (checkD2Reads cb wb).2


end ReexecV3D3.Logged
