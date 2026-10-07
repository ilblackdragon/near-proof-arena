import ReexecV3D3.Logged.WasmHostL

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

/-- The erased store record. -/
def dr (r : RealStore) : RealStore := { r with store := dummy }


end ReexecV3D3.Logged.W
