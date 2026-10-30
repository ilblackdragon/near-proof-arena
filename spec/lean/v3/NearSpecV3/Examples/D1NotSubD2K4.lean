import NearSpecV3.Examples.D1NotSubD2Data
import NearSpecV3.ChunkValidationD1a

/-! One kernel decision of the D1 ⊄ D2 counterexample: the pair is also in `RelD1a` (all the D1a
amendments hold at the challenge instance `B0`). -/

namespace NearSpecV3.Examples

open NearSpec NearSpecV3

set_option maxRecDepth 200000 in
theorem gf_relD1a : RelD1a B0 claimGF witnessGF := by decide +kernel

end NearSpecV3.Examples
