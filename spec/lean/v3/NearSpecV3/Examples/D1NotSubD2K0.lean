import NearSpecV3.Examples.D1NotSubD2Data

/-! One kernel decision of the D1 ⊄ D2 counterexample (`D1NotSubD2`). -/

namespace NearSpecV3.Examples

open NearSpec NearSpecV3

set_option maxRecDepth 200000 in
theorem gf_acceptsD0 : acceptsD0 claimGF witnessGF = true := by decide +kernel

end NearSpecV3.Examples
