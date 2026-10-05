import ZkFormal.NearAssembly.Final
import ZkFormal.Near.Render.Proof.MinHeight

/-!
# ZkFormal.NearAssembly.MinHeight — R-L7-6 (from L6)

The SHA table of every honest NEAR trace has `log ≥ 5` (it hashes at least the
receipt commitment `RC`, one block = 18 rows), so the query domain is `≥ 2^8`.
-/

namespace ZkFormal.NearAssembly

open ZkFormal.Near

theorem near_min_height : NearMinHeightStmt := by
  intro c w _
  exact ⟨T_SHA, by decide, Nat.le_trans (by decide) (Render.render_sha_log_ge c.1 (extOf c.1 w))⟩

end ZkFormal.NearAssembly
