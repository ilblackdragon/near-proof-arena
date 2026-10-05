import ZkFormal.Near.Air
import ZkFormal.Udr.Np.Statements

/-!
# ZkFormal.Near.NpOkCheck — `NpOk nearAir Params.default` (lane L3's side condition)

Per table, `#constraints + 2·aux + 3·interactions ≤ 2^20`, and `numBuses < 2^30`;
checked by kernel evaluation (leaf module).
-/

namespace ZkFormal.Near

theorem nearAir_npOk : ZkFormal.Udr.Np.NpOk nearAir ZkFormal.Stark.Params.default := by
  refine ⟨rfl, ?_, by decide⟩
  decide +kernel

end ZkFormal.Near
