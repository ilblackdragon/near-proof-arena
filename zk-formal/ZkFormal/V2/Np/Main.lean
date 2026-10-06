import ZkFormal.V2.Np.Early
import ZkFormal.V2.Np.Query

/-!
# ZkFormal.V2.Np.Main — round-by-round soundness of np-udr-stark-v2 (L3 deliverable)

`rbrWithP`: for every v2 AIR `AP` and parameters with `NpOkP AP prm` (v1's `NpOk` for
`AP.toAir`, plus `AirP.wf`), the IOP verifier `Iop.verifierP Fp Fp8 AP prm` has
round-by-round soundness facts for the language `AirLangP AP` (`∃ tr, HoldsP`).  It has
the same budgets as v1: at most `2^36` bad challenges per round, and `agreeUdr` passing
query positions.
-/

namespace ZkFormal.V2.Np

open ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

theorem rbrWithP (AP : AirP) (prm : Params) (hok : NpOkP AP prm) :
    RbrWith (VnpP AP prm) (AirLangP AP) Fp8.all badBudget (agreeUdr prm.logBlowup) (DoomedP AP prm) :=
  rbrWithP_of shapedPrefix scheduleAlt msg0P msg2P msg4P msg6P msg8P msgLateP chal1P chal3P chal5P chal7P
    chalLateP queryP AP prm hok

theorem rbrFactsP (AP : AirP) (prm : Params) (hok : NpOkP AP prm) :
    RbrFacts (VnpP AP prm) (AirLangP AP) Fp8.all badBudget (agreeUdr prm.logBlowup) :=
  ⟨DoomedP AP prm, rbrWithP AP prm hok⟩

end ZkFormal.V2.Np
