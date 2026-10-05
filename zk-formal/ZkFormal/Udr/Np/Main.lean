import ZkFormal.Udr.Np.Compose
import ZkFormal.Udr.Np.Shape
import ZkFormal.Udr.Np.Early
import ZkFormal.Udr.Np.Msg4
import ZkFormal.Udr.Np.Msg8
import ZkFormal.Udr.Np.FrameMsg
import ZkFormal.Udr.Np.BusRounds
import ZkFormal.Udr.Np.Ali
import ZkFormal.Udr.Np.Chal7
import ZkFormal.Udr.Np.Late
import ZkFormal.Udr.Np.Bridge7
import ZkFormal.Udr.Np.DeepSem

/-!
# ZkFormal.Udr.Np.Main — round-by-round soundness of np-udr-stark (L3 deliverable)

`rbrWith`: for every AIR `A` and parameters satisfying `NpOk A prm`, the IOP
verifier `Iop.verifier Fp Fp8 A prm` has round-by-round soundness facts
(`RbrWith`, the input of L2's `Bcs.stark_romSound_rbr`) for the language
`AirLang Fp A`, with at most `2^36` bad challenges per round among all of
`Fp8` and at most `agreeUdr prm.logBlowup n` passing query positions out of
`n` for doomed transcripts.
-/

namespace ZkFormal.Udr.Np

open ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

theorem rbrWith (A : Air) (prm : Params) (hok : NpOk A prm) :
    RbrWith (Vnp A prm) (AirLang Fp A) Fp8.all badBudget (agreeUdr prm.logBlowup) (Doomed A prm) :=
  rbrWith_of shapedPrefix scheduleAlt msg0 msg2 msg4 msg6 msg8 msgLate chal1 chal3 chal5 chal7
    chalLate (query_of_deepSem deepSem) A prm hok

theorem rbrFacts (A : Air) (prm : Params) (hok : NpOk A prm) :
    RbrFacts (Vnp A prm) (AirLang Fp A) Fp8.all badBudget (agreeUdr prm.logBlowup) :=
  ⟨Doomed A prm, rbrWith A prm hok⟩

end ZkFormal.Udr.Np
