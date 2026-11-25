import M5T1.AccSem
import M5T1.ResumeC

/-!
# M5T1.ResumeF — the resume leaf's predicate from the circuit and the chip contract (F-4)

`ResumeC.RsHoldsC` carries `AccOK` (what `ACC` establishes); `AccSem.acc_sound` proves it from
`Holds` and the native chip's contract `ChipOK`. `rsHolds_of`: the leaf statement the prover
establishes (the AIR holds, byte public values, the two digests, public tapes that neither send on
`RNG`/`IF384` nor receive on `ACCD`) plus `ChipOK` gives `RsHoldsC`, so `resume_relC8` applies to
it. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace M5T1.ResumeF

open ZkFormal.Air ZkFormal.Algebra M5T1 M5T1.SegRt M5T1.RbSem M5T1.AccDef M5T1.ResumeC
open NearSpecV3.E2E.Bnd

theorem rsHolds_of {tape xtape : ResumeC.Tp} {d d' : ArenaCore.Bytes} {w : RsW}
    (H : Holds (fullAir tape xtape) w.1 w.2.1) (hb : ∀ i < 1531, pv w.1 i < 256)
    (hd : d = bdigest (bytesOf w.1 BIN 834)) (hd' : d' = bdigest (bytesOf w.1 BOUT 450))
    (hr1 : Bus.NoRng tape) (hr2 : Bus.NoRng xtape)
    (hi1 : MsgRow.NoSendOn B_IF384 tape) (hi2 : MsgRow.NoSendOn B_IF384 xtape)
    (hd1 : AccSem.NoRecvOn B_ACCD tape) (hd2 : AccSem.NoRecvOn B_ACCD xtape)
    (hC : ChipOK w.2.1) : RsHoldsC tape xtape d d' w :=
  ⟨H, hb, hd, hd', AccSem.acc_sound H hb hr1 hr2 hi1 hi2 hd1 hd2 hC⟩

#print axioms rsHolds_of

end M5T1.ResumeF
