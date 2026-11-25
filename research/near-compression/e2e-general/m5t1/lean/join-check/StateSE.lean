
/-!
# Lane F, F-5: the STATE working-set mode's engine half (`SE`) in lane E's D-c instance

Appended to lane E's `join/StViewE.lean` + `join/StateW.lean` (not lake modules) by
`join-check/run.sh`, which elaborates the concatenation in lane F's package environment (`M5T1`,
which requires lane B's `StateM5a`).

* **`state_engHalf`** — lane F's `EngHalfRCOn` on `StatePreW` for lane E's `stSem` (`W` = the
  42-B `stRoot`, traffic lane B's `StQ`): `M5T1.SeC.se_engHalf` with the leaf's `HoldsE` = `SE`'s
  rows, traffic `qOfS` (`SREQ`/`HB` change list, the `STMQ`/`STMA` metas), state pair the two
  `stRoot`s.
* **`stateSeg_relC8`** — the STATE working-set leaf (`SE` ⊕ lane B's `m5tSegC`) is relatively,
  canonically sound: `state_engHalf` ∧ lane B's `HoldsSt` (`StcSound.holdsSt_seg`, from `Holds`
  of `m5tSegC`) via lane E's `state_sound_stRoot`.

Named: `SeC.SeStep` (the VM-free engine rows), the joined AIR's `joint` (one trace for both halves).
-/

namespace LaneF.StateSE

open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.SB NearSpecV3.E2E.M8
open NearSpecV3.E2E.Glue StateM5a.StateView StateM5a.StHalfC LaneE.StateW M5T1.SeC

/-- The STATE working-set leaf's engine half as `stAir`'s `HoldsE`. -/
def segHoldsE (xtape : M5T1.SeC.Tp) : NearSpec.Bytes → LB → LB → StQ → NearSpec.Bytes → NearSpec.Bytes → Prop :=
  fun ctx b b' q r r' => ∃ w, SeHolds8 xtape ctx b b' w ∧ q = qOfS w ∧ r = rInS w.1 ∧ r' = rOutS w.1

/-- **Lane F's engine half for the working-set mode** (`EngHalfRCOn` on `StatePreW`). -/
theorem state_engHalf {sf : Intake → NearSpecV3.Wasm.TTN.Store} {V : ViewImpl} (hV : M5T1.ResumeC.RsView V)
    (xtape : M5T1.SeC.Tp) {HoldsS joint}
    (hS : SeStep V (stSem V (A := seAirs xtape) (HoldsE := segHoldsE xtape) (HoldsS := HoldsS)
      (joint := joint)) (StatePreW V) xtape (fun w r' => r' = rOutS w.1) qOfS) :
    EngHalfRCOn sf V (stSem V (A := seAirs xtape) (HoldsE := segHoldsE xtape) (HoldsS := HoldsS)
      (joint := joint)) (StatePreW V) Sha384Coll :=
  se_engHalf hV _ _ xtape _ qOfS id (fun _ => rfl)
    (fun _ _ _ _ _ _ ⟨w, h, hq, hr, hr'⟩ => ⟨w, h, hq, hr, hr'⟩) hS

/-- **The STATE working-set leaf is relatively, canonically sound** (lane F's `SE` engine half ∧
lane B's `HoldsSt` ∧ lane E's `reqsRel_state`). -/
theorem stateSeg_relC8 {sf : Intake → NearSpecV3.Wasm.TTN.Store} {V : ViewImpl}
    (hV : M5T1.ResumeC.RsView V) (hVst : V.stD = StateM5a.StateView.stD PB) (xtape : M5T1.SeC.Tp) {HoldsS joint}
    (hS : SeStep V (stSem V (A := seAirs xtape) (HoldsE := segHoldsE xtape) (HoldsS := HoldsS)
      (joint := joint)) (StatePreW V) xtape (fun w r' => r' = rOutS w.1) qOfS)
    (hB : ∀ q r r', HoldsS q r r' → HoldsSt PB q r r') :
    TmplSoundRel8C sf V (seAirs xtape) Sha384Coll .state :=
  state_sound_stRoot sf V hVst Sha384Coll id (state_engHalf hV xtape hS) hB

end LaneF.StateSE

#print axioms LaneF.StateSE.state_engHalf
#print axioms LaneF.StateSE.stateSeg_relC8
