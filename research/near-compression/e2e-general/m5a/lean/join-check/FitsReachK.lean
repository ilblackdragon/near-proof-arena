
/-! B-T1 item 1 (lane B): appended to lane E's `join/StViewE.lean` by `join-check/run.sh` (that file
is not in a lake library). Lane E's `FitsReachK κ R` is lane B's `FitsReach stViewE κ R` by `rfl`,
so lane E's `fitsReachK_engine` discharges lane B's `FitsReach` for the engine. -/
namespace LaneE.StViewEJoin
open NearSpecV3.E2E NearSpecV3.E2E.Bnd StateM5a.StateViewParams
theorem fitsReachK_eq (κ : Intake → List NearSpec.Bytes) (R : Intake → EConf → Prop) :
    FitsReachK κ R = FitsReach stViewE κ R := rfl
theorem fitsReach_engine (κ : Intake → List NearSpec.Bytes) [OvlVal.VmWritesShort] :
    FitsReach stViewE κ (RK κ) :=
  fitsReachK_engine κ
end LaneE.StViewEJoin
#print axioms LaneE.StViewEJoin.fitsReachK_eq
#print axioms LaneE.StViewEJoin.fitsReach_engine
