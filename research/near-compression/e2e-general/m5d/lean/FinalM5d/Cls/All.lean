import FinalM5d.Cls.C4_1_3
import FinalM5d.Cls.C4_2_8
import FinalM5d.Cls.C4_5_16
import FinalM5d.Cls.C4_33_100
import FinalM5d.Cls.C5_1_3
import FinalM5d.Cls.C5_2_8
import FinalM5d.Cls.C5_5_16
import FinalM5d.Cls.C5_33_100
import FinalM5d.Cls.C6_5_16
import FinalM5d.Final

/-! The generated FINAL classes (`gen_class.py`). The F1 copy is `finalAir` itself. -/

namespace FinalM5d.Cls

open ZkFormal.Air

/-- The FINAL AIR, its layouts and generator constants of class `(NS, d, t)`, if generated. -/
def byClass : Nat → Nat → Nat → Option (Air × List (String × Layout) × List (String × String))
  | 4, 1, 3 => some (FinalM5d.C4_1_3.finalAir, FinalM5d.C4_1_3.finalLayouts, FinalM5d.C4_1_3.finalConsts)
  | 4, 2, 8 => some (FinalM5d.C4_2_8.finalAir, FinalM5d.C4_2_8.finalLayouts, FinalM5d.C4_2_8.finalConsts)
  | 4, 5, 16 => some (FinalM5d.C4_5_16.finalAir, FinalM5d.C4_5_16.finalLayouts, FinalM5d.C4_5_16.finalConsts)
  | 4, 33, 100 => some (FinalM5d.C4_33_100.finalAir, FinalM5d.C4_33_100.finalLayouts, FinalM5d.C4_33_100.finalConsts)
  | 5, 1, 3 => some (FinalM5d.C5_1_3.finalAir, FinalM5d.C5_1_3.finalLayouts, FinalM5d.C5_1_3.finalConsts)
  | 5, 2, 8 => some (FinalM5d.C5_2_8.finalAir, FinalM5d.C5_2_8.finalLayouts, FinalM5d.C5_2_8.finalConsts)
  | 5, 5, 16 => some (FinalM5d.C5_5_16.finalAir, FinalM5d.C5_5_16.finalLayouts, FinalM5d.C5_5_16.finalConsts)
  | 5, 33, 100 => some (FinalM5d.C5_33_100.finalAir, FinalM5d.C5_33_100.finalLayouts, FinalM5d.C5_33_100.finalConsts)
  | 6, 5, 16 => some (FinalM5d.C6_5_16.finalAir, FinalM5d.C6_5_16.finalLayouts, FinalM5d.C6_5_16.finalConsts)
  | _, _, _ => none

theorem f1_eq : FinalM5d.C6_5_16.finalAir = FinalM5d.finalAir := rfl

end FinalM5d.Cls
