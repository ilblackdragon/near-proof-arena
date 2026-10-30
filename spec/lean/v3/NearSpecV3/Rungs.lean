import NearSpecV3.RungsDefs
import NearSpecV3.D2SubD3
import NearSpecV3.D0SubD1

/-! # Admitting the fast checkers into the rung relations (`RungsDefs.lean` has the definitions)

`checkD2` alone, and `checkD0`/`checkD0a`/`checkD1`/`checkD1a` together with `checkD2`, accept only
chunks of the corresponding rung. -/

namespace NearSpecV3

open NearSpec

/-! ## Admitting the fast checkers -/

theorem notExcluded_of_ok {r : Except String Unit} (h : r = .ok ()) : notExcluded r = true := by
  subst h; rfl

theorem checkD2_ok_of_rel {cb w : Bytes} (h : RelD2 cb w) : checkD2 cb w = .ok () := by
  unfold RelD2 acceptsD2 at h; split at h
  · assumption
  · cases h

theorem checkD1_ok_of_rel {cb w : Bytes} (h : RelD1 cb w) : checkD1 cb w = .ok () := by
  unfold RelD1 acceptsD1 at h; split at h
  · assumption
  · cases h

theorem checkD0_ok_of_rel {cb w : Bytes} (h : RelD0 cb w) : checkD0 cb w = .ok () := by
  unfold RelD0 acceptsD0 at h; split at h
  · assumption
  · cases h

/-- **`checkD2` accepts only `RelRungD2` chunks.** -/
theorem rungD2_of_checkD2 {cb w : Bytes} (h : RelD2 cb w) : RelRungD2 cb w :=
  ⟨Successor.relD2_relD3 cb w h, notExcluded_of_ok (checkD2_ok_of_rel h)⟩

/-- A `checkD1` accept is a `RelRungD1` chunk when `checkD2` accepts too. -/
theorem rungD1_of_checks {cb w : Bytes} (h1 : RelD1 cb w) (h2 : RelD2 cb w) : RelRungD1 cb w :=
  ⟨(rungD2_of_checkD2 h2).1, notExcluded_of_ok (checkD1_ok_of_rel h1), (rungD2_of_checkD2 h2).2⟩

theorem rungD0_of_checks {cb w : Bytes} (h0 : RelD0 cb w) (h2 : RelD2 cb w) : RelRungD0 cb w :=
  ⟨(rungD1_of_checks (relD0_relD1 cb w h0) h2).1, notExcluded_of_ok (checkD0_ok_of_rel h0),
    (rungD1_of_checks (relD0_relD1 cb w h0) h2).2⟩

theorem rungD1a_of_checks {B : Nat} {cb w : Bytes} {W Dp N : Nat} (h1 : RelD1a B cb w W Dp N)
    (h2 : RelD2 cb w) : RelRungD1a B cb w W Dp N :=
  ⟨(rungD1_of_checks (relD1a_relD1 h1) h2).1,
    notExcluded_of_ok ((relD1a_iff B cb w W Dp N).1 h1),
    (rungD1_of_checks (relD1a_relD1 h1) h2).2⟩

theorem rungD0a_of_checks {B : Nat} {cb w : Bytes} {W Dp : Nat} (h0 : RelD0a B cb w W Dp)
    (h2 : RelD2 cb w) : RelRungD0a B cb w W Dp :=
  ⟨(rungD0_of_checks (relD0a_relD0 h0) h2).1,
    notExcluded_of_ok ((relD0a_iff B cb w W Dp).1 h0),
    (rungD0_of_checks (relD0a_relD0 h0) h2).2⟩

end NearSpecV3
