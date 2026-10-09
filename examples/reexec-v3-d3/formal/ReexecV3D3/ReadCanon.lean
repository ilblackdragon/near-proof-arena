import ReexecV3D3.ReadCanonDefs
import ReexecV3D3.Logged.API

namespace ReexecV3D3.Read

open NearSpec NearSpecV3 NearSpecV3.D2

/-- A successful read-set check still establishes the original frozen relation. -/
theorem check_sound {cb w : Bytes} (h : check cb w = true) :
    D3.checkD3 cb w = .ok () := by
  unfold check at h
  cases he : Logged.checkD3Reads cb w with
  | mk result keys =>
    rw [he] at h
    cases result with
    | error e => cases h
    | ok u =>
      cases u
      have hf := Logged.checkD3Reads_fst cb w
      rw [he] at hf
      exact hf.symm

/-- Acceptance requires literal equality, not merely store equivalence. -/
theorem check_normal {cb w : Bytes} (h : check cb w = true) : canonW cb w = w := by
  unfold check at h
  unfold canonW
  cases he : Logged.checkD3Reads cb w with
  | mk result keys =>
    rw [he] at h
    cases result with
    | error e => cases h
    | ok u =>
      cases u
      simpa using h

end ReexecV3D3.Read
