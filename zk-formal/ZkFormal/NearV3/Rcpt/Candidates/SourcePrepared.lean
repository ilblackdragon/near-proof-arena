import ZkFormal.NearV3.Rcpt.Candidates.SourceCoverage
import ZkFormal.NearV3.Rcpt.Candidates.DedupPublicViews

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Candidate-only native preparation adds the equal-key metadata check needed
for proof reuse. Its completeness follows from the unchanged D0a relation. -/
def prepSourceD0 (cb : Bytes) (hint : Hint) : Except String Prep := do
  let p ← prepD0 cb hint
  if sourceMetadataConsistent p.lists then return p else throw "invalid: inconsistent source metadata"

theorem prepSourceD0_sound {cb : Bytes} {hint : Hint} {p : Prep}
    (h : prepSourceD0 cb hint=.ok p) :
    prepD0 cb hint=.ok p ∧ sourceMetadataConsistent p.lists=true := by
  unfold prepSourceD0 at h
  cases hp : prepD0 cb hint with
  | error err =>
    rw [hp] at h
    change (Except.error err : Except String Prep)=.ok p at h
    cases h
  | ok out =>
    rw [hp] at h
    change (if sourceMetadataConsistent out.lists then Except.ok out else
      Except.error "invalid: inconsistent source metadata")=Except.ok p at h
    split at h
    · rename_i hm
      cases h
      exact ⟨rfl, hm⟩
    · cases h

theorem prepSourceD0_complete {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p) :
    prepSourceD0 cb hint=.ok p := by
  have hm := relD0a_prepared_metadata h hp
  unfold prepSourceD0
  rw [hp]
  change (if sourceMetadataConsistent p.lists then Except.ok p else
    Except.error "invalid: inconsistent source metadata")=Except.ok p
  rw [hm]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates
