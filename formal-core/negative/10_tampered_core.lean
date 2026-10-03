-- EXPECT: SHADOWED_DEFINITION (tampered formal-core)
-- No import of the pinned ArenaCore: the candidate ships its own module that
-- defines `ArenaCore.AdmissionStatement := True`.  Elaborated on its own
-- this file succeeds; the checker must elaborate the judge-generated wrapper
-- against the *pinned* formal-core (and refuse candidate modules in the
-- `ArenaCore`/judge namespaces), where it fails with a redeclaration error.
namespace ArenaCore
structure ChallengeParams where
structure ArtifactDescription where
def AdmissionStatement (_ : ChallengeParams) (_ : ArtifactDescription) : Prop := True
end ArenaCore
namespace Candidate
theorem certificate : ArenaCore.AdmissionStatement ⟨⟩ ⟨⟩ := trivial
end Candidate
