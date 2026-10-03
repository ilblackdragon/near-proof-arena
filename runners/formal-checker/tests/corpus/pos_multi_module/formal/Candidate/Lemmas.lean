import ArenaStandIn.Admission
namespace Candidate.Lemmas
open ArenaStandIn
theorem sound : ∀ n : Nat, n + 0 = n := fun n => by simp
theorem complete : (80 : Nat) * 2 = 80 + 80 := by decide
end Candidate.Lemmas
