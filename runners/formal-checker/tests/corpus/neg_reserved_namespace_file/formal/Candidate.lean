import ArenaExpected

theorem Candidate.certificate : ArenaExpected.expectedType :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
