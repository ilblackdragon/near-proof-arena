import ArenaStandIn.Admission

partial def Candidate.spin (n : Nat) : Nat := Candidate.spin (n + 1)
#eval Candidate.spin 0

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
