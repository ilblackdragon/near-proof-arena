import ArenaStandIn.Admission

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, (ArenaStandIn.Assumptions.toyCollisionResistance _ _ rfl).symm⟩
