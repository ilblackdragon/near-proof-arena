import ArenaStandIn.Admission

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 81, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
