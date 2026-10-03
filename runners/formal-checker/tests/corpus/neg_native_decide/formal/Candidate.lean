import ArenaStandIn.Admission

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } := by
  refine ⟨fun _ => rfl, ?_, Nat.zero_le _, rfl⟩
  show (80 : Nat) * 2 = 80 + 80
  native_decide
