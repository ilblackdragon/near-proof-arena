import ArenaStandIn.Admission

partial def Candidate.loop (n : Nat) : Nat := Candidate.loop (n + 1)

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  have _h : Candidate.loop 0 = Candidate.loop 0 := rfl
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
