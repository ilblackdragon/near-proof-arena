import ArenaStandIn.Admission

def Candidate.myStmt : Prop := ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" }

theorem Candidate.certificate : Candidate.myStmt :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
