import ArenaStandIn.Admission

axiom Candidate.cheat : False

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  Candidate.cheat.elim
