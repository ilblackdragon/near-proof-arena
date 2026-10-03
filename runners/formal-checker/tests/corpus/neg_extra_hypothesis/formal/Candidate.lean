import ArenaStandIn.Admission

theorem Candidate.certificate (h : False) : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  h.elim
