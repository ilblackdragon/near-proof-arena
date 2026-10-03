import Candidate.Lemmas
import ArenaStandIn.Admission

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨Candidate.Lemmas.sound, Candidate.Lemmas.complete, Nat.zero_le _, rfl⟩
