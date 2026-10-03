import Candidate.Bad
import ArenaStandIn.Admission

-- The certificate itself is honest and does not use `Candidate.Bad`; the
-- ill-typed declaration lives in another module, which the module-batched
-- rechecks replay in a different sandbox run.
theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
