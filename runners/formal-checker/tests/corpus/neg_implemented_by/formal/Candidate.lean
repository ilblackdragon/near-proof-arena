import ArenaStandIn.Admission

def Candidate.fastImpl (n : Nat) : Nat := n
@[implemented_by Candidate.fastImpl]
def Candidate.spec (n : Nat) : Nat := n + 0

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } :=
  ⟨fun _ => rfl, rfl, Nat.zero_le _, rfl⟩
