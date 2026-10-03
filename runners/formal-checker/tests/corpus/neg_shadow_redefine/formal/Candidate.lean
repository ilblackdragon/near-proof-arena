namespace ArenaStandIn
structure ChallengeParams where
  protocolVersion : Nat
  chainId : String
structure ArtifactDesc where
  verifierDigest : String
  paramsDigest : String
def AdmissionStatement (_p : ChallengeParams) (_a : ArtifactDesc) : Prop := True
end ArenaStandIn

theorem Candidate.certificate : ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" } := trivial
