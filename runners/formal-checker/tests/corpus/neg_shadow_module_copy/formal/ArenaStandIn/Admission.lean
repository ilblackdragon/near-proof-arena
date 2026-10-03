namespace ArenaStandIn
structure ChallengeParams where
  protocolVersion : Nat
  chainId : String
structure ArtifactDesc where
  verifierDigest : String
  paramsDigest : String
def AdmissionStatement (_p : ChallengeParams) (_a : ArtifactDesc) : Prop := True ∧ True ∧ True ∧ True
end ArenaStandIn
