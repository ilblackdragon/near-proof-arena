import ZkFormal.NearV3.Rcpt.Candidates.PreparedVerified
import ZkFormal.NearV3.Rcpt.Link.RelSources
import ZkFormal.NearV3.Assembly.PreparedSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- The proposed native equal-key root/from-shard check never rejects an existing
D0a-valid witness for a successfully prepared claim. It adds no domain assumption. -/
theorem relD0a_prepared_metadata {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p) :
    sourceMetadataConsistent p.lists = true := by
  obtain ⟨k, w, hk, _, hv, _⟩ := relD0a_sources_verified h
  exact preparedSourceLists_metadata_consistent w.entries k.H.shardId k.sourceBlks hv
    (Assembly.prepD0_source_lists hp hk)

/-- Same completeness fact for the claim-only prepared record. -/
theorem relD0a_prepared_claim_metadata {budget : Nat} {cb wb : Bytes} {pc : PrepC}
    (h : RelD0a budget cb wb) (hp : prepClaim cb = .ok pc) :
    sourceMetadataConsistent pc.lists = true := by
  obtain ⟨k, w, hk, _, hv, _⟩ := relD0a_sources_verified h
  exact preparedSourceLists_metadata_consistent w.entries k.H.shardId k.sourceBlks hv
    (Assembly.prepClaim_source_lists hp hk)

end ZkFormal.NearV3.Rcpt.Candidates
