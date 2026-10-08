import ZkFormal.NearV3.Rcpt.Candidates.SizeCountWitnessFields
import ZkFormal.NearV3.Link.Chain3

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Near NearSpec NearSpecV3 Assembly Sched

/-- Successful native claim decoding fixes the epoch hash width, independently
of witness acceptance or any reconstructed witness size bound. -/
theorem decoded_claim_epoch_length {cb : Bytes} {c : Claim}
    (h : decodeClaimE cb=.ok c) : c.epochId.length=32 := by
  unfold decodeClaimE at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    exact V3.pHash_len (by assumption)

set_option maxHeartbeats 4000000 in
/-- The actual claim walk retains that decoded epoch field. -/
theorem walk_claim_epoch_length {cb : Bytes} {k : WalkD0}
    (h : walkD0 cb=.ok k) : k.c.epochId.length=32 := by
  unfold walkD0 at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    apply decoded_claim_epoch_length
    assumption

/-- ROOT-chain coverage is already exact for every prepared transition index. -/
theorem prepared_head_coverage {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    {hs : List HeadE} {ups : List UpsE} {r0 rK : List Nat}
    (hchain : RootChain hs ups p.hdr.K r0 rK) :
    ∀ tau,tau≤k.implicitBlks.length → ∃ h∈hs,h.tau=tau := by
  intro tau ht
  rw [←prepD0_implicit_count hp hk] at ht
  exact ⟨headAt hs tau,hchain.head_mem tau ht⟩

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
