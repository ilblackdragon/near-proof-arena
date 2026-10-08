import ZkFormal.NearV3.Candidates.NativePackedAllocation

namespace ZkFormal.NearV3.Candidates.AcceptedSourceShaContract
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.DedupCompile

/-- All allocator prerequisites for the actual prepared source job family,
including the original occurrence/duplicate accounting, follow from acceptance. -/
theorem accepted {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w) :
    let source:=sourceShaMessages p.lists w.entries
    (Sha.Gen.honestRows source).length≤8932712 ∧
    (∀M∈source,(Sha.Gen.msgRows M).length≤35) ∧
    (∀M∈source,∀b∈M.bytes,b<256) := by
  have hrel:=(relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,_,hs⟩:=relD0a_inputs hrel hp hf hr
  obtain ⟨he,hm⟩:=sourceWeights_exact hr p.lists hs
  have hb:=(relD0a_work_bounds hrel hp hf hr).2.1
  refine ⟨?_,?_,sourceShaMessages_bytes p.lists w.entries⟩
  · rw [←upsertShaWeights_sum,sourceShaMessages_weights,he]
    exact hb
  · intro M hM
    apply hm (Sha.Gen.msgRows M).length
    rw [←sourceShaMessages_weights]
    exact List.mem_map.mpr ⟨M,hM,rfl⟩

end ZkFormal.NearV3.Candidates.AcceptedSourceShaContract
