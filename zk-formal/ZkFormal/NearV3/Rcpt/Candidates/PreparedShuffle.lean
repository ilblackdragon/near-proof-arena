import ZkFormal.NearV3.Rcpt.Candidates.PreparedCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

/-- Successful preparation certifies shuffle fuel for every source block. -/
theorem preparedSourceLists_shuffle {blocks : List Blk} {out : List SrcList}
    (h : preparedSourceLists blocks=.ok out) :
    ∀ B∈blocks,∃ shuffled,shuffleWithSeed (slotDescriptors B B.slots) B.hdr.prevHash=some shuffled := by
  apply forIn_all_yield (fun B => ∃ shuffled,shuffleWithSeed (slotDescriptors B B.slots) B.hdr.prevHash=some shuffled) _ ?_ blocks [] out h
  intro B acc step hs
  obtain ⟨srcs,hsrc,hs⟩ := bind_ok hs
  rw [slotSources_eq] at hsrc
  have he := Except.ok.inj hsrc
  subst srcs
  split at hs
  · rename_i shuffled hsh
    obtain ⟨_,he,hs⟩ := bind_ok hs
    cases he
    cases hs
    exact ⟨⟨_,rfl⟩,⟨shuffled,hsh⟩⟩
  · obtain ⟨_,he,_⟩ := bind_ok hs
    cases he

/-- Dictionary lookup commutes with the same shuffle. Native shuffle success
therefore follows from preparation and authenticated slot selection, independently
of receipt contents and of repeated-key multiplicity. -/
theorem prepD0_selected_shuffle {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k)
    (entries : List ProofEntry) (own : Nat)
    (hv : ∀ B∈k.sourceBlks,∀ x∈B.slots,SourceSlotValid entries own B x) :
    ∀ B∈k.sourceBlks,∃ shuffled,shuffleWithSeed (selectedProofs entries B B.slots) B.hdr.prevHash=some shuffled := by
  intro B hB
  obtain ⟨shuffled,hsh⟩ := preparedSourceLists_shuffle (Assembly.prepD0_source_lists hp hw) B hB
  refine ⟨shuffled.map (sourceEntry entries),?_⟩
  rw [←slotDescriptors_selected entries own B B.slots (hv B hB),shuffleWithSeed_map,hsh]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates
