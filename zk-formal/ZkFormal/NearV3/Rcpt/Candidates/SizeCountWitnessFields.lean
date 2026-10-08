import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNativePaid

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Near NearSpec NearSpecV3 Assembly

/-- Existing head coverage supplies the constructor's exact root width; a
missing-head default is not silently treated as a valid hash. -/
theorem witness_post_length (x : ExtV3) (hw : HeadWf x.heads) (tau : Nat)
    (hc : ∃ h∈x.heads,h.tau=tau) : (x.post tau).length=32 := by
  have he : (x.heads.find? fun h => h.tau==tau).isSome := by
    apply List.find?_isSome.mpr
    obtain ⟨h,hh,ht⟩ := hc
    exact ⟨h,hh,by simp [ht]⟩
  cases hf : x.heads.find? (fun h => h.tau==tau) with
  | none => simp [hf] at he
  | some h =>
    have hh := (hw.len h (List.mem_of_find?_eq_some hf)).2
    simp only [ExtV3.post,hf,Option.map_some,Option.getD_some,Link3.toB,List.length_map,hh]

theorem witness_transition_lengths (k : WalkD0) (x : ExtV3) (hw : HeadWf x.heads)
    (hc : ∀ tau,tau≤k.implicitBlks.length → ∃ h∈x.heads,h.tau=tau) :
    ∀ t∈transitions (stateWitnessOfV3 k x),
      t.blockHash.length=32 ∧ t.postStateRoot.length=32 := by
  intro t ht
  simp only [transitions,stateWitnessOfV3,List.mem_cons] at ht
  rcases ht with rfl | ht
  · exact ⟨by simp [ExtV3.transition],witness_post_length x hw 0 (hc 0 (by omega))⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    have hi : p.2<k.implicitBlks.length := by
      have hm : p.2∈k.implicitBlks.zipIdx.map Prod.snd := List.mem_map.mpr ⟨p,hp,rfl⟩
      simpa [List.zipIdx_map_snd,List.range_eq_range'] using hm
    exact ⟨by simp [ExtV3.transition],witness_post_length x hw (p.2+1) (hc _ (by omega))⟩

theorem witness_applied_hash_length (k : WalkD0) (x : ExtV3) :
    (stateWitnessOfV3 k x).appliedReceiptsHash.length=32 := by
  simp only [stateWitnessOfV3,ArenaCore.sha256_length]

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
