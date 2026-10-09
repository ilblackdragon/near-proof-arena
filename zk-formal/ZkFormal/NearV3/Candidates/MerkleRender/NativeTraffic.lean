import ZkFormal.NearV3.Candidates.MerkleRender.Traffic

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen ZkFormal.NearV3.Rcpt.Candidates

theorem concrete_digests (leaves : List (List Nat)) (hn : 1≤leaves.length) :
    ∀ x∈mrkShape leaves.length,
      (ch (levelTable leaves) x.1 (2*x.2.1)).dig.length=32 ∧
      (x.2.2=true → (ch (levelTable leaves) x.1 (2*x.2.1+1)).dig.length=32) := by
  intro x hx
  obtain ⟨h1,h2,h3,h4,_⟩ := shape_rec hn hx
  simp only at h1 h2 h3 h4
  have hsz : size leaves.length x.1=(size leaves.length (x.1-1)+1)/2 := by
    obtain ⟨j,hj⟩ : ∃j,x.1=j+1 := ⟨x.1-1,by omega⟩
    rw [hj]; rfl
  simp only [ch,levelTable_get leaves (x.1-1) (by omega)]
  have hd : ∀i, i<size leaves.length (x.1-1) →
      ((levelsFromLeaves leaves (x.1-1)).getD i default).dig.length=32 := by
    intro i hi
    have hh : i<(levelsFromLeaves leaves (x.1-1)).length := by rwa [levelsFromLeaves_length]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hh]
    exact levelsFromLeaves_digest leaves _ _ (List.getElem_mem _)
  refine ⟨hd _ (by omega),fun hh => hd _ ?_⟩
  rw [hh] at h4
  simp at h4
  omega

/-- All physical bus traffic for the concrete nonempty native outcome trace.
Count/root aliases and the empty-control columns are fully accounted for. -/
theorem outcome_nonempty_traffic (os : List NearSpec.Outcome) (pub : List Fp)
    (hn1 : 1≤os.length) (hn : os.length≤4481) :
    TableTraffic MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub
      (mrkTraffic (MerklePublic.aliasPublic pub)
        (generatedView os.length (levelTable (outcomePreimages os)))) := by
  have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
  have hd := concrete_digests (outcomePreimages os) (by rwa [hl])
  rw [hl] at hd
  have ht := traffic19 os.length (levelTable (outcomePreimages os))
    (MerklePublic.aliasPublic pub) hn1 hn hd
  intro b m
  have he : os.length≠0 := by omega
  simp only [outcomeTrace,honestTrace,if_neg he,MerkleEmpty.lift_traffic,MerklePublic.count_alias]
  exact ht b m

end ZkFormal.NearV3.Candidates.MerkleRender
