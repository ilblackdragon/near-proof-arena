import ZkFormal.NearV3.Assembly.SourceAddresses

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- The address chain skipped by empty-extension resolution, including its
final target even when it is an unrevealed hash. -/
def resolutionAddresses : Nat → Nat → Nat → PTrie → List OccurrenceAddress
  | n,v,d,.ext [] c m => ⟨n,v,d,.ext [] c m⟩::resolutionAddresses (n+1) v (d+1) c
  | n,v,d,t => [⟨n,v,d,t⟩]

theorem resolutionAddresses_view {ns tau} : ∀ n v d t,
    ViewSegment ns tau n v d t → ∀ a∈resolutionAddresses n v d t,
      ViewSegment ns tau a.nid a.vid a.depth a.tree
  | n,v,d,.ext [] c m,hs,a,ha => by
    simp only [resolutionAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hs
    · exact resolutionAddresses_view _ _ _ _ hs.ext a ha
  | n,v,d,.hash h,hs,a,ha
  | n,v,d,.leaf _ _ _,hs,a,ha
  | n,v,d,.ext (_::_) _ _,hs,a,ha
  | n,v,d,.branch _ _ _,hs,a,ha => by
    simp only [resolutionAddresses,List.mem_singleton] at ha
    subst a
    exact hs

theorem resolutionAddresses_size : ∀ n v d t a, a∈resolutionAddresses n v d t →
    tsize a.tree ≤ tsize t
  | n,v,d,.ext [] c m,a,ha => by
    simp only [resolutionAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (resolutionAddresses_size _ _ _ _ a ha)
  | n,v,d,.hash h,a,ha
  | n,v,d,.leaf _ _ _,a,ha
  | n,v,d,.ext (_::_) _ _,a,ha
  | n,v,d,.branch _ _ _,a,ha => by
    simp only [resolutionAddresses,List.mem_singleton] at ha
    subst a
    exact Nat.le_refl _

theorem resolutionAddresses_decreasing : ∀ n v d t,
    (resolutionAddresses n v d t).Pairwise (fun a b => tsize b.tree<tsize a.tree)
  | n,v,d,.ext [] c m => by
    apply List.pairwise_cons.mpr
    exact ⟨fun a ha => Nat.lt_succ_of_le (resolutionAddresses_size _ _ _ _ a ha),
      resolutionAddresses_decreasing _ _ _ _⟩
  | n,v,d,.hash h
  | n,v,d,.leaf _ _ _
  | n,v,d,.ext (_::_) _ _
  | n,v,d,.branch _ _ _ => by simp [resolutionAddresses]

theorem resolutionAddresses_resolved : ∀ n v d t,
    resolveAddress n v d t ∈ resolutionAddresses n v d t
  | n,v,d,.ext [] c m => by
    exact List.mem_cons_of_mem _ (resolutionAddresses_resolved _ _ _ _)
  | n,v,d,.hash h
  | n,v,d,.leaf _ _ _
  | n,v,d,.ext (_::_) _ _
  | n,v,d,.branch _ _ _ => by simp [resolveAddress,resolutionAddresses]

end ZkFormal.NearV3.Assembly
