import ZkFormal.NearV3.Assembly.ResolutionAddresses

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
/-- Full native source path plus the mismatching extension child resolution chain. -/
def extendedAddresses : Nat → Nat → Nat → PTrie → List Nat → List OccurrenceAddress
  | n,v,d,.ext k c m,key =>
      ⟨n,v,d,.ext k c m⟩ ::
        if isPrefix k key then extendedAddresses (n+1) v (d+1) c (key.drop k.length) else resolutionAddresses (n+1) v (d+1) c
  | n,v,d,.branch sv cs m,slot::key =>
      ⟨n,v,d,.branch sv cs m⟩ ::
        kidExtendedAddresses (n+1) (v+(optSlotVal sv).length) (d+1) cs slot key
  | n,v,d,t,_ => [⟨n,v,d,t⟩]
def kidExtendedAddresses : Nat → Nat → Nat → Kids → Nat → List Nat → List OccurrenceAddress
  | _,_,_,.nil,_,_ => []
  | _,_,_,.none _,0,_ => []
  | n,v,d,.some c _,0,key => extendedAddresses n v d c key
  | n,v,d,.none rest,i+1,key => kidExtendedAddresses n v d rest i key
  | n,v,d,.some c rest,i+1,key =>
      kidExtendedAddresses (n+tsize c) (v+(valsOf c).length) d rest i key
end

mutual
theorem extendedAddresses_view {ns tau} : ∀ n v d t key,
    ViewSegment ns tau n v d t → ∀ a∈extendedAddresses n v d t key,
      ViewSegment ns tau a.nid a.vid a.depth a.tree
  | n,v,d,.hash h,key,hs,a,ha => by simp only [extendedAddresses,List.mem_singleton] at ha; subst a; exact hs
  | n,v,d,.leaf k s m,key,hs,a,ha => by simp only [extendedAddresses,List.mem_singleton] at ha; subst a; exact hs
  | n,v,d,.ext k c m,key,hs,a,ha => by
    simp only [extendedAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hs
    · split at ha
      · exact extendedAddresses_view _ _ _ _ _ hs.ext a ha
      · exact resolutionAddresses_view _ _ _ _ hs.ext a ha
  | n,v,d,.branch sv cs m,[],hs,a,ha => by simp only [extendedAddresses,List.mem_singleton] at ha; subst a; exact hs
  | n,v,d,.branch sv cs m,slot::key,hs,a,ha => by
    simp only [extendedAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hs
    · exact kidExtendedAddresses_view _ _ _ _ _ _ hs.branch a ha
theorem kidExtendedAddresses_view {ns tau} : ∀ n v d cs slot key,
    KidViewSegment ns tau n v d cs → ∀ a∈kidExtendedAddresses n v d cs slot key,
      ViewSegment ns tau a.nid a.vid a.depth a.tree
  | _,_,_,.nil,_,_,_,_,h => by simp [kidExtendedAddresses] at h
  | _,_,_,.none _,0,_,_,_,h => by simp [kidExtendedAddresses] at h
  | n,v,d,.some c _,0,key,hs,a,ha => extendedAddresses_view n v d c key hs.child a ha
  | n,v,d,.none rest,i+1,key,hs,a,ha => kidExtendedAddresses_view n v d rest i key hs.none a ha
  | n,v,d,.some c rest,i+1,key,hs,a,ha =>
      kidExtendedAddresses_view (n+tsize c) (v+(valsOf c).length) d rest i key hs.rest a ha
end

mutual
theorem extendedAddresses_size : ∀ n v d t key a, a∈extendedAddresses n v d t key →
    tsize a.tree ≤ tsize t
  | n,v,d,.hash h,key,a,ha => by simp only [extendedAddresses,List.mem_singleton] at ha; subst a; exact Nat.le_refl _
  | n,v,d,.leaf k s m,key,a,ha => by simp only [extendedAddresses,List.mem_singleton] at ha; subst a; exact Nat.le_refl _
  | n,v,d,.ext k c m,key,a,ha => by
    simp only [extendedAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_refl _
    · split at ha
      · have hh := extendedAddresses_size _ _ _ _ _ a ha
        simp only [tsize,occs,List.length_cons]
        exact Nat.le_succ_of_le hh
      · exact Nat.le_succ_of_le (resolutionAddresses_size _ _ _ _ a ha)
  | n,v,d,.branch sv cs m,[],a,ha => by simp only [extendedAddresses,List.mem_singleton] at ha; subst a; exact Nat.le_refl _
  | n,v,d,.branch sv cs m,slot::key,a,ha => by
    simp only [extendedAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_refl _
    · have hh := kidExtendedAddresses_size _ _ _ _ _ _ a ha
      simp only [tsize,occs,List.length_cons]
      exact Nat.le_succ_of_le hh
theorem kidExtendedAddresses_size : ∀ n v d cs slot key a, a∈kidExtendedAddresses n v d cs slot key →
    tsize a.tree ≤ ksize cs
  | _,_,_,.nil,_,_,_,h => by simp [kidExtendedAddresses] at h
  | _,_,_,.none _,0,_,_,h => by simp [kidExtendedAddresses] at h
  | n,v,d,.some c rest,0,key,a,ha => by
    have hh := extendedAddresses_size n v d c key a ha
    simp only [ksize,kOccs,List.length_append]
    exact Nat.le_trans hh (Nat.le_add_right _ _)
  | n,v,d,.none rest,i+1,key,a,ha => kidExtendedAddresses_size n v d rest i key a ha
  | n,v,d,.some c rest,i+1,key,a,ha => by
    have hh := kidExtendedAddresses_size (n+tsize c) (v+(valsOf c).length) d rest i key a ha
    simp only [ksize,kOccs,List.length_append]
    exact Nat.le_trans hh (Nat.le_add_left _ _)
end

mutual
theorem extendedAddresses_decreasing : ∀ n v d t key,
    (extendedAddresses n v d t key).Pairwise (fun a b => tsize b.tree < tsize a.tree)
  | _,_,_,.hash _,_ => by simp [extendedAddresses]
  | _,_,_,.leaf ..,_ => by simp [extendedAddresses]
  | n,v,d,.ext k c m,key => by
    simp only [extendedAddresses]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_,extendedAddresses_decreasing _ _ _ _ _⟩
      intro a ha
      have hh := extendedAddresses_size _ _ _ _ _ a ha
      simp only [tsize,occs,List.length_cons]
      exact Nat.lt_succ_of_le hh
    · exact List.pairwise_cons.mpr ⟨fun a ha => Nat.lt_succ_of_le (resolutionAddresses_size _ _ _ _ a ha), resolutionAddresses_decreasing _ _ _ _⟩
  | _,_,_,.branch ..,[] => by simp [extendedAddresses]
  | n,v,d,.branch sv cs m,slot::key => by
    apply List.pairwise_cons.mpr
    refine ⟨?_,kidExtendedAddresses_decreasing _ _ _ _ _ _⟩
    intro a ha
    have hh := kidExtendedAddresses_size _ _ _ _ _ _ a ha
    simp only [tsize,occs,List.length_cons]
    exact Nat.lt_succ_of_le hh
theorem kidExtendedAddresses_decreasing : ∀ n v d cs slot key,
    (kidExtendedAddresses n v d cs slot key).Pairwise (fun a b => tsize b.tree < tsize a.tree)
  | _,_,_,.nil,_,_ => by simp [kidExtendedAddresses]
  | _,_,_,.none _,0,_ => by simp [kidExtendedAddresses]
  | n,v,d,.some c _,0,key => extendedAddresses_decreasing n v d c key
  | n,v,d,.none rest,i+1,key => kidExtendedAddresses_decreasing n v d rest i key
  | n,v,d,.some c rest,i+1,key =>
      kidExtendedAddresses_decreasing (n+tsize c) (v+(valsOf c).length) d rest i key
end

theorem extendedAddresses_ids (n v d : Nat) (t : PTrie) (key : List Nat)
    {a : OccurrenceAddress} (ha : a∈extendedAddresses n v d t key) :
    pathRecordId (extendedAddresses n v d t key) a.tree=a.nid := by
  apply pathRecordId_member _ ha
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map]
  exact (extendedAddresses_decreasing n v d t key).imp (fun h he => by omega)

end ZkFormal.NearV3.Assembly
