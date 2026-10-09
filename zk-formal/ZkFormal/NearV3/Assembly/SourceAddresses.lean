import ZkFormal.NearV3.Assembly.PathView
import ZkFormal.NearV3.Assembly.PathRecordId

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
/-- Full native write-key path, retaining empty extensions for PT source IDs. -/
def sourceAddresses : Nat → Nat → Nat → PTrie → List Nat → List OccurrenceAddress
  | n,v,d,.ext k c m,key =>
      ⟨n,v,d,.ext k c m⟩ ::
        if isPrefix k key then sourceAddresses (n+1) v (d+1) c (key.drop k.length) else []
  | n,v,d,.branch sv cs m,slot::key =>
      ⟨n,v,d,.branch sv cs m⟩ ::
        kidSourceAddresses (n+1) (v+(optSlotVal sv).length) (d+1) cs slot key
  | n,v,d,t,_ => [⟨n,v,d,t⟩]
def kidSourceAddresses : Nat → Nat → Nat → Kids → Nat → List Nat → List OccurrenceAddress
  | _,_,_,.nil,_,_ => []
  | _,_,_,.none _,0,_ => []
  | n,v,d,.some c _,0,key => sourceAddresses n v d c key
  | n,v,d,.none rest,i+1,key => kidSourceAddresses n v d rest i key
  | n,v,d,.some c rest,i+1,key =>
      kidSourceAddresses (n+tsize c) (v+(valsOf c).length) d rest i key
end

mutual
theorem sourceAddresses_view {ns tau} : ∀ n v d t key,
    ViewSegment ns tau n v d t → ∀ a∈sourceAddresses n v d t key,
      ViewSegment ns tau a.nid a.vid a.depth a.tree
  | n,v,d,.hash h,key,hs,a,ha => by simp only [sourceAddresses,List.mem_singleton] at ha; subst a; exact hs
  | n,v,d,.leaf k s m,key,hs,a,ha => by simp only [sourceAddresses,List.mem_singleton] at ha; subst a; exact hs
  | n,v,d,.ext k c m,key,hs,a,ha => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hs
    · split at ha
      · exact sourceAddresses_view _ _ _ _ _ hs.ext a ha
      · simp at ha
  | n,v,d,.branch sv cs m,[],hs,a,ha => by simp only [sourceAddresses,List.mem_singleton] at ha; subst a; exact hs
  | n,v,d,.branch sv cs m,slot::key,hs,a,ha => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hs
    · exact kidSourceAddresses_view _ _ _ _ _ _ hs.branch a ha
theorem kidSourceAddresses_view {ns tau} : ∀ n v d cs slot key,
    KidViewSegment ns tau n v d cs → ∀ a∈kidSourceAddresses n v d cs slot key,
      ViewSegment ns tau a.nid a.vid a.depth a.tree
  | _,_,_,.nil,_,_,_,_,h => by simp [kidSourceAddresses] at h
  | _,_,_,.none _,0,_,_,_,h => by simp [kidSourceAddresses] at h
  | n,v,d,.some c _,0,key,hs,a,ha => sourceAddresses_view n v d c key hs.child a ha
  | n,v,d,.none rest,i+1,key,hs,a,ha => kidSourceAddresses_view n v d rest i key hs.none a ha
  | n,v,d,.some c rest,i+1,key,hs,a,ha =>
      kidSourceAddresses_view (n+tsize c) (v+(valsOf c).length) d rest i key hs.rest a ha
end

mutual
theorem sourceAddresses_size : ∀ n v d t key a, a∈sourceAddresses n v d t key →
    tsize a.tree ≤ tsize t
  | n,v,d,.hash h,key,a,ha => by simp only [sourceAddresses,List.mem_singleton] at ha; subst a; exact Nat.le_refl _
  | n,v,d,.leaf k s m,key,a,ha => by simp only [sourceAddresses,List.mem_singleton] at ha; subst a; exact Nat.le_refl _
  | n,v,d,.ext k c m,key,a,ha => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_refl _
    · split at ha
      · have hh := sourceAddresses_size _ _ _ _ _ a ha
        simp only [tsize,occs,List.length_cons]
        exact Nat.le_succ_of_le hh
      · simp at ha
  | n,v,d,.branch sv cs m,[],a,ha => by simp only [sourceAddresses,List.mem_singleton] at ha; subst a; exact Nat.le_refl _
  | n,v,d,.branch sv cs m,slot::key,a,ha => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_refl _
    · have hh := kidSourceAddresses_size _ _ _ _ _ _ a ha
      simp only [tsize,occs,List.length_cons]
      exact Nat.le_succ_of_le hh
theorem kidSourceAddresses_size : ∀ n v d cs slot key a, a∈kidSourceAddresses n v d cs slot key →
    tsize a.tree ≤ ksize cs
  | _,_,_,.nil,_,_,_,h => by simp [kidSourceAddresses] at h
  | _,_,_,.none _,0,_,_,h => by simp [kidSourceAddresses] at h
  | n,v,d,.some c rest,0,key,a,ha => by
    have hh := sourceAddresses_size n v d c key a ha
    simp only [ksize,kOccs,List.length_append]
    exact Nat.le_trans hh (Nat.le_add_right _ _)
  | n,v,d,.none rest,i+1,key,a,ha => kidSourceAddresses_size n v d rest i key a ha
  | n,v,d,.some c rest,i+1,key,a,ha => by
    have hh := kidSourceAddresses_size (n+tsize c) (v+(valsOf c).length) d rest i key a ha
    simp only [ksize,kOccs,List.length_append]
    exact Nat.le_trans hh (Nat.le_add_left _ _)
end

mutual
theorem sourceAddresses_decreasing : ∀ n v d t key,
    (sourceAddresses n v d t key).Pairwise (fun a b => tsize b.tree < tsize a.tree)
  | _,_,_,.hash _,_ => by simp [sourceAddresses]
  | _,_,_,.leaf ..,_ => by simp [sourceAddresses]
  | n,v,d,.ext k c m,key => by
    simp only [sourceAddresses]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_,sourceAddresses_decreasing _ _ _ _ _⟩
      intro a ha
      have hh := sourceAddresses_size _ _ _ _ _ a ha
      simp only [tsize,occs,List.length_cons]
      exact Nat.lt_succ_of_le hh
    · simp
  | _,_,_,.branch ..,[] => by simp [sourceAddresses]
  | n,v,d,.branch sv cs m,slot::key => by
    apply List.pairwise_cons.mpr
    refine ⟨?_,kidSourceAddresses_decreasing _ _ _ _ _ _⟩
    intro a ha
    have hh := kidSourceAddresses_size _ _ _ _ _ _ a ha
    simp only [tsize,occs,List.length_cons]
    exact Nat.lt_succ_of_le hh
theorem kidSourceAddresses_decreasing : ∀ n v d cs slot key,
    (kidSourceAddresses n v d cs slot key).Pairwise (fun a b => tsize b.tree < tsize a.tree)
  | _,_,_,.nil,_,_ => by simp [kidSourceAddresses]
  | _,_,_,.none _,0,_ => by simp [kidSourceAddresses]
  | n,v,d,.some c _,0,key => sourceAddresses_decreasing n v d c key
  | n,v,d,.none rest,i+1,key => kidSourceAddresses_decreasing n v d rest i key
  | n,v,d,.some c rest,i+1,key =>
      kidSourceAddresses_decreasing (n+tsize c) (v+(valsOf c).length) d rest i key
end

theorem sourceAddresses_ids (n v d : Nat) (t : PTrie) (key : List Nat)
    {a : OccurrenceAddress} (ha : a∈sourceAddresses n v d t key) :
    pathRecordId (sourceAddresses n v d t key) a.tree=a.nid := by
  apply pathRecordId_member _ ha
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map]
  exact (sourceAddresses_decreasing n v d t key).imp (fun h he => by omega)

end ZkFormal.NearV3.Assembly
