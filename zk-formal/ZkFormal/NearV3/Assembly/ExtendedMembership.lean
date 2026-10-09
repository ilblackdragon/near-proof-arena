import ZkFormal.NearV3.Assembly.ExtendedAddresses

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
theorem sourceAddresses_extended : ∀ n v d t key a,
    a∈sourceAddresses n v d t key → a∈extendedAddresses n v d t key
  | n,v,d,.hash h,key,a,ha
  | n,v,d,.leaf _ _ _,key,a,ha
  | n,v,d,.branch _ _ _,[],a,ha => ha
  | n,v,d,.ext k c m,key,a,ha => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact List.mem_cons_self
    · split at ha
      · rename_i hp
        simp only [extendedAddresses,hp,ite_true,List.mem_cons]
        exact Or.inr (sourceAddresses_extended _ _ _ _ _ a ha)
      · simp at ha
  | n,v,d,.branch sv cs m,slot::key,a,ha => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (kidSourceAddresses_extended _ _ _ _ _ _ a ha)
theorem kidSourceAddresses_extended : ∀ n v d cs slot key a,
    a∈kidSourceAddresses n v d cs slot key → a∈kidExtendedAddresses n v d cs slot key
  | _,_,_,.nil,_,_,_,h => by simp [kidSourceAddresses] at h
  | _,_,_,.none _,0,_,_,h => by simp [kidSourceAddresses] at h
  | n,v,d,.some c _,0,key,a,ha => sourceAddresses_extended n v d c key a ha
  | n,v,d,.none rest,i+1,key,a,ha => kidSourceAddresses_extended n v d rest i key a ha
  | n,v,d,.some c rest,i+1,key,a,ha =>
      kidSourceAddresses_extended (n+tsize c) (v+(valsOf c).length) d rest i key a ha
end

theorem extendedAddresses_resolved : ∀ n v d t key,
    resolveAddress n v d t ∈ extendedAddresses n v d t key
  | n,v,d,.ext [] c m,key => by
    simp only [extendedAddresses,isPrefix,ite_true,resolveAddress,List.drop_zero,List.mem_cons]
    exact Or.inr (extendedAddresses_resolved _ _ _ _ _)
  | n,v,d,.hash h,key
  | n,v,d,.leaf _ _ _,key
  | n,v,d,.ext (_::_) _ _,key
  | n,v,d,.branch _ _ _,key => by cases key <;> simp [extendedAddresses,resolveAddress]

mutual
/-- Every source extension has its resolved child in the extended local map,
including the mismatching terminal extension whose child is not traversed. -/
theorem sourceExtension_extended : ∀ n v d t key a,
    a∈sourceAddresses n v d t key → ∀ k c m,a.tree=.ext k c m →
    resolveAddress (a.nid+1) a.vid (a.depth+1) c ∈ extendedAddresses n v d t key
  | n,v,d,.hash h,key,a,ha,k,c,m,he
  | n,v,d,.leaf _ _ _,key,a,ha,k,c,m,he
  | n,v,d,.branch _ _ _,[],a,ha,k,c,m,he => by
    simp only [sourceAddresses,List.mem_singleton] at ha
    subst a
    cases he
  | n,v,d,.ext key0 child mem,key,a,ha,k,c,m,he => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · cases he
      simp only [extendedAddresses,List.mem_cons]
      apply Or.inr
      split
      · exact extendedAddresses_resolved _ _ _ _ _
      · exact resolutionAddresses_resolved _ _ _ _
    · split at ha
      · rename_i hp
        simp only [extendedAddresses,hp,ite_true,List.mem_cons]
        exact Or.inr (sourceExtension_extended _ _ _ _ _ a ha k c m he)
      · simp at ha
  | n,v,d,.branch sv cs mem,slot::key,a,ha,k,c,m,he => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · cases he
    · exact List.mem_cons_of_mem _ (kidSourceExtension_extended _ _ _ _ _ _ a ha k c m he)
theorem kidSourceExtension_extended : ∀ n v d cs slot key a,
    a∈kidSourceAddresses n v d cs slot key → ∀ k c m,a.tree=.ext k c m →
    resolveAddress (a.nid+1) a.vid (a.depth+1) c ∈ kidExtendedAddresses n v d cs slot key
  | _,_,_,.nil,_,_,_,h,_,_,_,_ => by simp [kidSourceAddresses] at h
  | _,_,_,.none _,0,_,_,h,_,_,_,_ => by simp [kidSourceAddresses] at h
  | n,v,d,.some child _,0,key,a,ha,k,c,m,he => sourceExtension_extended n v d child key a ha k c m he
  | n,v,d,.none rest,i+1,key,a,ha,k,c,m,he => kidSourceExtension_extended n v d rest i key a ha k c m he
  | n,v,d,.some child rest,i+1,key,a,ha,k,c,m,he =>
      kidSourceExtension_extended (n+tsize child) (v+(valsOf child).length) d rest i key a ha k c m he
end

end ZkFormal.NearV3.Assembly
