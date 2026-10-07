import ZkFormal.NearV3.Assembly.OccurrenceResolvedId

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

structure SourceContext where
  address : OccurrenceAddress
  key : List Nat

mutual
def sourceContexts : Nat → Nat → Nat → PTrie → List Nat → List SourceContext
  | n,v,d,.ext k c m,key => ⟨⟨n,v,d,.ext k c m⟩,key⟩ ::
      if isPrefix k key then sourceContexts (n+1) v (d+1) c (key.drop k.length) else []
  | n,v,d,.branch sv cs m,slot::key => ⟨⟨n,v,d,.branch sv cs m⟩,slot::key⟩ ::
      kidSourceContexts (n+1) (v+(optSlotVal sv).length) (d+1) cs slot key
  | n,v,d,t,key => [⟨⟨n,v,d,t⟩,key⟩]
def kidSourceContexts : Nat → Nat → Nat → Kids → Nat → List Nat → List SourceContext
  | _,_,_,.nil,_,_ => []
  | _,_,_,.none _,0,_ => []
  | n,v,d,.some c _,0,key => sourceContexts n v d c key
  | n,v,d,.none rest,i+1,key => kidSourceContexts n v d rest i key
  | n,v,d,.some c rest,i+1,key => kidSourceContexts (n+tsize c) (v+(valsOf c).length) d rest i key
end

mutual
theorem sourceContexts_addresses : ∀ n v d t key,
    (sourceContexts n v d t key).map SourceContext.address=sourceAddresses n v d t key
  | _,_,_,.hash _,_ => rfl
  | _,_,_,.leaf ..,_ => rfl
  | n,v,d,.ext k c m,key => by
    simp only [sourceContexts,sourceAddresses,List.map_cons]
    split
    · rw [sourceContexts_addresses]
    · rfl
  | _,_,_,.branch ..,[] => rfl
  | n,v,d,.branch sv cs m,slot::key => by
    simp only [sourceContexts,sourceAddresses,List.map_cons]
    rw [kidSourceContexts_addresses]
theorem kidSourceContexts_addresses : ∀ n v d cs slot key,
    (kidSourceContexts n v d cs slot key).map SourceContext.address=kidSourceAddresses n v d cs slot key
  | _,_,_,.nil,_,_ => rfl
  | _,_,_,.none _,0,_ => rfl
  | n,v,d,.some c _,0,key => sourceContexts_addresses n v d c key
  | n,v,d,.none rest,i+1,key => kidSourceContexts_addresses n v d rest i key
  | n,v,d,.some c rest,i+1,key => kidSourceContexts_addresses (n+tsize c) (v+(valsOf c).length) d rest i key
end

theorem locateKid_extended_resolved : ∀ n v d cs slot key child,
    locateKid d n v cs slot=some child →
    resolveAddress child.nid child.vid child.depth child.tree ∈ kidExtendedAddresses n v d cs slot key
  | _,_,_,.nil,_,_,_,h => by simp [locateKid] at h
  | _,_,_,.none _,0,_,_,h => by simp [locateKid] at h
  | n,v,d,.some c _,0,key,child,h => by
    cases h
    exact extendedAddresses_resolved n v d c key
  | n,v,d,.none rest,i+1,key,child,h => locateKid_extended_resolved n v d rest i key child h
  | n,v,d,.some c rest,i+1,key,child,h =>
    locateKid_extended_resolved (n+tsize c) (v+(valsOf c).length) d rest i key child h

mutual
/-- The native residual key selects the actual occurrence among possibly equal
siblings; this retains both the selected child nid and its value offset. -/
theorem context_branch_target : ∀ n v d t key ctx,
    ctx∈sourceContexts n v d t key → ∀ sv cs m slot rest child,
    ctx.address.tree=.branch sv cs m → ctx.key=slot::rest →
    locateKid (ctx.address.depth+1) (ctx.address.nid+1)
      (ctx.address.vid+(optSlotVal sv).length) cs slot=some child →
    resolveAddress child.nid child.vid child.depth child.tree∈extendedAddresses n v d t key
  | n,v,d,.hash h,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl
  | n,v,d,.leaf _ _ _,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl => by
    simp only [sourceContexts,List.mem_singleton] at hc
    subst ctx
    cases ht
  | n,v,d,.ext k c mem,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl => by
    simp only [sourceContexts,List.mem_cons] at hc
    rcases hc with rfl | hc
    · cases ht
    · split at hc
      · rename_i hp
        simp only [extendedAddresses,hp,ite_true,List.mem_cons]
        exact Or.inr (context_branch_target _ _ _ _ _ ctx hc sv cs m slot rest child ht hk hl)
      · simp at hc
  | n,v,d,.branch value kids mem,[],ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl => by
    simp only [sourceContexts,List.mem_singleton] at hc
    subst ctx
    cases hk
  | n,v,d,.branch value kids mem,s::ks,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl => by
    simp only [sourceContexts,List.mem_cons] at hc
    rcases hc with rfl | hc
    · cases ht
      cases hk
      exact List.mem_cons_of_mem _ (locateKid_extended_resolved _ _ _ _ _ _ child hl)
    · exact List.mem_cons_of_mem _ (kidContext_branch_target _ _ _ _ _ _ ctx hc sv cs m slot rest child ht hk hl)
theorem kidContext_branch_target : ∀ n v d kids i key ctx,
    ctx∈kidSourceContexts n v d kids i key → ∀ sv cs m slot rest child,
    ctx.address.tree=.branch sv cs m → ctx.key=slot::rest →
    locateKid (ctx.address.depth+1) (ctx.address.nid+1)
      (ctx.address.vid+(optSlotVal sv).length) cs slot=some child →
    resolveAddress child.nid child.vid child.depth child.tree∈kidExtendedAddresses n v d kids i key
  | _,_,_,.nil,_,_,_,h,_,_,_,_,_,_,_,_,_ => by simp [kidSourceContexts] at h
  | _,_,_,.none _,0,_,_,h,_,_,_,_,_,_,_,_,_ => by simp [kidSourceContexts] at h
  | n,v,d,.some c _,0,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl =>
    context_branch_target n v d c key ctx hc sv cs m slot rest child ht hk hl
  | n,v,d,.none r,i+1,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl =>
    kidContext_branch_target n v d r i key ctx hc sv cs m slot rest child ht hk hl
  | n,v,d,.some c r,i+1,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl =>
    kidContext_branch_target (n+tsize c) (v+(valsOf c).length) d r i key ctx hc sv cs m slot rest child ht hk hl
end

end ZkFormal.NearV3.Assembly
