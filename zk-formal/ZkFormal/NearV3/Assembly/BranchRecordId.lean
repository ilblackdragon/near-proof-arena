import ZkFormal.NearV3.Assembly.BranchCoverage
import ZkFormal.NearV3.Render.Ups.SeedWalkEdges

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

theorem locateKid_extended_child : ∀ n v d cs slot key child,
    locateKid d n v cs slot=some child →
    child ∈ kidExtendedAddresses n v d cs slot key
  | _,_,_,.nil,_,_,_,h => by simp [locateKid] at h
  | _,_,_,.none _,0,_,_,h => by simp [locateKid] at h
  | n,v,d,.some c _,0,key,child,h => by
    cases h
    exact extendedAddresses_root n v d c key
  | n,v,d,.none rest,i+1,key,child,h => locateKid_extended_child n v d rest i key child h
  | n,v,d,.some c rest,i+1,key,child,h =>
    locateKid_extended_child (n+tsize c) (v+(valsOf c).length) d rest i key child h

mutual
/-- The native residual key selects the actual occurrence among possibly equal
siblings; this retains both the selected child nid and its value offset. -/
theorem context_branch_child : ∀ n v d t key ctx,
    ctx∈sourceContexts n v d t key → ∀ sv cs m slot rest child,
    ctx.address.tree=.branch sv cs m → ctx.key=slot::rest →
    locateKid (ctx.address.depth+1) (ctx.address.nid+1)
      (ctx.address.vid+(optSlotVal sv).length) cs slot=some child →
    child∈extendedAddresses n v d t key
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
        exact Or.inr (context_branch_child _ _ _ _ _ ctx hc sv cs m slot rest child ht hk hl)
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
      exact List.mem_cons_of_mem _ (locateKid_extended_child _ _ _ _ _ _ child hl)
    · exact List.mem_cons_of_mem _ (kidContext_branch_child _ _ _ _ _ _ ctx hc sv cs m slot rest child ht hk hl)
theorem kidContext_branch_child : ∀ n v d kids i key ctx,
    ctx∈kidSourceContexts n v d kids i key → ∀ sv cs m slot rest child,
    ctx.address.tree=.branch sv cs m → ctx.key=slot::rest →
    locateKid (ctx.address.depth+1) (ctx.address.nid+1)
      (ctx.address.vid+(optSlotVal sv).length) cs slot=some child →
    child∈kidExtendedAddresses n v d kids i key
  | _,_,_,.nil,_,_,_,h,_,_,_,_,_,_,_,_,_ => by simp [kidSourceContexts] at h
  | _,_,_,.none _,0,_,_,h,_,_,_,_,_,_,_,_,_ => by simp [kidSourceContexts] at h
  | n,v,d,.some c _,0,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl =>
    context_branch_child n v d c key ctx hc sv cs m slot rest child ht hk hl
  | n,v,d,.none r,i+1,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl =>
    kidContext_branch_child n v d r i key ctx hc sv cs m slot rest child ht hk hl
  | n,v,d,.some c r,i+1,key,ctx,hc,sv,cs,m,slot,rest,child,ht,hk,hl =>
    kidContext_branch_child (n+tsize c) (v+(valsOf c).length) d r i key ctx hc sv cs m slot rest child ht hk hl
end


theorem locateKid_nid : ∀ n v d cs slot child,
    locateKid d n v cs slot=some child → child.nid=seedChildId n cs slot
  | _,_,_,.nil,_,_,h => by simp [locateKid] at h
  | _,_,_,.none _,0,_,h => by simp [locateKid] at h
  | n,v,d,.some c _,0,child,h => by cases h; rfl
  | n,v,d,.none rest,i+1,child,h => locateKid_nid n v d rest i child h
  | n,v,d,.some c rest,i+1,child,h => locateKid_nid (n+tsize c) (v+(valsOf c).length) d rest i child h

/-- Actual branch tracing supplies the residual slot context, so equal siblings
cannot redirect the local ID lookup to a different occurrence. -/
theorem traceUpsert_branch_target {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (n vid d : Nat) {p : TreePart}
    (hp : p∈run.parts) (hkind : p.kind=.RDB) {sv kids mem} (hsrc : p.source=.branch sv kids mem) :
    ∃ ctx∈sourceContexts n vid d t key,
      ctx.address.tree=p.source ∧
      pathRecordId (extendedAddresses n vid d t key) p.source=ctx.address.nid ∧
      ∀ child,nativeChildAt kids p.slot=some child →
        occurrenceResolvedId (pathRecordId (extendedAddresses n vid d t key)) child=
          viewTarget (seedChildId (ctx.address.nid+1) kids p.slot) child := by
  obtain ⟨ctx,hctx,htree,rest,hkey⟩ := traceUpsert_branch_covered _ _ _ _ hr n vid d p hp hkind
  have ha : ctx.address∈sourceAddresses n vid d t key := by
    rw [←sourceContexts_addresses]
    exact List.mem_map.mpr ⟨ctx,hctx,rfl⟩
  refine ⟨ctx,hctx,htree,htree ▸ extendedRecordId_source ha,?_⟩
  intro child hc
  have hl := locateKid_tree (ctx.address.depth+1) (ctx.address.nid+1)
    (ctx.address.vid+(optSlotVal sv).length) kids p.slot
  rw [hc,Option.map_eq_some_iff] at hl
  obtain ⟨ca,hca,hct⟩ := hl
  have hmem := context_branch_child n vid d t key ctx hctx sv kids mem p.slot rest ca
    (htree.trans hsrc) hkey hca
  have hid := extendedAddresses_ids n vid d t key hmem
  rw [hct] at hid
  unfold occurrenceResolvedId
  rw [hid,locateKid_nid _ _ _ _ _ _ hca]

end ZkFormal.NearV3.Assembly
