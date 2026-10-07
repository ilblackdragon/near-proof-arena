import ZkFormal.NearV3.Assembly.BranchRecordId

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
theorem sourceContexts_known : ∀ n v d t key,
    t.find key≠none → ∀ ctx∈sourceContexts n v d t key,
      ctx.address.tree.find ctx.key≠none
  | n,v,d,.hash h,key,hknown,ctx,hc
  | n,v,d,.leaf _ _ _,key,hknown,ctx,hc
  | n,v,d,.branch _ _ _,[],hknown,ctx,hc => by
    simp only [sourceContexts,List.mem_singleton] at hc
    subst ctx
    exact hknown
  | n,v,d,.ext k c m,key,hknown,ctx,hc => by
    simp only [sourceContexts,List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hknown
    · split at hc
      · rename_i hp
        have hchild : c.find (key.drop k.length)≠none := by simpa [PTrie.find,hp] using hknown
        exact sourceContexts_known _ _ _ _ _ hchild ctx hc
      · simp at hc
  | n,v,d,.branch sv cs m,slot::key,hknown,ctx,hc => by
    simp only [sourceContexts,List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hknown
    · exact kidSourceContexts_known _ _ _ _ _ _ hknown ctx hc
theorem kidSourceContexts_known : ∀ n v d cs slot key,
    Kids.find cs slot key≠none → ∀ ctx∈kidSourceContexts n v d cs slot key,
      ctx.address.tree.find ctx.key≠none
  | _,_,_,.nil,_,_,_,_,h => by simp [kidSourceContexts] at h
  | _,_,_,.none _,0,_,_,_,h => by simp [kidSourceContexts] at h
  | n,v,d,.some c _,0,key,hknown,ctx,hc => sourceContexts_known n v d c key hknown ctx hc
  | n,v,d,.none rest,i+1,key,hknown,ctx,hc => kidSourceContexts_known n v d rest i key hknown ctx hc
  | n,v,d,.some c rest,i+1,key,hknown,ctx,hc =>
    kidSourceContexts_known (n+tsize c) (v+(valsOf c).length) d rest i key hknown ctx hc
end

theorem sourceAddress_known {n v d t key a} (hk : t.find key≠none)
    (ha : a∈sourceAddresses n v d t key) : ∃ rest,a.tree.find rest≠none := by
  rw [←sourceContexts_addresses] at ha
  obtain ⟨ctx,hc,he⟩ := List.mem_map.mp ha
  exact ⟨ctx.key,he ▸ sourceContexts_known n v d t key hk ctx hc⟩

theorem nativePathNodes_known {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hk : t.find key≠none) :
    ∀ node∈nativePathNodes run,∃ rest,node.find rest≠none := by
  intro node hn
  simp only [nativePathNodes,List.mem_append,List.mem_map,List.mem_singleton] at hn
  rcases hn with ⟨p,hp,rfl⟩ | rfl
  · have hp' : p∈run.parts := by
      have := List.mem_reverse.mp hp
      exact (List.mem_filter.mp this).1
    obtain ⟨a,ha,he⟩ := (traceUpsert_source_addresses hr 0 0 0).2 p hp'
    obtain ⟨rest,hrest⟩ := sourceAddress_known hk ha
    exact ⟨rest,he ▸ hrest⟩
  · obtain ⟨a,ha,he⟩ := (traceUpsert_source_addresses hr 0 0 0).1
    obtain ⟨rest,hrest⟩ := sourceAddress_known hk ha
    exact ⟨rest,he ▸ hrest⟩

/-- A proper ancestor's child resolves to an actual known source-path node,
unlike the mismatching terminal extension's off-path child. -/
theorem properChild_resolved_node {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hk : t.find key≠none) {i : Nat} {p : TreePart}
    (hp : (properPath run)[i]?=some p) {child : PTrie} (hc : sourcePathChild p=some child) :
    isNode (resolveNative child)=true := by
  have hl := traceUpsert_pathChain t key value run hr i p hp
  simp only [hc,Option.map_some] at hl
  obtain ⟨rest,hrest⟩ := nativePathNodes_known hr hk _ (List.mem_of_getElem? hl.symm)
  cases he : resolveNative child <;> simp_all [isNode,PTrie.find]

end ZkFormal.NearV3.Assembly
