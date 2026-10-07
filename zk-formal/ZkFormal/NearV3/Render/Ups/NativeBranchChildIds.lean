import ZkFormal.NearV3.Assembly.BranchRecordId

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near Assembly

/-- Source-byte authentication needs the immediate child occurrence ID, before
empty-extension resolution. The actual residual key disambiguates equal siblings. -/
theorem traceUpsert_branch_childId {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (n vid d : Nat) {p : TreePart}
    (hp : p∈run.parts) (hkind : p.kind=.RDB) {sv kids mem} (hsrc : p.source=.branch sv kids mem) :
    ∃ ctx∈sourceContexts n vid d t key,
      ctx.address.tree=p.source ∧
      pathRecordId (extendedAddresses n vid d t key) p.source=ctx.address.nid ∧
      ∀ child,nativeChildAt kids p.slot=some child →
        pathRecordId (extendedAddresses n vid d t key) child=
          seedChildId (ctx.address.nid+1) kids p.slot := by
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
  exact hid.trans (locateKid_nid _ _ _ _ _ _ hca)
end ZkFormal.NearV3.Render.UpsGen
