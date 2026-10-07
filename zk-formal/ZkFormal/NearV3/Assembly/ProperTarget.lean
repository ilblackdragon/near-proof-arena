import ZkFormal.NearV3.Assembly.ContextKnown
import ZkFormal.NearV3.Render.Ups.SeedProperEdges
import ZkFormal.NearV3.Render.Ups.NativePathIds

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen UpsRows

/-- Actual successful branch descent binds the legacy native resolver to the
same selected occurrence target. Known reads exclude an unrevealed endpoint. -/
theorem proper_branch_target {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hk : t.find key≠none) (n vid d : Nat)
    {i : Nat} {p : TreePart} (hp : (properPath run)[i]?=some p)
    (hkind : p.kind=.RDB) {sv kids mem} (hsrc : p.source=.branch sv kids mem) :
    SeedProperTarget (pathRecordId (extendedAddresses n vid d t key) p.source)
      (resolvedRecordId (pathRecordId (extendedAddresses n vid d t key))) p := by
  have hpm := (properPath_mem hp).1
  obtain ⟨ctx,hctx,htree,rest,hkey⟩ := traceUpsert_branch_covered _ _ _ _ hr n vid d p hpm hkind
  have ha : ctx.address∈sourceAddresses n vid d t key := by
    rw [←sourceContexts_addresses]
    exact List.mem_map.mpr ⟨ctx,hctx,rfl⟩
  have hsource : pathRecordId (extendedAddresses n vid d t key) p.source=ctx.address.nid :=
    htree ▸ extendedRecordId_source ha
  simp only [SeedProperTarget,hsrc]
  intro child hc
  have hl := locateKid_tree (ctx.address.depth+1) (ctx.address.nid+1)
    (ctx.address.vid+(optSlotVal sv).length) kids p.slot
  rw [hc,Option.map_eq_some_iff] at hl
  obtain ⟨ca,hca,hct⟩ := hl
  have hmem := context_branch_target n vid d t key ctx hctx sv kids mem p.slot rest ca
    (htree.trans hsrc) hkey hca
  have hid := extendedAddresses_ids n vid d t key hmem
  simp only [resolveAddress_tree,hct] at hid
  have hn := properChild_resolved_node hr hk hp (child:=child) (by simp [sourcePathChild,hsrc,hc])
  have htarget := resolveAddress_target ca.nid ca.vid ca.depth ca.tree (by simpa [hct] using hn)
  rw [hsrc] at hsource
  rw [hct] at htarget
  unfold resolvedRecordId
  rw [hid,hsource,htarget,locateKid_nid _ _ _ _ _ _ hca]

/-- All proper native ancestors satisfy the concrete selected-child agreement
needed by the physical prefix-provider theorem. No ID agreement is an input. -/
theorem traceUpsert_seedProperTarget {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hk : t.find key≠none) (n vid d : Nat)
    {i : Nat} {p : TreePart} (hp : (properPath run)[i]?=some p) :
    SeedProperTarget (pathRecordId (extendedAddresses n vid d t key) p.source)
      (resolvedRecordId (pathRecordId (extendedAddresses n vid d t key))) p := by
  have hpm := properPath_mem hp
  have hs := traceUpsert_properSources t key value run hr p hpm.1
  have hd := hpm.2
  cases hkind : p.kind <;> simp only [hkind,descendKind] at hd
  all_goals try contradiction
  · obtain ⟨sv,kids,mem,child,cm,hsrc,_,_⟩ := (show ∃ sv kids mem child cm,
      p.source=.branch sv kids mem ∧ nativeChildAt kids p.slot=some child ∧ child.mem?=some cm by
        simpa only [ProperSource,hkind] using hs)
    exact proper_branch_target hr hk n vid d hp hkind hsrc
  · obtain ⟨ek,child,mem,cm,hsrc,_,_⟩ := (show ∃ ek child mem cm,
      p.source=.ext ek child mem ∧ ek≠[] ∧ child.mem?=some cm by
        simpa only [ProperSource,hkind] using hs)
    obtain ⟨a,ha,he⟩ := (traceUpsert_source_addresses hr n vid d).2 p hpm.1
    have hid : pathRecordId (extendedAddresses n vid d t key) p.source=a.nid :=
      he ▸ extendedRecordId_source ha
    have hn := properChild_resolved_node hr hk hp (child:=child) (by simp [sourcePathChild,hsrc])
    rw [hsrc] at hid
    simpa only [SeedProperTarget,hsrc,hid] using extendedRecordId_ext_target ha (he.trans hsrc) hn

theorem traceUpsert_seedProperTargets {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hk : t.find key≠none) (n vid d : Nat) :
    ∀ p∈properPath run,
      SeedProperTarget (pathRecordId (extendedAddresses n vid d t key) p.source)
        (resolvedRecordId (pathRecordId (extendedAddresses n vid d t key))) p := by
  intro p hp
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
  exact traceUpsert_seedProperTarget hr hk n vid d (List.getElem?_eq_some_iff.mpr ⟨hi,he⟩)

end ZkFormal.NearV3.Assembly
