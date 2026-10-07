import ZkFormal.NearV3.Assembly.ExtendedMembership
import ZkFormal.NearV3.Assembly.SourceCoverage

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- Extending the lookup domain preserves every original source occurrence ID. -/
theorem extendedRecordId_source {n v d t key a}
    (ha : a∈sourceAddresses n v d t key) :
    pathRecordId (extendedAddresses n v d t key) a.tree=a.nid :=
  extendedAddresses_ids n v d t key (sourceAddresses_extended n v d t key a ha)

/-- The off-path terminal extension child gets exactly the actual seeded target,
including an arbitrary empty-extension chain. -/
theorem extendedRecordId_ext_target {n v d t key a}
    (ha : a∈sourceAddresses n v d t key) {k c m} (he : a.tree=.ext k c m)
    (hn : isNode (resolveNative c)=true) :
    resolvedRecordId (pathRecordId (extendedAddresses n v d t key)) c=viewTarget (a.nid+1) c := by
  have hc := sourceExtension_extended n v d t key a ha k c m he
  have hid := extendedAddresses_ids n v d t key hc
  simp only [resolveAddress_tree] at hid
  exact hid.trans (resolveAddress_target _ _ _ _ hn)

/-- All actual native source parts keep exact providers under the extended map. -/
theorem forest_traceUpsert_extended_provider {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree key value=some run) {p : TreePart} (hp : p∈run.parts) :
    ∃ a∈sourceAddresses root.nid root.vid root.depth root.tree key,
      a.tree=p.source ∧
      pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree key) p.source=a.nid ∧
      (forestStoreViews ts).nodes[a.nid]?=some (seedNodeView tau a.depth a.nid a.vid p.source) := by
  obtain ⟨a,ha,he,_,hview⟩ := forest_traceUpsert_source_provider hroot hr hp
  exact ⟨a,ha,he,he ▸ extendedRecordId_source ha,hview⟩

/-- Target providers are existing forest occurrences; extending the address map
allocates no new NodeS3 records and requires no extra byte-budget premise. -/
theorem forest_extended_target_provider {ts : List PTrie} {tau : Nat} {root a : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {key : List Nat}
    (ha : a∈sourceAddresses root.nid root.vid root.depth root.tree key)
    {k c m} (he : a.tree=.ext k c m) (hn : isNode (resolveNative c)=true) :
    let target := resolveAddress (a.nid+1) a.vid (a.depth+1) c
    (forestStoreViews ts).nodes[target.nid]?=
      some (seedNodeView tau target.depth target.nid target.vid (resolveNative c)) := by
  have hs := forestRootAt_view (ns:=forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hroot
  have hc := sourceExtension_extended _ _ _ _ _ a ha k c m he
  have hv := extendedAddresses_view _ _ _ _ _ hs _ hc
  have hnode : isNode (resolveAddress (a.nid+1) a.vid (a.depth+1) c).tree=true := by
    rwa [resolveAddress_tree]
  simpa only [forestStoreViews,Nat.zero_add,resolveAddress_tree] using hv.get hnode

end ZkFormal.NearV3.Assembly
