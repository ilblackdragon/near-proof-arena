import ZkFormal.NearV3.Render.Ups.ForestTerminalSafe
import ZkFormal.NearV3.Render.Ups.NativePrefixResolution
import ZkFormal.NearV3.Render.Ups.SeedProperEdges

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly

theorem seed_terminal_prefix_edge (n tau depth vid : Nat)
    {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hf : root.find key≠none)
    (i : Nat) (hi : i<run.matched) :
    [n,i,run.terminalKey.getD i 0,n,i+1,EK_KEY]∈edgesOf3 n
      (seedNodeView tau depth n vid run.terminalSource) := by
  have hp := traceUpsert_terminalPrefix root key v run hr
  rw [terminalPrefix_symbol hp i hi]
  rcases traceUpsert_terminalNodeShape hr hf with ⟨key,slot,mem,hs⟩|⟨key,child,mem,hs,hm⟩|hm
  · have hb : run.matched≤key.length := by simpa only [hs,nativeNodeKey] using hp.1
    simpa only [hs,nativeNodeKey] using seed_leaf_key tau depth n vid i key slot mem (by omega)
  · rw [hs]
    exact ext_inner_edge n i _ key _ _ rfl (by omega)
  · omega

/-- Native traversal edges are supplied by actual global occurrence nodes. Only
selected ancestor child-ID agreement remains; terminal-prefix providers are constructed. -/
theorem forest_prefix_provider {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (ht : ∀ p∈run.parts, descendKind p.kind=true →
      let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
      SeedProperTarget (recordId p.source) (resolvedRecordId recordId) p)
    (e : List Nat)
    (he : e∈nativePrefixEdges
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run) :
    ∃ n s, (forestStoreViews ts).nodes[n]?=some s ∧ e∈edgesOf3 n s := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  change e∈ancestorWalkEdges recordId run++terminalWalkEdges recordId run at he
  rcases List.mem_append.mp he with he|he
  · obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have hp' : p∈run.parts.filter (fun q=>descendKind q.kind) := List.mem_reverse.mp hp
    obtain ⟨hmem,hd⟩ := List.mem_filter.mp hp'
    obtain ⟨a,ha,hs,hid,hget⟩ := forest_traceUpsert_extended_provider hroot hr hmem
    have hi' : i<(partWalkKey p).length := List.mem_range.mp hi
    have hprovider := seed_proper_edge recordId (resolvedRecordId recordId) hr p hmem hd i hi'
      tau a.depth a.vid (ht p hmem hd)
    have hid' : recordId p.source=a.nid := hid
    exact ⟨a.nid,_,hget,by simpa only [hid'] using hprovider⟩
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    obtain ⟨a,ha,hs,_,hget⟩ := forest_terminal_seed hroot hr hf
    have hid : recordId run.terminalSource=a.nid := hs ▸ extendedRecordId_source ha
    refine ⟨a.nid,_,hget,?_⟩
    rw [hid]
    exact seed_terminal_prefix_edge a.nid tau a.depth a.vid hr hf i (List.mem_range.mp hi)

/-- Every physical pre-terminal row, including under the safe terminal resolver,
uses an existing global node provider once selected ancestor offsets are identified. -/
theorem forest_physical_prefix_provider {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (ht : ∀ p∈run.parts, descendKind p.kind=true →
      let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
      SeedProperTarget (recordId p.source) (resolvedRecordId recordId) p)
    (valueId : Slot→Nat) (resolvedId : PTrie→Nat) (baseI : UpsInst) (Qs : List UpsPartI)
    (t : Nat) (hrow : 1≤t ∧ t<run.splitCursor [0,15]) :
    let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root.tree run value)
      root.tree run value Qs
    ∃ n s, (forestStoreViews ts).nodes[n]?=some s ∧ (step I t).e∈edgesOf3 n s := by
  dsimp only
  apply forest_prefix_provider hroot hr hf ht
  rw [nativePrefixEdges_physical_resolved _ valueId resolvedId baseI hr hf Qs]
  apply List.mem_map.mpr
  refine ⟨t-1,List.mem_range.mpr (show t-1<run.splitCursor [0,15]-1 by omega),?_⟩
  rw [Nat.sub_add_cancel hrow.1]
end ZkFormal.NearV3.Render.UpsGen
