import ZkFormal.NearV3.Assembly.PathDistinct

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- A trace-local executable lookup. Strict source-size descent makes size a
unique key within this path; no global structural trie equality is required. -/
def pathRecordId (addresses : List OccurrenceAddress) (t : PTrie) : Nat :=
  ((addresses.find? (fun a => tsize a.tree == tsize t)).map OccurrenceAddress.nid).getD 0

private theorem path_find_size : ∀ (addresses : List OccurrenceAddress),
    (addresses.map (fun a => tsize a.tree)).Nodup →
    ∀ a ∈ addresses, addresses.find? (fun b => tsize b.tree == tsize a.tree)=some a := by
  intro addresses
  induction addresses with
  | nil => simp
  | cons b bs ih =>
    intro hn a ha
    simp only [List.map_cons,List.nodup_cons] at hn
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · have hne : tsize b.tree ≠ tsize a.tree := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨a,ha,he.symm⟩)
      simpa [List.find?_cons,hne] using ih hn.2 a ha

theorem pathRecordId_member {addresses : List OccurrenceAddress}
    (hn : (addresses.map (fun a => tsize a.tree)).Nodup) {a : OccurrenceAddress}
    (ha : a ∈ addresses) : pathRecordId addresses a.tree=a.nid := by
  simp [pathRecordId,path_find_size addresses hn a ha]

/-- The current renderer's structural-map interface is coherent on this actual
trace's proper sources. It is deliberately scoped to one allocated path. -/
theorem traceUpsert_recordIds {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) {addresses : List OccurrenceAddress}
    (ht : addresses.map OccurrenceAddress.tree=nativePathNodes run) :
    (nativePathNodes run).map (pathRecordId addresses)=addresses.map OccurrenceAddress.nid := by
  have hn : (addresses.map (fun a => tsize a.tree)).Nodup := by
    have hh := congrArg (List.map tsize) ht
    simp only [List.map_map,Function.comp_def] at hh
    rw [hh]
    exact traceUpsert_path_sizes_nodup hr
  rw [←ht,List.map_map]
  exact List.map_congr_left (fun a ha => pathRecordId_member hn ha)

theorem traceUpsert_sourceLevelIds {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) {addresses : List OccurrenceAddress}
    (ht : addresses.map OccurrenceAddress.tree=nativePathNodes run) :
    sourceLevelIds (pathRecordId addresses) run=addresses.map OccurrenceAddress.nid := by
  rw [←nativePathNodes_ids]
  exact traceUpsert_recordIds hr ht

end ZkFormal.NearV3.Assembly
