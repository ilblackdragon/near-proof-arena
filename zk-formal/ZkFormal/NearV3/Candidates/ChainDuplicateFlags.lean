import ZkFormal.NearV3.Candidates.StoreClassPartition
namespace ZkFormal.NearV3.Candidates.ChainDuplicateFlags
open StoreDuplicateMetadata StoreClassPartition StoreDuplicateChain

private theorem tail_facts (prev : Nat) (ids : List Nat) (e : Entry)
    (he : e∈tailEntries prev ids) : e.dup=true ∧ e.eid∈ids := by
  induction ids generalizing prev with
  | nil => simp [tailEntries] at he
  | cons i ids ih =>
    rcases List.mem_cons.mp he with rfl|he
    · exact ⟨rfl,by simp⟩
    · obtain ⟨hd,hi⟩:=ih i he
      exact ⟨hd,by simp [hi]⟩

theorem class_dup (i : Nat) (ids : List Nat) (hn : (i::ids).Nodup)
    (e : Entry) (he : e∈entries (i::ids)) : e.dup=!(e.eid==i) := by
  rcases List.mem_cons.mp he with rfl|he
  · simp
  · obtain ⟨hd,hi⟩:=tail_facts i ids e he
    have hne : e.eid≠i := by intro h;subst i;exact (List.nodup_cons.mp hn).1 hi
    simp [hd,hne]

private theorem member_head (rs : List Occurrence) (key : HonestStoreRepresentatives.Key) :
    (members rs key).head?=rs.find? (fun r=>r.key==key) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.key=key <;> simp [members,h] at ih ⊢

theorem class_representative (rs : List Occurrence) (key : HonestStoreRepresentatives.Key)
    (r : Occurrence) (rest : List Occurrence) (he : members rs key=r::rest) :
    representativeId rs key=r.eid := by
  have hh:=member_head rs key
  rw [he] at hh
  simp only [List.head?_cons] at hh
  simp [representativeId,←hh]

/-- Chain predecessor links change repE/hd, but preserve the exact duplicate
selection predicate used by the checked native store-charge theorem. -/
theorem metadata_dup (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup)
    (r : Occurrence) (hr : r∈rs) :
    (ChainMetadata.metadata (chain rs) r.eid).dup=!(r.eid==representativeId rs r.key) := by
  have hk : r.key∈keys rs := (HonestStoreRepresentatives.covers _ _).mpr
    (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hm : r∈members rs r.key := List.mem_filter.mpr ⟨hr,by simp⟩
  have hi : r.eid∈(entries ((members rs r.key).map Occurrence.eid)).map Entry.eid := by
    rw [entity_ids]
    exact List.mem_map.mpr ⟨r,hm,rfl⟩
  obtain ⟨e,he,heid⟩:=List.mem_map.mp hi
  have hc : e∈chain rs := List.mem_flatMap.mpr ⟨r.key,hk,he⟩
  rw [←heid,ChainMetadata.metadata_exact _ (chain_unique rs hn) e hc]
  cases hg : members rs r.key with
  | nil => simp [hg] at hm
  | cons a rest =>
    have hu : ((members rs r.key).map Occurrence.eid).Nodup :=
      (List.filter_sublist (p:=fun s : Occurrence=>s.key==r.key)).map Occurrence.eid |>.nodup hn
    rw [hg] at he hu
    rw [class_representative rs r.key a rest hg]
    exact class_dup a.eid (rest.map Occurrence.eid) hu e he
end ZkFormal.NearV3.Candidates.ChainDuplicateFlags
