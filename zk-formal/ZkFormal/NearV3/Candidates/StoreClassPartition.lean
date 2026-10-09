import ZkFormal.NearV3.Candidates.ChainMetadata
namespace ZkFormal.NearV3.Candidates.StoreClassPartition
open ZkFormal.Near StoreDuplicateMetadata HonestStoreRepresentatives

def members (rs : List Occurrence) (key : Key) : List Occurrence :=
  rs.filter fun r=>r.key==key

def keys (rs : List Occurrence) : List Key := representatives (rs.map Occurrence.key)

def grouped (rs : List Occurrence) : List Occurrence := (keys rs).flatMap (members rs)

private theorem partition (ks : List Key) (rs : List Occurrence)
    (hn : ks.Nodup) (hc : ∀r∈rs,r.key∈ks) :
    (ks.flatMap (members rs)).Perm rs := by
  induction ks generalizing rs with
  | nil =>
    have hr : rs=[] := by
      cases rs with
      | nil => rfl
      | cons r rs => have :=hc r (by simp);simp at this
    simp [hr]
  | cons k ks ih =>
    have hn':=List.nodup_cons.mp hn
    let rest:=rs.filter fun r=>!(r.key==k)
    have hh : (ks.flatMap (members rest)).Perm rest := by
      apply ih rest hn'.2
      intro r hr
      have hm:=List.mem_filter.mp hr
      have hk : r.key≠k := by simpa using hm.2
      exact (List.mem_cons.mp (hc r hm.1)).resolve_left hk
    have he : ks.flatMap (members rest)=ks.flatMap (members rs) := by
      change (ks.map (members rest)).flatten=(ks.map (members rs)).flatten
      apply congrArg List.flatten
      apply List.map_congr_left
      intro key hk
      unfold members rest
      rw [List.filter_filter]
      apply List.filter_congr
      intro r _
      have hne : key≠k := by intro h;subst key;exact hn'.1 hk
      by_cases hr : r.key=key
      · simp [hr,hne]
      · simp [hr]
    rw [he] at hh
    simp only [List.flatMap_cons]
    exact ((List.Perm.refl (members rs k)).append hh).trans
      (List.filter_append_perm (fun r : Occurrence=>r.key==k) rs)

/-- All occurrences appear exactly once when grouped by actual native byte
classes; order may change, entity IDs and multiplicities cannot disappear. -/
theorem grouped_perm (rs : List Occurrence) : (grouped rs).Perm rs :=
  partition (keys rs) rs (distinct _) (fun r hr=>
    (covers _ _).mpr (List.mem_map.mpr ⟨r,hr,rfl⟩))

theorem group_nonempty (rs : List Occurrence) (key : Key) (hk : key∈keys rs) :
    members rs key≠[] := by
  obtain ⟨r,hr,hkey⟩:=List.mem_map.mp ((covers _ _).mp hk)
  intro he
  have hm : r∈members rs key := List.mem_filter.mpr ⟨hr,by simp [hkey]⟩
  rw [he] at hm
  simp at hm

def chain (rs : List Occurrence) : List StoreDuplicateChain.Entry :=
  (keys rs).flatMap fun key=>StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)

theorem chain_ids (rs : List Occurrence) :
    (chain rs).map StoreDuplicateChain.Entry.eid=(grouped rs).map Occurrence.eid := by
  simp [chain,grouped,List.map_flatMap,StoreDuplicateChain.entity_ids]

theorem chain_unique (rs : List Occurrence) (hn : (rs.map Occurrence.eid).Nodup) :
    ((chain rs).map StoreDuplicateChain.Entry.eid).Nodup := by
  rw [chain_ids]
  exact ((grouped_perm rs).map Occurrence.eid).nodup_iff.mpr hn

theorem chain_canonical (rs : List Occurrence)
    (hi : ∀r∈rs,r.eid<ZkFormal.Algebra.P) :
    ∀r∈chain rs,r.repE<ZkFormal.Algebra.P := by
  intro r hr
  obtain ⟨key,_,hr⟩:=List.mem_flatMap.mp hr
  apply ChainMetadata.chain_small _ _ r hr
  intro i hi'
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hi'
  exact hi r (List.mem_filter.mp hr).1
theorem chain_coverage (rs : List Occurrence) (r : Occurrence) (hr : r∈rs) :
    ∃e∈chain rs,e.eid=r.eid := by
  apply List.mem_map.mp
  rw [chain_ids]
  exact ((grouped_perm rs).map Occurrence.eid).mem_iff.mpr (List.mem_map.mpr ⟨r,hr,rfl⟩)

/-- Every nonempty class contributes exactly one full byte-and-prefix charge. -/
theorem total_charge (rs : List Occurrence) :
    ((keys rs).map fun key=>
      ((StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)).filter
        fun e=>!e.dup).length*(key.2.length+4)).sum=charge (keys rs) := by
  unfold charge
  congr 1
  apply List.map_congr_left
  intro key hk
  rw [StoreDuplicateChain.nondup_count]
  have hn:=group_nonempty rs key hk
  have hi : ((members rs key).map Occurrence.eid).isEmpty=false := by
    cases he : members rs key with
    | nil => exact False.elim (hn he)
    | cons r rest => rfl
  simp [hi]

/-- ENT balance composes over the complete partition, including zero-length
value classes. The payload function will be instantiated by physical records. -/
theorem total_ent (rs : List Occurrence) (payload : Key→List ZkFormal.Near.Msg) :
    ((keys rs).flatMap fun key=>StoreDuplicateChain.sends
      (StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)) (payload key))=
    ((keys rs).flatMap fun key=>StoreDuplicateChain.recvs
      (StoreDuplicateChain.entries ((members rs key).map Occurrence.eid)) (payload key)) := by
  change ((keys rs).map _).flatten=((keys rs).map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro key _
  exact StoreDuplicateChain.ent_balance _ _

/-- Actual combined records supply uniqueness and predecessor field bounds;
no arbitrary metadata coverage or canonicality premise remains. -/
theorem combined_metadata (vs : List ZkFormal.NearV3.NodeS3)
    (tau : ZkFormal.NearV3.ValE→Nat) (es : List ZkFormal.NearV3.ValE)
    (hn : ZkFormal.NearV3.NodeWf3 vs) (hv : ZkFormal.NearV3.ValWf es) :
    let rs:=CombinedStoreOccurrences.allOccurrences vs tau es
    ((chain rs).map StoreDuplicateChain.Entry.eid).Nodup ∧
    (∀r∈chain rs,r.repE<ZkFormal.Algebra.P) ∧
    (∀r∈rs,∃e∈chain rs,e.eid=r.eid) := by
  exact ⟨chain_unique _ (StoreSelectedClasses.combined_ids vs tau es hv),
    chain_canonical _ (StoreOccurrenceIds.entity_ids_small vs tau es hn hv),
    chain_coverage _⟩

/-- The concrete partition and chain constructor produces locally valid
count-extended node/value tables from the original renderer inputs. -/
theorem combined_local (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : Render.NodeOk vs) (hv : ValWf es) (t : Nat) (pub : List ZkFormal.Algebra.Fp) :
    let cs:=chain (CombinedStoreOccurrences.allOccurrences vs tau es)
    TableLocal Rcpt.Candidates.SizeCount.nodeTable
      (TrieCountHeight.node (ChainMetadata.assign cs 0 vs) pub) t pub ∧
    TableLocal Rcpt.Candidates.SizeCount.valTable
      (TrieCountHeight.value (ChainMetadata.assignValues cs es) pub) t pub := by
  exact ChainMetadata.complete _ vs es hn hv (combined_metadata vs tau es hn.wf hv).2.1 t pub

end ZkFormal.NearV3.Candidates.StoreClassPartition
