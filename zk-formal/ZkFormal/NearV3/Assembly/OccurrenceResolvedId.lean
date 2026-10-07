import ZkFormal.NearV3.Assembly.ExtendedRecordId

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- A map-level resolver matching actual occurrence view targets, including an
empty extension whose child remains an unrevealed hash. -/
def occurrenceResolvedId (recordId : PTrie → Nat) (t : PTrie) : Nat :=
  viewTarget (recordId t) t

theorem resolutionAddresses_root (n v d : Nat) (t : PTrie) :
    (⟨n,v,d,t⟩ : OccurrenceAddress)∈resolutionAddresses n v d t := by
  cases t with
  | ext k c m => cases k <;> simp [resolutionAddresses]
  | hash | leaf | branch => simp [resolutionAddresses]

theorem extendedAddresses_root (n v d : Nat) (t : PTrie) (key : List Nat) :
    (⟨n,v,d,t⟩ : OccurrenceAddress)∈extendedAddresses n v d t key := by
  cases t <;> cases key <;> simp [extendedAddresses]

mutual
/-- Every source extension has its resolved child in the extended local map,
including the mismatching terminal extension whose child is not traversed. -/
theorem sourceExtension_child_extended : ∀ n v d t key a,
    a∈sourceAddresses n v d t key → ∀ k c m,a.tree=.ext k c m →
    (⟨a.nid+1,a.vid,a.depth+1,c⟩ : OccurrenceAddress) ∈ extendedAddresses n v d t key
  | n,v,d,.hash h,key,a,ha,k,c,m,he
  | n,v,d,.leaf _ _ _,key,a,ha,k,c,m,he
  | n,v,d,.branch _ _ _,[],a,ha,k,c,m,he => by
    simp only [sourceAddresses,List.mem_singleton] at ha
    subst a
    cases he
  | n,v,d,.ext key0 child mem,key,a,ha,k,c,m,he => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · cases he
      simp only [extendedAddresses,List.mem_cons]
      apply Or.inr
      split
      · exact extendedAddresses_root _ _ _ _ _
      · exact resolutionAddresses_root _ _ _ _
    · split at ha
      · rename_i hp
        simp only [extendedAddresses,hp,ite_true,List.mem_cons]
        exact Or.inr (sourceExtension_child_extended _ _ _ _ _ a ha k c m he)
      · simp at ha
  | n,v,d,.branch sv cs mem,slot::key,a,ha,k,c,m,he => by
    simp only [sourceAddresses,List.mem_cons] at ha
    rcases ha with rfl | ha
    · cases he
    · exact List.mem_cons_of_mem _ (kidSourceExtension_child_extended _ _ _ _ _ _ a ha k c m he)
theorem kidSourceExtension_child_extended : ∀ n v d cs slot key a,
    a∈kidSourceAddresses n v d cs slot key → ∀ k c m,a.tree=.ext k c m →
    (⟨a.nid+1,a.vid,a.depth+1,c⟩ : OccurrenceAddress) ∈ kidExtendedAddresses n v d cs slot key
  | _,_,_,.nil,_,_,_,h,_,_,_,_ => by simp [kidSourceAddresses] at h
  | _,_,_,.none _,0,_,_,h,_,_,_,_ => by simp [kidSourceAddresses] at h
  | n,v,d,.some child _,0,key,a,ha,k,c,m,he => sourceExtension_child_extended n v d child key a ha k c m he
  | n,v,d,.none rest,i+1,key,a,ha,k,c,m,he => kidSourceExtension_child_extended n v d rest i key a ha k c m he
  | n,v,d,.some child rest,i+1,key,a,ha,k,c,m,he =>
      kidSourceExtension_child_extended (n+tsize child) (v+(valsOf child).length) d rest i key a ha k c m he
end


theorem occurrenceResolvedId_ext_target {n v d t key a}
    (ha : a∈sourceAddresses n v d t key) {k c m} (he : a.tree=.ext k c m) :
    occurrenceResolvedId (pathRecordId (extendedAddresses n v d t key)) c=viewTarget (a.nid+1) c := by
  have hc := sourceExtension_child_extended n v d t key a ha k c m he
  have hid := extendedAddresses_ids n v d t key hc
  exact congrArg (fun nid => viewTarget nid c) hid

theorem sourceAddress_resolved_extended {n v d t key a}
    (ha : a∈sourceAddresses n v d t key) :
    resolveAddress a.nid a.vid a.depth a.tree∈extendedAddresses n v d t key := by
  obtain ⟨an,av,ad,tree⟩ := a
  cases tree with
  | ext k c m =>
    cases k with
    | nil => exact sourceExtension_extended n v d t key _ ha [] c m rfl
    | cons => exact sourceAddresses_extended n v d t key _ ha
  | hash | leaf | branch => exact sourceAddresses_extended n v d t key _ ha

/-- On actual source-path nodes whose native resolved target is revealed, the
corrected occurrence resolver agrees with the previous native resolver. -/
theorem occurrenceResolvedId_source_agrees {n v d t key a}
    (ha : a∈sourceAddresses n v d t key) (hn : isNode (resolveNative a.tree)=true) :
    occurrenceResolvedId (pathRecordId (extendedAddresses n v d t key)) a.tree=
      resolvedRecordId (pathRecordId (extendedAddresses n v d t key)) a.tree := by
  have hs := extendedRecordId_source ha
  have hr := extendedAddresses_ids n v d t key (sourceAddress_resolved_extended ha)
  simp only [resolveAddress_tree] at hr
  unfold occurrenceResolvedId resolvedRecordId
  rw [hs,hr]
  exact (resolveAddress_target _ _ _ _ hn).symm

end ZkFormal.NearV3.Assembly
