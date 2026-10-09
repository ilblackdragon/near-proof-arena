import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountClosingVersion
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem closingAccountView_id {pre post : PTrie} {keys : List (List Nat)}
    {key : List Nat} {a : AcctV} (h:closingAccountView pre post keys key=some a) :
    valueIndex pre key=some a.k := by
  simp only [closingAccountView,bind,Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all [nativeAccountView]
  exact congrArg AcctV.k h

theorem closingAccountViews_ids {pre post : PTrie} {keys selected : List (List Nat)} {as : List AcctV}
    (h:closingAccountViews pre post keys selected=some as) :
    as.map AcctV.k=selected.filterMap (valueIndex pre) := by
  induction selected generalizing as with
  | nil=>simp [closingAccountViews] at h;subst as;rfl
  | cons key rest ih=>
    cases hv:closingAccountView pre post keys key with
    | none=>simp [closingAccountViews,hv] at h
    | some a=>
      cases hs:closingAccountViews pre post keys rest with
      | none=>simp [closingAccountViews,hv,hs] at h
      | some tail=>
        simp [closingAccountViews,hv,hs] at h
        subst as
        simp [closingAccountView_id hv,ih hs]

/-- The account constructor names precisely the activated original occurrence
IDs. This membership theorem does not yet assert ID injectivity or a digest
multiset permutation. -/
theorem nativeAccountViews_active_ids {pre post : PTrie} {rs : List Receipt}
    {writes : List (List Nat×Bytes)} {as : List AcctV}
    (hkeys:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (h:nativeAccountViews pre post rs=some as) (i : Nat) :
    i∈as.map AcctV.k ↔ i∈writtenValueIds pre writes := by
  rw [closingAccountViews_ids h]
  simp only [List.mem_filterMap,writtenValueIds]
  constructor
  · rintro ⟨key,hkey,hi⟩
    have hk: key∈writes.map Prod.fst:=by
      rw [hkeys]
      exact (distinctTouched_mem key _).mp hkey
    obtain ⟨w,hw,he⟩:=List.mem_map.mp hk
    exact ⟨w,hw,by simpa [he] using hi⟩
  · rintro ⟨w,hw,hi⟩
    refine ⟨w.1,?_,hi⟩
    apply (distinctTouched_mem w.1 _).mpr
    rw [←hkeys]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
