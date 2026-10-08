import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountIds
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem valueIndex_filterMap_nodup (pre : PTrie) (keys : List (List Nat))
    (hn:keys.Nodup) : (keys.filterMap (valueIndex pre)).Nodup := by
  induction keys with
  | nil=>simp
  | cons key keys ih=>
    obtain ⟨hnot,ht⟩:=List.nodup_cons.mp hn
    cases hi:valueIndex pre key with
    | none=>simpa [hi] using ih ht
    | some i=>
      simp only [List.filterMap_cons,hi]
      apply List.nodup_cons.mpr
      refine ⟨?_,ih ht⟩
      intro hm
      obtain ⟨other,ho,hj⟩:=List.mem_filterMap.mp hm
      have he:=valueIndex_key_unique pre key other i hi hj
      exact hnot (he ▸ ho)

theorem nativeAccountViews_ids_nodup {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) : (as.map AcctV.k).Nodup := by
  rw [closingAccountViews_ids h]
  exact valueIndex_filterMap_nodup _ _ (distinctTouched_nodup _)

/-- Exact occurrence multiplicities: closing records are a permutation of the
activated original value indices, each exactly once. -/
theorem nativeAccountViews_ids_perm {pre post : PTrie} {rs : List Receipt}
    {writes : List (List Nat×Bytes)} {as : List AcctV}
    (hkeys:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (h:nativeAccountViews pre post rs=some as) :
    (as.map AcctV.k).Perm
      ((List.range (NearSpecV3.valsOf pre).length).filter (fun i=>decide (i∈writtenValueIds pre writes))) := by
  apply (List.perm_ext_iff_of_nodup (nativeAccountViews_ids_nodup h)
    (List.Pairwise.filter _ (List.nodup_range))).mpr
  intro i
  rw [nativeAccountViews_active_ids hkeys h]
  simp only [List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · intro hi
    obtain ⟨w,_,hw⟩:=List.mem_filterMap.mp hi
    exact ⟨valueIndex_bound hw,hi⟩
  · exact And.right

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
