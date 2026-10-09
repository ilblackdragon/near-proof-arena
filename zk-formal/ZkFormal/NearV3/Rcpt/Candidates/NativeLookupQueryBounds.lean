import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra Render.UpsGen Assembly Qv Qv.Candidates.CombinedWalkGen

def allLookupQueries (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (resolve : Resolve) : List NativeLookupQuery :=
  accountLookupQueries rs++accessKeyLookupQueries rs++queueLookupQueries pre v pres resolve

theorem allLookupQueries_nibbles (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (resolve : Resolve) :
    ∀q∈allLookupQueries rs pre v pres resolve,∀a∈q.key,a<16 := by
  intro q hq
  simp only [allLookupQueries,List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · obtain ⟨⟨r,i⟩,_,rfl⟩:=List.mem_map.mp hq
    simpa only [accountKeyPath,nibblesOk,List.all_eq_true,decide_eq_true_eq] using nibbles_ok (0::r.receiverId)
  · obtain ⟨⟨r,i⟩,_,rfl⟩:=List.mem_map.mp hq
    simpa only [keyAccessKey,nibblesOk,List.all_eq_true,decide_eq_true_eq] using
      nibbles_ok ([2]++r.receiverId++[2]++r.signerPk.encode)
  · obtain ⟨w,_,rfl⟩:=List.mem_map.mp hq
    simpa only [queueLookupQuery,Walk.request,nibblesOk,List.all_eq_true,decide_eq_true_eq] using
      nibbles_ok w.kind.bytes

theorem queue_query_wid (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (hg : 24*v.shards.length≤2000000) (hk : pres.length≤32) :
    ∀q∈queueLookupQueries pre v pres resolve,q.wid<Algebra.P := by
  intro q hq
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hq
  change walkId w.tau w.slot<Algebra.P
  simp only [plan,List.mem_append] at hw
  rcases hw with hw|hw
  · obtain ⟨ht,hs,_⟩:=mainPlan_slot hw
    have hb:= (List.getElem?_eq_some_iff.mp hs).1
    rw [mainRequests_length] at hb
    unfold walkId W_QV Algebra.P
    try dsimp only
    omega
  · obtain ⟨⟨t,i⟩,hi,rfl⟩:=List.mem_map.mp hw
    have hb:= (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)).1
    unfold walkId W_QV Algebra.P
    try dsimp only
    omega

theorem allLookupQueries_wid (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (resolve : Resolve) (hn : rs.length≤4481)
    (hg : 24*v.shards.length≤2000000) (hk : pres.length≤32) :
    ∀q∈allLookupQueries rs pre v pres resolve,q.wid<Algebra.P := by
  intro q hq
  simp only [allLookupQueries,List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · obtain ⟨⟨r,i⟩,hi,rfl⟩:=List.mem_map.mp hq
    have hb:= (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)).1
    change i<2013265921
    omega
  · obtain ⟨⟨r,i⟩,hi,rfl⟩:=List.mem_map.mp hq
    have hb:= (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hi).1)).1
    change 8192+i<2013265921
    omega
  · exact queue_query_wid pre v pres resolve hg hk q hq

theorem allLookupQueries_rows (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (resolve : Resolve) (hr : ∀r∈rs,r.wf=true)
    (hn : rs.length≤4481) (hg : 24*v.shards.length≤2000000) (hk : pres.length≤32) :
    ((allLookupQueries rs pre v pres resolve).map (fun q=>q.key.length+2)).sum≤3441276 := by
  have ha:=account_lookup_rows rs (fun r hm=>(receipt_lookup_widths r (hr r hm)).1)
  have hx:=access_key_lookup_rows rs hr
  simp only [allLookupQueries,List.map_append,List.sum_append,queue_lookup_rows]
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
