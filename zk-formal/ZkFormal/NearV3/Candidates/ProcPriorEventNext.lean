import ZkFormal.NearV3.Candidates.ProcPriorEventOrder
namespace ZkFormal.NearV3.Candidates.ProcPriorEventNext
open NearSpec NearSpec.Bandwidth ProcPriorEvents ProcPriorEventOrder

theorem writes_nodup (ids : List Nat) (rs : List LinkAllowance) : (writeEvents ids rs).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply (write_order ids rs).imp
  intro a b h he
  subst b
  omega

theorem queries_nodup (ids : List Nat) (rs : List LinkAllowance) : (queryEvents ids rs).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply List.pairwise_map.mpr
  apply List.pairwise_lt_range.imp
  intro a b hab he
  have hh:=congrArg Event.link he
  dsimp at hh
  omega

theorem events_nodup (ids : List Nat) (rs : List LinkAllowance) : (events ids rs).Nodup := by
  apply (events_perm ids rs).nodup_iff.mpr
  rw [List.nodup_append]
  refine ⟨writes_nodup ids rs,queries_nodup ids rs,?_⟩
  intro e hw f hq hef
  subst f
  obtain ⟨_,_,_,he,_,_⟩:=write_source ids rs e hw
  have ht:= (query_source ids rs e hq).2.2.1
  rw [ht] at he
  cases he

theorem adjacent (ids : List Nat) (rs : List LinkAllowance) (pre post : List Event) (a b : Event)
    (h:events ids rs=pre++a::b::post) : a≠b ∧ precedes a b=true := by
  have hn:=events_nodup ids rs
  have hs:=events_sorted ids rs
  rw [h,List.nodup_append] at hn
  rw [h,List.pairwise_append] at hs
  exact ⟨fun he=>(List.nodup_cons.mp hn.2.1).1 (by simp [he]),
    (List.pairwise_cons.mp hs.2.1).1 b (by simp)⟩

theorem query_final (ids : List Nat) (rs : List LinkAllowance) (pre post : List Event) (a b : Event)
    (h:events ids rs=pre++a::b::post) (hq:a.query=true) : a.link≠b.link := by
  obtain ⟨hne,hs⟩:=adjacent ids rs pre post a b h
  have ham:a∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp (by rw [h]; simp)
  have hbm:b∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp (by rw [h]; simp)
  have ha:a∈queryEvents ids rs := by
    rcases List.mem_append.mp ham with hw|hq'
    · obtain ⟨_,_,_,hf,_,_⟩:=write_source ids rs a hw
      rw [hq] at hf; cases hf
    · exact hq'
  have hta:a.stamp=rs.length := (query_source ids rs a ha).2.1
  intro hk
  rcases List.mem_append.mp hbm with hw|hr
  · have hb:=write_before_queries ids rs b hw
    simp only [precedes,decide_eq_true_eq] at hs
    omega
  · have htb:b.stamp=rs.length := (query_source ids rs b hr).2.1
    exact hne (event_unique ids rs a b ham (List.mem_append_right _ hr) hk (by omega))

theorem next_write_stamp (ids : List Nat) (rs : List LinkAllowance) (pre post : List Event) (a b : Event)
    (h:events ids rs=pre++a::b::post) (hk:a.link=b.link) : a.stamp+1≤b.stamp := by
  obtain ⟨hne,hs⟩:=adjacent ids rs pre post a b h
  have ham:a∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp (by rw [h]; simp)
  have hbm:b∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp (by rw [h]; simp)
  have ht:a.stamp≠b.stamp := fun he=>hne (event_unique ids rs a b ham hbm hk he)
  simp only [precedes,decide_eq_true_eq] at hs
  omega

end ZkFormal.NearV3.Candidates.ProcPriorEventNext
