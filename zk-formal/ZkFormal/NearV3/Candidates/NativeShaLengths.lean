import ZkFormal.NearV3.Candidates.NativePostShaBudget

namespace ZkFormal.NearV3.Candidates.NativeShaLengths
open ZkFormal.Near Render Rcpt.Candidates

theorem node_origin (ns : List NodeS3) (n : Nat) (m : Render.Msg)
    (h : m∈nativeNodeShaJobsFrom n ns) : ∃s∈ns,∃post,m.bytes=s.v.ser post := by
  induction ns generalizing n with
  | nil => simp [nativeNodeShaJobsFrom] at h
  | cons s ss ih =>
    simp only [nativeNodeShaJobsFrom,List.mem_cons] at h
    rcases h with rfl|rfl|h
    · exact ⟨s,by simp,false,rfl⟩
    · exact ⟨s,by simp,true,rfl⟩
    · obtain ⟨o,ho,p,hp⟩:=ih (n+1) h
      exact ⟨o,by simp [ho],p,hp⟩

theorem value_origin (vs : List ValE) (m : Render.Msg) (h : m∈nativeValueShaJobs vs) :
    ∃v∈vs,m.bytes=v.bytes := by
  induction vs with
  | nil => simp [nativeValueShaJobs] at h
  | cons v vs ih =>
    simp only [nativeValueShaJobs,List.mem_append] at h
    rcases h with h|h
    · split at h
      · simp at h
      · simp only [List.mem_singleton] at h
        subst m
        exact ⟨v,by simp,rfl⟩
    · obtain ⟨o,ho,he⟩:=ih h
      exact ⟨o,by simp [ho],he⟩

theorem jobs_length (ns : List NodeS3) (vs : List ValE) (hn : NodeWf3 ns) (hv : ValWf vs) :
    ∀m∈nativeShaJobs ns vs,m.bytes.length<2^25 := by
  intro m hm
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨s,hs,post,he⟩:=node_origin ns 0 m hm
    have hh:=Link3.le_sum_mem (List.mem_map.mpr ⟨s,hs,rfl⟩ :
      (s.v.ser false).length∈ns.map (fun s=>(s.v.ser false).length))
    have hr:=hn.rows
    rw [he]
    cases post with
    | false => omega
    | true => rw [node_post_length s.v (hn.wf s hs)];omega
  · obtain ⟨v,hv',he⟩:=value_origin vs m hm
    have hh:=Link3.le_sum_mem (List.mem_map.mpr ⟨v,hv',rfl⟩ :
      (if v.vz then 1 else v.len)∈vs.map (fun v=>if v.vz then 1 else v.len))
    have hs:=hv.shape v hv'
    have hr:=hv.rows
    rw [he]
    cases hz : v.vz with
    | true => rw [(hs.1 hz).2];simp
    | false => rw [(hs.2 hz).1];simp only [hz,Bool.false_eq_true,ite_false] at hh;omega

end ZkFormal.NearV3.Candidates.NativeShaLengths
