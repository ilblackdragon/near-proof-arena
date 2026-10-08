import ZkFormal.NearV3.Candidates.PostNodeBytes
import ZkFormal.NearV3.Candidates.NativeExecutionPost

namespace ZkFormal.NearV3.Candidates.NativePostBytes
open NearSpec ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem forest_bytes (ts : List PTrie) (hw : ∀t∈ts,t.wf=true) (post : Bool)
    (s : NodeS3) (hs : s∈forestNodes 0 0 0 ts) : ∀x∈s.v.ser post,x<256 := by
  have hm : s.v.ser post∈(forestNodes 0 0 0 ts).map (fun s=>s.v.ser post) := List.mem_map.mpr ⟨s,hs,rfl⟩
  rw [forestNodes_bytes post 0 0 0 ts hw] at hm
  obtain ⟨o,_,he⟩:=List.mem_map.mp hm
  rw [←he]
  intro x hx
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hx
  exact b.toNat_lt

/-- Both streams of actual native allocated records remain valid bytes after
post digest replacement and all metadata/count assignments. -/
theorem updated_bytes (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (cs : List StoreDuplicateChain.Entry) (u : Inputs) (q : UseRequests)
    (s : NodeS3)
    (hs : s∈assignList q 0 (records u (ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 ts))))) :
    ∀post x,x∈s.v.ser post → x<256 := by
  obtain ⟨i,a,ha,rfl⟩:=assignList_member q _ 0 s hs
  simp only [records,List.mem_map] at ha
  obtain ⟨b,hb,rfl⟩:=ha
  obtain ⟨j,c,hc,rfl⟩:=ChainMetadata.assign_member cs _ 0 b hb
  obtain ⟨k,_,d,hd,rfl⟩:=initializeList_member _ 0 c hc
  intro post
  change ∀x,x∈(node u d.v).ser post → x<256
  cases post with
  | false => rw [node_pre];exact forest_bytes ts hw false d (List.mem_of_getElem? hd)
  | true => exact PostNodeBytes.node_bytes u d.v (forest_bytes ts hw true d (List.mem_of_getElem? hd))

theorem node_jobs_bytes (ns : List NodeS3)
    (h : ∀s∈ns,∀post x,x∈s.v.ser post → x<256) (n : Nat) :
    ∀m∈nativeNodeShaJobsFrom n ns,∀x∈m.bytes,x<256 := by
  induction ns generalizing n with
  | nil => simp [nativeNodeShaJobsFrom]
  | cons s ss ih =>
    intro m hm
    simp only [nativeNodeShaJobsFrom,List.mem_cons] at hm
    rcases hm with rfl|rfl|hm
    · exact h s (by simp) false
    · exact h s (by simp) true
    · exact ih (fun s hs=>h s (by simp [hs])) (n+1) m hm

theorem seed_value_bytes (cs : List StoreDuplicateChain.Entry) (n : Nat) (bs : List Bytes) :
    ∀v∈ChainMetadata.assignValues cs (seedValuesFrom n bs),∀x∈v.bytes,x<256 := by
  induction bs generalizing n with
  | nil => simp [seedValuesFrom,ChainMetadata.assignValues]
  | cons b bs ih =>
    intro v hv
    simp only [seedValuesFrom,ChainMetadata.assignValues,List.map_cons,List.mem_cons] at hv
    rcases hv with rfl|hv
    · intro x hx
      change x∈b.map UInt8.toNat at hx
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp hx
      exact b.toNat_lt
    · exact ih (n+1) v hv

theorem value_jobs_bytes (vs : List ValE) (h : ∀v∈vs,∀x∈v.bytes,x<256) :
    ∀m∈nativeValueShaJobs vs,∀x∈m.bytes,x<256 := by
  induction vs with
  | nil => simp [nativeValueShaJobs]
  | cons v vs ih =>
    intro m hm
    simp only [nativeValueShaJobs,List.mem_append] at hm
    rcases hm with hm|hm
    · split at hm
      · simp at hm
      · simp only [List.mem_singleton] at hm
        subst m
        exact h v (by simp)
    · exact ih (fun v hv=>h v (by simp [hv])) m hm

theorem jobs_bytes (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (cs : List StoreDuplicateChain.Entry) (u : Inputs) (q : UseRequests) :
    let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 ts))))
    let vs:=ChainMetadata.assignValues cs (seedValuesFrom 0 (forestBytes ts))
    ∀m∈nativeShaJobs ns vs,∀x∈m.bytes,x<256 := by
  dsimp only
  intro m hm
  rcases List.mem_append.mp hm with hm|hm
  · exact node_jobs_bytes _ (updated_bytes ts hw cs u q) 0 m hm
  · exact value_jobs_bytes _ (seed_value_bytes cs 0 _) m hm

end ZkFormal.NearV3.Candidates.NativePostBytes
