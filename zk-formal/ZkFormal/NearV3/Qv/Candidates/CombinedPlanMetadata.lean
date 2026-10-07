import ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec

theorem mainPlan_last_metadata (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve)
    (w : Walk) (hw : w ∈ mainPlan pre v K resolve) (hl : w.lastMain=true) :
    w.tau=0 ∧ 2≤w.slot ∧ w.kind.code/2=1 ∧
      w.count=(w.kind.code%2)*(w.slot-2) := by
  simp only [mainPlan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hw
  rcases hw with (rfl | rfl | rfl) | ⟨⟨s,i⟩,hi,rfl⟩
  all_goals simp [mainWalk] at hl
  all_goals try omega
  all_goals simp [mainWalk,Kind.code]
  all_goals omega

theorem plan_last_metadata (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (hl : w.lastMain=true) :
    w.tau=0 ∧ 2≤w.slot ∧ w.kind.code/2=1 ∧
      w.count=(w.kind.code%2)*(w.slot-2) := by
  rcases List.mem_append.mp hw with hm | hi
  · exact mainPlan_last_metadata pre v pres.length resolve w hm hl
  · obtain ⟨⟨p,i⟩,_,rfl⟩ := List.mem_map.mp hi
    simp [implicitPlan] at hl

theorem plan_implicit_metadata (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (ht : w.tau≠0) :
    w.kind=.delayed ∧ w.slot=0 ∧ w.lastMain=false := by
  rcases List.mem_append.mp hw with hm | hi
  · simp only [mainPlan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hm
    rcases hm with (rfl | rfl | rfl) | ⟨⟨s,i⟩,_,rfl⟩
    all_goals simp [mainWalk] at ht
  · obtain ⟨⟨p,i⟩,_,rfl⟩ := List.mem_map.mp hi
    exact ⟨rfl,rfl,rfl⟩

theorem plan_final_metadata (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (hf : w.final=true) :
    w.tau=pres.length ∧ (w.tau=0 → w.lastMain=true) := by
  rcases List.mem_append.mp hw with hm | hi
  · simp only [mainPlan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hm
    rcases hm with (rfl | rfl | rfl) | ⟨⟨s,i⟩,_,rfl⟩
    all_goals simp [mainWalk] at hf ⊢
    all_goals simp [hf.2,hf.1]
  · obtain ⟨⟨p,i⟩,_,rfl⟩ := List.mem_map.mp hi
    simp at hf ⊢
    exact hf


theorem plan_absent_buffer_count (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (hv : v.Valid) (w : Walk) (hw : w ∈ plan pre v pres resolve)
    (hk : w.kind.code=1) (ha : w.value.isSome=false) : w.count=0 := by
  rcases List.mem_append.mp hw with hm | hi
  · simp only [mainPlan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hm
    rcases hm with (rfl | rfl | rfl) | ⟨⟨s,i⟩,_,rfl⟩
    all_goals try simp [mainWalk,Kind.code] at hk
    have hb := hv.2.1
    change v.buffered.isSome=false at ha
    change v.shards.length=0
    cases he : v.buffered with
    | none =>
      have hs : v.shards=[] := by simpa [he,BufferedValue] using hb
      simp [hs]
    | some bs => simp [he] at ha
  · obtain ⟨⟨p,i⟩,_,rfl⟩ := List.mem_map.mp hi
    simp [Kind.code] at hk

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

