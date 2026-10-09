import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocationWf
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

theorem closingKeyVersion_zero (key : List Nat) (start : Nat) (ks : List (List Nat)) :
    closingKeyVersion key start ks=0 ↔ key∉ks := by
  induction ks generalizing start with
  | nil=>simp [closingKeyVersion]
  | cons k ks ih=>
    simp only [closingKeyVersion]
    by_cases ht:closingKeyVersion key (start+1) ks=0
    · have hn: key∉ks:=(ih (start+1)).mp ht
      simp [ht,hn,List.mem_cons,eq_comm]
    · have hm:key∈ks:=by simpa using mt (ih (start+1)).mpr ht
      simp [ht,hm]

/-- The selected version is exactly the last occurrence, retaining the full
receipt index even when other receivers intervene. -/
theorem closingKeyVersion_last (key : List Nat) (start : Nat) (ks : List (List Nat))
    (hm:key∈ks) :
    ∃before after,ks=before++key::after ∧ key∉after ∧
      closingKeyVersion key start ks=start+before.length+1 := by
  induction ks generalizing start with
  | nil=>simp at hm
  | cons k ks ih=>
    by_cases ht:key∈ks
    · obtain ⟨before,after,he,hn,hv⟩:=ih (start+1) ht
      have hz:closingKeyVersion key (start+1) ks≠0:=by
        intro hzero
        exact (closingKeyVersion_zero _ _ _).mp hzero ht
      refine ⟨k::before,after,by simp [he],hn,?_⟩
      simp only [closingKeyVersion,if_neg hz,List.length_cons]
      omega
    · have hk:k=key:=by simpa [ht,eq_comm] using hm
      subst k
      have hz:closingKeyVersion key (start+1) ks=0:=(closingKeyVersion_zero _ _ _).mpr ht
      exact ⟨[],ks,rfl,ht,by simp [closingKeyVersion,hz]⟩

theorem closingKeyVersion_range (key : List Nat) (ks : List (List Nat)) (hm:key∈ks) :
    0<closingKeyVersion key 0 ks ∧ closingKeyVersion key 0 ks≤ks.length := by
  have hz:closingKeyVersion key 0 ks≠0:=by
    intro hzero
    exact (closingKeyVersion_zero _ _ _).mp hzero hm
  have hb:=closingKeyVersion_bound key 0 ks
  omega

open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem closingAccountView_version {pre post : PTrie} {keys : List (List Nat)}
    {key : List Nat} {a : AcctV} (h:closingAccountView pre post keys key=some a) :
    a.tlast=closingKeyVersion key 0 keys := by
  simp only [closingAccountView,bind,Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all [nativeAccountView]
  exact (congrArg AcctV.tlast h).symm

theorem nativeAccountViews_last {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) (a : AcctV) (ha:a∈as) :
    ∃key before after,
      rs.map (fun r=>accountKeyPath r.receiverId)=before++key::after ∧
      key∉after ∧ a.tlast=before.length+1 := by
  obtain ⟨key,hkey,hview⟩:=closingAccountViews_member h a ha
  have hm:= (distinctTouched_mem key _).mp hkey
  obtain ⟨before,after,he,hn,hv⟩:=closingKeyVersion_last key 0 _ hm
  exact ⟨key,before,after,he,hn,by simpa using (closingAccountView_version hview).trans hv⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
