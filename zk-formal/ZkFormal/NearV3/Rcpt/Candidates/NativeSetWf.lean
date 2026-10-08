import ZkFormal.NearV3.Rcpt.Candidates.NativeSizedReplay

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

mutual
theorem native_set_wf : ∀(t : PTrie)(key : List Nat)(value : Bytes)(post : PTrie),
    t.set key value=some post → t.wf=true → value.length<4294967296 → post.wf=true
  | .hash _,_,_,_,h,_,_=>by simp [PTrie.set] at h
  | .leaf k s m,key,value,post,h,hw,hv=>by
    simp only [PTrie.set] at h
    split at h
    · cases hs:s.get <;> simp [hs] at h
      subst post
      simp only [PTrie.wf,Bool.and_eq_true] at hw ⊢
      exact ⟨⟨⟨hw.1.1.1,by simp [slotOk,hv]⟩,hw.1.2⟩,hw.2⟩
    · simp at h
  | .ext k c m,key,value,post,h,hw,hv=>by
    simp only [PTrie.set] at h
    split at h
    · cases hs:c.set (key.drop k.length) value with
      | none=>simp [hs] at h
      | some child=>
        simp only [hs,Option.map_some,Option.some.injEq] at h
        subst post
        simp only [PTrie.wf,Bool.and_eq_true] at hw ⊢
        exact ⟨⟨⟨hw.1.1.1,native_set_wf c _ value child hs hw.1.1.2 hv⟩,hw.1.2⟩,hw.2⟩
    · simp at h
  | .branch v cs m,[],value,post,h,hw,hv=>by
    simp only [PTrie.set] at h
    split at h <;> simp at h
    subst post
    simp only [PTrie.wf,Bool.and_eq_true] at hw ⊢
    exact ⟨⟨by simp [slotOk,hv],hw.1.2⟩,hw.2⟩
  | .branch v cs m,n::key,value,post,h,hw,hv=>by
    simp only [PTrie.set] at h
    cases hs:Kids.set cs n key value with
    | none=>simp [hs] at h
    | some children=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      simp only [PTrie.wf,Bool.and_eq_true] at hw ⊢
      exact ⟨⟨hw.1.1,native_kids_set_wf cs n key value children 16 hs hw.1.2 hv⟩,hw.2⟩
theorem native_kids_set_wf : ∀(cs : Kids)(n : Nat)(key : List Nat)(value : Bytes)(post : Kids)(width : Nat),
    Kids.set cs n key value=some post → Kids.wf cs width=true → value.length<4294967296 → Kids.wf post width=true
  | .nil,_,_,_,_,_,h,_,_=>by simp [Kids.set] at h
  | .none _,0,_,_,_,_,h,_,_=>by simp [Kids.set] at h
  | .some c rest,0,key,value,post,width,h,hw,hv=>by
    simp only [Kids.set] at h
    cases hs:c.set key value with
    | none=>simp [hs] at h
    | some child=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      simp only [Kids.wf,Bool.and_eq_true] at hw ⊢
      exact ⟨⟨hw.1.1,native_set_wf c key value child hs hw.1.2 hv⟩,hw.2⟩
  | .none rest,n+1,key,value,post,width,h,hw,hv=>by
    simp only [Kids.set] at h
    cases hs:Kids.set rest n key value with
    | none=>simp [hs] at h
    | some children=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      simp only [Kids.wf,Bool.and_eq_true] at hw ⊢
      exact ⟨hw.1,native_kids_set_wf rest n key value children (width-1) hs hw.2 hv⟩
  | .some c rest,n+1,key,value,post,width,h,hw,hv=>by
    simp only [Kids.set] at h
    cases hs:Kids.set rest n key value with
    | none=>simp [hs] at h
    | some children=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      simp only [Kids.wf,Bool.and_eq_true] at hw ⊢
      exact ⟨hw.1,native_kids_set_wf rest n key value children (width-1) hs hw.2 hv⟩
end

theorem SizedAccountRun.wf {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes post) (hw : pre.wf=true) : post.wf=true := by
  induction h with
  | nil=>exact hw
  | cons hr hl hn hs ht ih=>exact ih (native_set_wf _ _ _ _ hs hw (by omega))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
