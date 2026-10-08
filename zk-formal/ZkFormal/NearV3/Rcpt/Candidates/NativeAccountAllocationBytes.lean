import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocationWf
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

/-- Every successfully constructed account has byte-faithful PRE and POST
fields, including the initial amount that is not in its VPOST SHA preimage. -/
theorem closingAccountView_bytes {pre post : PTrie} {keys : List (List Nat)} {key : List Nat} {v : AcctV}
    (h:closingAccountView pre post keys key=some v) : ∀b∈v.pre++v.post,b<256 := by
  unfold closingAccountView at h
  cases hi:valueIndex pre key with
  | none=>simp [hi] at h
  | some i=>
    simp only [hi,bind,Option.bind] at h
    cases hb:(NearSpecV3.valsOf pre)[i]? with
    | none=>simp [hb] at h
    | some before=>
      simp only [hb] at h
      cases ha:(NearSpecV3.valsOf post)[i]? with
      | none=>simp [ha] at h
      | some after=>
        simp only [ha] at h
        cases hd:Account.decode after with
        | none=>simp [hd] at h
        | some a=>
          simp only [hd,pure,Option.some.injEq] at h
          subst v
          exact nativeAccountView_bytes _ _ _ _

theorem closingAccountViews_bytes {pre post : PTrie} {keys selected : List (List Nat)} {as : List AcctV}
    (h:closingAccountViews pre post keys selected=some as) : ∀a∈as,∀b∈a.pre++a.post,b<256 := by
  intro a ha
  obtain ⟨key,_,hv⟩:=closingAccountViews_member h a ha
  exact closingAccountView_bytes hv

theorem nativeAccountViews_bytes {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) : ∀a∈as,∀b∈a.pre++a.post,b<256 :=
  closingAccountViews_bytes h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
