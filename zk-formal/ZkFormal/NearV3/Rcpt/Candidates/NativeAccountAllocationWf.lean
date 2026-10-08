import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocation
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem closingAccountView_wf {pre post : PTrie} {keys : List (List Nat)} {key : List Nat} {v : AcctV}
    (he:(NearSpecV3.valsOf post).map accountSignature=(NearSpecV3.valsOf pre).map accountSignature)
    (hn:(NearSpecV3.valsOf pre).length<Algebra.P) (hk:keys.length<Algebra.P)
    (h:closingAccountView pre post keys key=some v) :
    AcctWf [v] ∧ ∀m∈accountShaJobs [v],∀b∈m.bytes,b<256 := by
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
          have hs:=congrArg (fun xs=>xs[i]?) he
          simp only [List.getElem?_map,hb,ha,Option.map_some,Option.some.injEq] at hs
          have hid:i<Algebra.P:=Nat.lt_trans (List.getElem?_eq_some_iff.mp hb).1 hn
          have ht:closingKeyVersion key 0 keys<Algebra.P:=by
            have hh:=closingKeyVersion_bound key 0 keys
            omega
          have hv:=nativeAccountPair_view i (closingKeyVersion key 0 keys) hid ht hs hd
          exact ⟨hv.1,hv.2.2⟩

theorem closingAccountViews_member {pre post : PTrie} {keys selected : List (List Nat)} {as : List AcctV}
    (h:closingAccountViews pre post keys selected=some as) (a : AcctV) (ha:a∈as) :
    ∃key∈selected,closingAccountView pre post keys key=some a := by
  induction selected generalizing as with
  | nil=>simp [closingAccountViews] at h;subst as;simp at ha
  | cons key rest ih=>
    simp only [closingAccountViews] at h
    cases hv:closingAccountView pre post keys key with
    | none=>simp [hv] at h
    | some v=>
      cases hs:closingAccountViews pre post keys rest with
      | none=>simp [hv,hs] at h
      | some vs=>
        simp only [hv,hs,bind,Option.bind,pure,Option.some.injEq] at h
        subst as
        rcases List.mem_cons.mp ha with rfl|ha
        · exact ⟨key,by simp,hv⟩
        · obtain ⟨k,hk,hv⟩:=ih hs ha
          exact ⟨k,by simp [hk],hv⟩

/-- Empty native batches remain allowed. Otherwise the entire actual closing
account list is well formed and every SHA preimage is a real byte sequence. -/
theorem nativeAccountViews_wf {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} {as : List AcctV}
    (h:applyReceipts ctx i st rs=.ok out)
    (ha:nativeAccountViews st.1.trie out.1.trie rs=some as)
    (hn:(NearSpecV3.valsOf st.1.trie).length<Algebra.P) (hr:rs.length<Algebra.P) :
    (as=[] ∨ AcctWf as) ∧ ∀m∈accountShaJobs as,∀b∈m.bytes,b<256 := by
  have hspec : ∀a∈as,AcctWf [a] ∧ ∀m∈accountShaJobs [a],∀b∈m.bytes,b<256 := by
    intro a hmem
    obtain ⟨key,_,hv⟩:=closingAccountViews_member ha a hmem
    exact closingAccountView_wf (native_receipt_signatures ctx rs i st out h) hn
      (by simpa only [List.length_map] using hr) hv
  constructor
  · by_cases he:as=[]
    · exact Or.inl he
    · right
      refine ⟨he,?_,?_,?_⟩
      · intro a hm;exact (hspec a hm).1.len a (by simp)
      · intro a hm;exact (hspec a hm).1.notMax a (by simp)
      · intro a hm;exact (hspec a hm).1.canon a (by simp)
  · intro m hm b hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    exact (hspec a ha).2 _ (by simp [accountShaJobs]) b hb

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
