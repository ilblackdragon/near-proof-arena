import ZkFormal.NearV3.Rcpt.Candidates.NativeTouchedAccountDecode
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

/-- Last receipt version touching a concrete account key; version zero denotes
no write. Repeated receivers share one closing account record. -/
def closingKeyVersion (key : List Nat) : Nat→List (List Nat)→Nat
  | _,[]=>0
  | start,k::ks=>let later:=closingKeyVersion key (start+1) ks
    if later=0 then (if k=key then start+1 else 0) else later

theorem closingKeyVersion_bound (key : List Nat) (start : Nat) (ks : List (List Nat)) :
    closingKeyVersion key start ks≤start+ks.length := by
  induction ks generalizing start with
  | nil=>simp [closingKeyVersion]
  | cons k ks ih=>
    have hh:=ih (start+1)
    simp only [closingKeyVersion,List.length_cons]
    split
    · split <;> omega
    · omega

/-- The constructor fails rather than dropping a requested closing account. -/
def closingAccountView (pre post : PTrie) (keys : List (List Nat)) (key : List Nat) : Option AcctV := do
  let i←valueIndex pre key
  let before←(NearSpecV3.valsOf pre)[i]?
  let after←(NearSpecV3.valsOf post)[i]?
  let a←Account.decode after
  pure (nativeAccountView i (closingKeyVersion key 0 keys) before a.amount)

def closingAccountViews (pre post : PTrie) (keys : List (List Nat)) : List (List Nat)→Option (List AcctV)
  | []=>some []
  | key::rest=>do
    let a←closingAccountView pre post keys key
    let as←closingAccountViews pre post keys rest
    pure (a::as)

def nativeAccountViews (pre post : PTrie) (rs : List Receipt) : Option (List AcctV) :=
  let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
  closingAccountViews pre post keys (distinctTouched keys)

theorem closingAccountView_success {pre post : PTrie} {key : List Nat}
    (hp:WriteTreePair pre post)
    (he:(NearSpecV3.valsOf post).map accountSignature=(NearSpecV3.valsOf pre).map accountSignature)
    (ha:AccountAt pre key) (keys : List (List Nat)) :
    ∃a,closingAccountView pre post keys key=some a := by
  obtain ⟨i,before,b,hi,hb,hdec⟩:=ha
  obtain ⟨j,after,a,hj,ha,hdecode⟩:=accountAt_forward hp he ⟨i,before,b,hi,hb,hdec⟩
  have hij:i=j:=Option.some.inj (hi.symm.trans ((write_value_index hp key).trans hj))
  subst j
  exact ⟨nativeAccountView i (closingKeyVersion key 0 keys) before a.amount,by simp [closingAccountView,hi,hb,ha,hdecode]⟩

theorem closingAccountViews_success {pre post : PTrie}
    (hp:WriteTreePair pre post)
    (he:(NearSpecV3.valsOf post).map accountSignature=(NearSpecV3.valsOf pre).map accountSignature)
    (keys selected : List (List Nat)) (ha:∀key∈selected,AccountAt pre key) :
    ∃as,closingAccountViews pre post keys selected=some as ∧ as.length=selected.length := by
  induction selected with
  | nil=>exact ⟨[],rfl,rfl⟩
  | cons key rest ih=>
    obtain ⟨a,ha'⟩:=closingAccountView_success hp he (ha key (by simp)) keys
    obtain ⟨as,has,hlen⟩:=ih (fun key hk=>ha key (by simp [hk]))
    exact ⟨a::as,by simp [closingAccountViews,ha',has],by simp [hlen]⟩

/-- Successful native receipt execution constructs exactly one closing view
per distinct touched key. Empty batches construct the empty account list. -/
theorem nativeAccountViews_success {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out) :
    ∃as,nativeAccountViews st.1.trie out.1.trie rs=some as ∧
      as.length=(distinctTouched (rs.map (fun r=>accountKeyPath r.receiverId))).length ∧
      as.length≤rs.length := by
  obtain ⟨writes,hw,_⟩:=native_sized_account_writes ctx rs i st out h
  have ht:=native_touched_account_decode ctx rs i st out h
  obtain ⟨as,ha,hl⟩:=closingAccountViews_success hw.forget.skeleton
    (native_receipt_signatures ctx rs i st out h) (rs.map (fun r=>accountKeyPath r.receiverId))
    (distinctTouched (rs.map (fun r=>accountKeyPath r.receiverId))) (by
      intro key hk
      have hm: key∈rs.map (fun r=>accountKeyPath r.receiverId):=(distinctTouched_mem key _).mp hk
      obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hm
      exact ht r hr)
  refine ⟨as,ha,hl,?_⟩
  have hb:=distinctTouched_count (rs.map (fun r=>accountKeyPath r.receiverId))
  simpa only [List.length_map,←hl] using hb

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
