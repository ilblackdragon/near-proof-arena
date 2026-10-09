import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountReadPair
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocationBytes
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem closingAccountViews_of_each (pre post : PTrie) (keys selected : List (List Nat))
    (h:∀key∈selected,∃a,closingAccountView pre post keys key=some a) :
    ∃as,closingAccountViews pre post keys selected=some as ∧ as.length=selected.length := by
  induction selected with
  | nil=>exact ⟨[],rfl,rfl⟩
  | cons key rest ih=>
    obtain ⟨a,ha⟩:=h key (by simp)
    obtain ⟨as,has,hl⟩:=ih (fun k hk=>h k (by simp [hk]))
    exact ⟨a::as,by simp [closingAccountViews,ha,has],by simp [hl]⟩

/-- Choose the whole account list on the original prestate/replayed old-tree
allocation using actual native account reads. No equality of value ordinals
with the scheduler-intermediate trie is assumed. -/
theorem native_rebased_accounts {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    (original replay : PTrie) (hp:WriteTreePair original replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    (hn:(NearSpecV3.valsOf original).length<Algebra.P) (hr:rs.length<Algebra.P) :
    ∃as,nativeAccountViews original replay rs=some as ∧ as.length≤rs.length ∧
      (as=[] ∨ AcctWf as) ∧ (∀a∈as,∀b∈a.pre++a.post,b<256) ∧
      (∀m∈accountShaJobs as,∀b∈m.bytes,b<256) := by
  let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
  have hsingle : ∀key∈keys,∃v,closingAccountView original replay keys key=some v ∧ AcctWf [v] := by
    intro key hk
    obtain ⟨r,hm,rfl⟩:=List.mem_map.mp hk
    obtain ⟨before,after,a,b,hb,ha,hda,hdb,hs⟩:=native_touched_read_pair h r hm
    have hor:original.find (accountKeyPath r.receiverId)=some (some before):=(hpre _).trans hb
    have hrep:replay.find (accountKeyPath r.receiverId)=some (some after):=(hpost _).trans ha
    obtain ⟨j,hj,hv,_⟩:=rebased_closing_view hp hor hrep hda hdb hs keys
    have hjb:j<Algebra.P:=Nat.lt_trans (valueIndex_bound hj) hn
    have htb:closingKeyVersion (accountKeyPath r.receiverId) 0 keys<Algebra.P:=by
      have hh:=closingKeyVersion_bound (accountKeyPath r.receiverId) 0 keys
      have hl:keys.length=rs.length:=by simp [keys]
      omega
    exact ⟨_,hv,nativeAccountView_wf j _ hjb htb hda b.amount⟩
  obtain ⟨as,ha,hlen⟩:=closingAccountViews_of_each original replay keys (distinctTouched keys) (by
    intro key hk
    obtain ⟨v,hv,_⟩:=hsingle key ((distinctTouched_mem key keys).mp hk)
    exact ⟨v,hv⟩)
  have hbytes:=closingAccountViews_bytes ha
  have hrecords:∀v∈as,AcctWf [v] := by
    intro v hv
    obtain ⟨key,hk,hv⟩:=closingAccountViews_member ha v hv
    obtain ⟨a,hav,hwf⟩:=hsingle key ((distinctTouched_mem key keys).mp hk)
    have he:a=v:=Option.some.inj (hav.symm.trans hv)
    simpa only [he] using hwf
  refine ⟨as,ha,?_,?_,hbytes,?_⟩
  · have hh:=distinctTouched_count keys
    simpa only [←hlen,keys,List.length_map] using hh
  · by_cases he:as=[]
    · exact Or.inl he
    · right
      refine ⟨he,?_,?_,?_⟩
      · intro a hm;exact (hrecords a hm).len a (by simp)
      · intro a hm;exact (hrecords a hm).notMax a (by simp)
      · intro a hm;exact (hrecords a hm).canon a (by simp)
  · intro m hm b hb
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    rcases List.mem_append.mp hb with hb|hb
    · exact hbytes a ha b (List.mem_append_right _ hb)
    · exact hbytes a ha b (List.mem_append_left _ (List.mem_of_mem_drop hb))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
