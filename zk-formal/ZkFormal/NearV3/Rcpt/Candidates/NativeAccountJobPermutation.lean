import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountIdPermutation
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountRebasedAllocation
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

/-- Actual native writes supply the final payload at the original compact ID,
not the possibly shifted receipt-stage value index. -/
theorem native_rebased_account_payload {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {original replay : PTrie} (hp:WriteTreePair original replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as)
    (a : AcctV) (ha:a∈as) :
    ∃before after,(NearSpecV3.valsOf original)[a.k]?=some before ∧
      (NearSpecV3.valsOf replay)[a.k]?=some after ∧ before.length=72 ∧ after.length=72 ∧
      a.post++a.pre.drop 16=after.map UInt8.toNat := by
  obtain ⟨key,hkey,hview⟩:=closingAccountViews_member has a ha
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ((distinctTouched_mem key _).mp hkey)
  obtain ⟨before,after,b,c,hb,hc,hdb,hdc,hs⟩:=native_touched_read_pair h r hr
  have hor:original.find (accountKeyPath r.receiverId)=some (some before):=(hpre _).trans hb
  have hrep:replay.find (accountKeyPath r.receiverId)=some (some after):=(hpost _).trans hc
  obtain ⟨j,hj,hv,hpayload⟩:=rebased_closing_view hp hor hrep hdb hdc hs
    (rs.map (fun r=>accountKeyPath r.receiverId))
  have he:=Option.some.inj (hview.symm.trans hv)
  subst a
  obtain ⟨l,hl,hvl⟩:=valueIndex_complete original _ before hor
  have heq:j=l:=Option.some.inj (hj.symm.trans hl)
  subst l
  obtain ⟨l,hl,hva⟩:=valueIndex_complete replay _ after hrep
  have heq:j=l:=Option.some.inj (hj.symm.trans ((write_value_index hp _).trans hl))
  subst l
  exact ⟨before,after,hvl,hva,(Sound.decode_wf hdb).2.2.2.2,
    (Sound.decode_wf hdc).2.2.2.2,hpayload⟩

/-- Account SHA jobs retain exactly one final byte preimage for each activated
original value ID, including repeated receipt writes to the same account. -/
theorem native_rebased_account_jobs {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {original replay : PTrie} (hp:WriteTreePair original replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    {writes : List (List Nat×Bytes)}
    (hkeys:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as) :
    (accountShaJobs as).Perm
      (((List.range (NearSpecV3.valsOf original).length).filter
        (fun i=>decide (i∈writtenValueIds original writes))).map
          (fun j=> (⟨msgId K_VPOST j,((NearSpecV3.valsOf replay).getD j []).map UInt8.toNat⟩ : Render.Msg))) := by
  have he:accountShaJobs as=(as.map AcctV.k).map
      (fun j=> (⟨msgId K_VPOST j,((NearSpecV3.valsOf replay).getD j []).map UInt8.toNat⟩ : Render.Msg)) := by
    simp only [accountShaJobs,List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨_,after,_,hafter,_,_,hpay⟩:=native_rebased_account_payload h hp hpre hpost has a ha
    simp only [Function.comp_apply,hpay,List.getD_eq_getElem?_getD,hafter,Option.getD_some]
  rw [he]
  exact (nativeAccountViews_ids_perm hkeys has).map _

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
