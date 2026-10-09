import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountAllocationWf
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem indexed_value_read {t : PTrie} {key : List Nat} {i : Nat} {b : Bytes}
    (hi:valueIndex t key=some i) (hb:(NearSpecV3.valsOf t)[i]?=some b) :
    t.find key=some (some b) := by
  obtain ⟨raw,hr⟩:=valueIndex_defined t key i hi
  obtain ⟨j,hj,hv⟩:=valueIndex_complete t key raw hr
  have hij:i=j:=Option.some.inj (hi.symm.trans hj)
  subst j
  have he:raw=b:=Option.some.inj (hv.symm.trans hb)
  simpa only [he] using hr

/-- Same receiver lookup on the actual native receipt-stage pre/post tries,
with exact decodable byte strings and immutable suffix conservation. -/
theorem native_touched_read_pair {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    (r : Receipt) (hr:r∈rs) :
    ∃pre post a b,
      st.1.trie.find (accountKeyPath r.receiverId)=some (some pre) ∧
      out.1.trie.find (accountKeyPath r.receiverId)=some (some post) ∧
      Account.decode pre=some a ∧ Account.decode post=some b ∧ post.drop 16=pre.drop 16 := by
  obtain ⟨j,pre,a,hj,hpre,hda⟩:=native_touched_account_decode ctx rs i st out h r hr
  obtain ⟨l,post,b,hl,hpost,hdb⟩:=native_touched_final_decode h r hr
  obtain ⟨writes,hw,_⟩:=native_sized_account_writes ctx rs i st out h
  have hij:j=l:=Option.some.inj (hj.symm.trans ((write_value_index hw.forget.skeleton _).trans hl))
  subst l
  have he:=congrArg (fun xs=>xs[j]?) (native_receipt_signatures ctx rs i st out h)
  simp only [List.getElem?_map,hpre,hpost,Option.map_some,Option.some.injEq] at he
  exact ⟨pre,post,a,b,indexed_value_read hj hpre,indexed_value_read hl hpost,hda,hdb,congrArg Prod.snd he⟩

/-- Structural scheduler changes may renumber compact values. Re-index an
account in the ORIGINAL prestate using equal actual keyed reads, never by
identifying its ordinal with the scheduler-intermediate ordinal. -/
theorem rebased_closing_view {original replay : PTrie} (hp:WriteTreePair original replay)
    {key : List Nat} {pre post : Bytes} {a b : Account}
    (hpre:original.find key=some (some pre)) (hpost:replay.find key=some (some post))
    (hda:Account.decode pre=some a) (hdb:Account.decode post=some b)
    (hs:post.drop 16=pre.drop 16) (keys : List (List Nat)) :
    ∃j,valueIndex original key=some j ∧
      closingAccountView original replay keys key=some (nativeAccountView j (closingKeyVersion key 0 keys) pre b.amount) ∧
      (nativeAccountView j (closingKeyVersion key 0 keys) pre b.amount).post++
        (nativeAccountView j (closingKeyVersion key 0 keys) pre b.amount).pre.drop 16=post.map UInt8.toNat := by
  obtain ⟨j,hj,hvb⟩:=valueIndex_complete original key pre hpre
  obtain ⟨l,hl,hva⟩:=valueIndex_complete replay key post hpost
  have hij:j=l:=Option.some.inj (hj.symm.trans ((write_value_index hp key).trans hl))
  subst l
  exact ⟨j,hj,by simp [closingAccountView,hj,hvb,hva,hdb],nativeAccountView_final_payload _ _ hdb hs⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
