import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPostDigest
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem forestPostValue_unwritten (rs : List ReplayTree) (hn:∀r∈rs,r.writes=[]) (i : Nat) :
    forestPostValue rs i=none := by
  induction rs generalizing i with
  | nil=>rfl
  | cons r rs ih=>
    have hr:=hn r (by simp)
    have ht:=ih (fun r hm=>hn r (by simp [hm]))
    simp [forestPostValue,oldTreeInputs,hr,writtenValueIds,ht]

theorem oldTreeInputs_outside (pre post : PTrie) (writes : List (List Nat×Bytes))
    (i : Nat) (hi:(NearSpecV3.valsOf pre).length≤i) :
    (oldTreeInputs pre post writes).value i=none := by
  apply oldTreeInputs_unwritten
  intro hm
  obtain ⟨w,hw,hj⟩:=List.mem_filterMap.mp hm
  have hb:=valueIndex_bound hj
  omega

theorem postDigestFrom_silent (u : Inputs) (i : Nat) (bs : List Bytes)
    (hn:∀j,i≤j→u.value j=none) : postDigestFrom u i bs=[] := by
  induction bs generalizing i with
  | nil=>rfl
  | cons b bs ih=>
    rw [postDigestFrom,hn i (by omega)]
    exact ih (i+1) (fun j hj=>hn j (by omega))

/-- Implicit transitions have no receipt writes and contribute no VPOST slots;
the original main transition alone supplies the account closing inventory. -/
theorem forest_main_postDigests (pre post : PTrie) (writes : List (List Nat×Bytes))
    (tail : List ReplayTree) (ht:∀r∈tail,r.writes=[]) :
    postDigestFrom (forestOldInputs (⟨pre,post,writes⟩::tail)) 0
      (forestBytes ((⟨pre,post,writes⟩::tail).map ReplayTree.pre))=
    postDigestFrom (oldTreeInputs pre post writes) 0 (NearSpecV3.valsOf pre) := by
  have he:∀i,(forestOldInputs (⟨pre,post,writes⟩::tail)).value i=
      (oldTreeInputs pre post writes).value i:=by
    intro i
    simp only [forestOldInputs,forestPostValue]
    split
    · rfl
    · rename_i hi
      rw [forestPostValue_unwritten tail ht]
      symm
      apply oldTreeInputs_outside
      rw [Assembly.native_valsOf_eq]
      omega
  simp only [List.map_cons,forestBytes,List.flatMap_cons]
  rw [postDigestFrom_append]
  have hz:postDigestFrom (forestOldInputs (⟨pre,post,writes⟩::tail))
      (0+(ZkFormal.NearV3.valsOf pre).length) (forestBytes (tail.map ReplayTree.pre))=[]:=by
    apply postDigestFrom_silent
    intro j hj
    rw [he]
    apply oldTreeInputs_outside
    rw [Assembly.native_valsOf_eq]
    omega
  simp only [forestBytes] at hz
  rw [hz,List.append_nil,postDigestFrom_indexed,postDigestFrom_indexed]
  rw [Assembly.native_valsOf_eq]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro j hj
  rw [he]

/-- Full final-node VPOST request multiset equals the native account SHA
providers on the same replay, with all implicit transitions retained. -/
theorem native_account_forest_digest_balance {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {original replay : PTrie} {writes : List (List Nat×Bytes)}
    (hr:SizedAccountRun original writes replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    (hkeys:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as)
    (tail : List ReplayTree) (ht:∀r∈tail,r.writes=[]) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) :
    ((accountShaJobs as).map Render.digestMsg).Perm
      ((assignList q 0 (records (forestOldInputs (⟨original,replay,writes⟩::tail))
        (Candidates.ChainMetadata.assign cs 0 (initializeList 0
          (forestNodes 0 0 0 ((⟨original,replay,writes⟩::tail).map ReplayTree.pre)))))).flatMap postSlotDigests) := by
  rw [native_postSlot_inventory,forest_main_postDigests _ _ _ tail ht]
  exact native_rebased_account_digests h hr hpre hpost hkeys has

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
