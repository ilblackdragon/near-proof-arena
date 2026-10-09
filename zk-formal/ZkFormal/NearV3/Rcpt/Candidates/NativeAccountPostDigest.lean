import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountJobPermutation
import ZkFormal.NearV3.Rcpt.Candidates.NativePostDigestForest
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly

theorem postDigestFrom_indexed (u : Inputs) (i : Nat) (bs : List Bytes) :
    postDigestFrom u i bs=(List.range bs.length).flatMap (fun j=>
      match u.value (i+j) with
      | none=>[]
      | some post=>[digMsg (msgId K_VPOST (i+j)) (bs.getD j []).length (digest post)]) := by
  induction bs generalizing i with
  | nil=>rfl
  | cons b bs ih=>
    simp only [postDigestFrom,ih,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
      List.flatMap_map,Nat.add_zero,List.getD_cons_zero]
    congr 1
    apply ZkFormal.Near.Render.flatMap_congr'
    intro j hj
    simp [Function.comp_apply,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem flatMap_filter_single (xs : List Nat) (p : Nat→Bool) (f : Nat→ZkFormal.Near.Msg) :
    xs.flatMap (fun i=>if p i then [f i] else [])=(xs.filter p).map f := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>cases hp:p x <;> simp [hp,ih]

theorem oldTreeInputs_digest_inventory {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (hr:SizedAccountRun pre writes post) :
    postDigestFrom (oldTreeInputs pre post writes) 0 (NearSpecV3.valsOf pre)=
      (((List.range (NearSpecV3.valsOf pre).length).filter
        (fun i=>decide (i∈writtenValueIds pre writes))).map
          (fun j=> (⟨msgId K_VPOST j,((NearSpecV3.valsOf post).getD j []).map UInt8.toNat⟩ : Render.Msg))).map Render.digestMsg := by
  rw [postDigestFrom_indexed]
  rw [List.map_map,←flatMap_filter_single]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro j hj
  have hjb:j<(NearSpecV3.valsOf pre).length:=List.mem_range.mp hj
  let before:Bytes:=(NearSpecV3.valsOf pre)[j]
  have hbefore:(NearSpecV3.valsOf pre)[j]?=some before:=List.getElem?_eq_some_iff.mpr ⟨hjb,rfl⟩
  have hlen:=hr.value_lengths
  rw [←Assembly.native_valsOf_eq,←Assembly.native_valsOf_eq] at hlen
  have hget:=congrArg (fun xs : List Nat=>xs[j]?) hlen
  simp only [List.getElem?_map,hbefore,Option.map_some] at hget
  cases ha:(NearSpecV3.valsOf post)[j]? with
  | none=>simp [ha] at hget
  | some after=>
    have hl:after.length=before.length:=by simpa [ha] using hget
    by_cases hactive:j∈writtenValueIds pre writes
    · simp [oldTreeInputs,hactive,←Assembly.native_valsOf_eq,ha,Nat.zero_add,
        List.getD_eq_getElem?_getD,hbefore,Function.comp_apply,
        Render.digestMsg,Render.shaN,Render.ofNats,Render.toNats,digMsg,digest,
        List.map_map,Function.comp_def,UInt8.ofNat_toNat,hl]
    · simp [oldTreeInputs,hactive]

theorem native_rebased_account_digests {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {original replay : PTrie} {writes : List (List Nat×Bytes)}
    (hr:SizedAccountRun original writes replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    (hkeys:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as) :
    ((accountShaJobs as).map Render.digestMsg).Perm
      (postDigestFrom (oldTreeInputs original replay writes) 0 (NearSpecV3.valsOf original)) := by
  rw [oldTreeInputs_digest_inventory hr]
  exact (native_rebased_account_jobs h hr.forget.skeleton hpre hpost hkeys has).map _

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
