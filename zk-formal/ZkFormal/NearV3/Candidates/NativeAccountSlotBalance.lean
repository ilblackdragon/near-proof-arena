import ZkFormal.NearV3.Candidates.NativeAccountTrace
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedNativeAccountDigest

namespace ZkFormal.NearV3.Candidates.NativeAccountSlotBalance
open ZkFormal.Near Render ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

private def slotOf (m : ZkFormal.Near.Msg) : ZkFormal.Near.Msg := [m.getD 0 0 / 16]

theorem account_slots (as : List AcctV) :
    ((accountShaJobs as).map Render.digestMsg).map slotOf=acctV3Sends as B_VSLOT := by
  simp [accountShaJobs,Render.digestMsg,slotOf,acctV3Sends,B_VSLOT,B_VBYTES,B_BYTES,B_MEM,
    List.map_map,msgId,K_VPOST]
  intro a _;omega

theorem node_slots (ns : List NodeS3) :
    (ns.flatMap postSlotDigests).map slotOf=nodeRecvs3 ns B_VSLOT := by
  have hz:=List.map_fst_zip (by simp : ns.length≤(List.range ns.length).length)
  let f:=fun s : NodeS3=>match s.v.value with | some (i,_,_,_,true)=>[[i]] | _=>[]
  have he:=congrArg (List.flatMap f) hz
  simp only [List.flatMap_map] at he
  change _=(ns.zip (List.range ns.length)).flatMap (fun p=>f p.1)
  rw [he]
  rw [List.map_flatMap]
  apply Render.flatMap_congr'
  intro s _
  unfold postSlotDigests f
  cases hv:s.v.value with
  | none => rfl
  | some v =>
    rcases v with ⟨i,l,pre,post,w⟩
    cases w <;> simp [slotOf,digMsg,msgId,K_VPOST]
    omega

/-- Natural digest multiplicity implies exact slot ownership; projection occurs
before field encoding, so no field-division or injectivity premise is used. -/
theorem physical (as : List AcctV) (ns : List NodeS3) (trA : Trace Fp)
    (tA tn : Nat) (pub msg : List Fp) (hn : NodeOk ns)
    (ha : TableTraffic AccountEmpty.table.interactions trA tA pub (acctV3Traffic as))
    (hp : ((accountShaJobs as).map Render.digestMsg).Perm (ns.flatMap postSlotDigests)) :
    tableBusCount AccountEmpty.table.interactions trA tA pub B_VSLOT true msg=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_VSLOT false msg := by
  have he:=hp.map slotOf
  rw [account_slots,node_slots] at he
  rw [(ha B_VSLOT msg).1,TrieCountTraffic.node_non_size ns pub tn B_VSLOT false msg (by decide),
    ((TrieHeight.node_complete ns hn tn pub).2.1 B_VSLOT msg).2]
  exact (he.map Msg.toFp).count_eq msg

end ZkFormal.NearV3.Candidates.NativeAccountSlotBalance
