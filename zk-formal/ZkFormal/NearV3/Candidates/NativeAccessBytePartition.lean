import ZkFormal.NearV3.Candidates.NativeAccessKeyTrace
import ZkFormal.NearV3.Candidates.NativeValueByteInventory

namespace ZkFormal.NearV3.Candidates.NativeAccessBytePartition
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra NativeAccessKeyProviders

def remaining (pre : PTrie) (writes : List (List Nat×Bytes)) : List Nat :=
  (List.range (NearSpecV3.valsOf pre).length).filter (fun i=>!(decide (i∈writtenValueIds pre writes)))

private theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  match xs with
  | []=>simp
  | a::xs=>
    rw [List.eraseDups_cons,List.nodup_cons]
    refine ⟨?_,eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem selected_remaining {pre : PTrie} {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    {i : Nat} (hi:i∈selected pre rs) : i∈remaining pre writes := by
  obtain ⟨r,_,_,_,hidx⟩:=selected_receipt hi
  exact NativeAccessByteOwnership.remaining_slot hw hidx

/-- Native selected IDs and indexed forest ownership enumerate exactly the
same providers once each, irrespective of repeated access receipts. -/
theorem selected_permutation {pre : PTrie} {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId)) :
    (selected pre rs).eraseDups.Perm
      ((remaining pre writes).filter (fun i=>decide (i∈selected pre rs))) := by
  apply (List.perm_ext_iff_of_nodup (eraseDups_nodup _)
    (((List.nodup_range).filter _).filter _)).2
  intro i
  simp only [List.mem_eraseDups,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun hi=>⟨by simpa only [remaining,List.mem_filter] using selected_remaining hw hi,hi⟩,fun hi=>hi.2⟩

theorem physical_split {pre : PTrie} {rs : List Receipt} {writes : List (List Nat×Bytes)}
    (hw:writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (hvalid:∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1)
    (tr : Trace Fp) (tk : Nat) (pub msg : List Fp)
    (ht:TableTraffic AkeyV3.interactions tr tk pub (akeyTraffic (providers pre rs))) :
    tableBusCount AkeyV3.interactions tr tk pub B_VBYTES true msg+
      cnt (((remaining pre writes).filter (fun i=>!(decide (i∈selected pre rs)))).flatMap
        (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg=
      cnt ((remaining pre writes).flatMap
        (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))) msg := by
  have hp:=List.Perm.flatMap_right
    (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))
    (selected_permutation (pre:=pre) hw)
  have hf:=List.Perm.flatMap_right
    (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat))
    (List.filter_append_perm (fun i=>decide (i∈selected pre rs)) (remaining pre writes))
  have hc:=(hp.map Msg.toFp).count_eq msg
  have hd:=(hf.map Msg.toFp).count_eq msg
  rw [(ht B_VBYTES msg).1]
  change cnt (akeySends (providers pre rs) B_VBYTES) msg+_= _
  rw [byte_inventory hvalid]
  simp only [List.flatMap_append,List.map_append,List.count_append,cnt] at hc hd ⊢
  omega

end ZkFormal.NearV3.Candidates.NativeAccessBytePartition
