import ZkFormal.NearV3.Candidates.ProcessRepairReceiptWalkKey
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptIds
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open RcptV3Proof

theorem receiver {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) {bs:List ListBlock} {e:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {x:RcptE} (hx:x∈flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))):
    Bytes8 x.v ∧ 2≤x.v.length ∧ x.v.length≤64 ∧ x.kslot<P:=by
  obtain ⟨L,hL,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨B,hB,rfl⟩:=List.mem_map.mp hL
  change x∈B.receipts.map (rcptOf (ProcPriorRoutedReceiptView.receipt tr) 0) at hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  have hlocal:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  have hlayout:=(hc.blocks B hB).layouts y hy
  have hi:=Assembly.ReceiptCandidateProof.ids_of hlocal hlayout
  have hvalid:=hi.2.1
  simp only [NearSpec.AccountId.valid,Bool.and_eq_true,decide_eq_true_eq,toBytes,List.length_map] at hvalid
  refine ⟨hi.2.2.2.2.1,hvalid.1.1,hvalid.1.2,?_⟩
  exact (Assembly.ReceiptCandidateProof.small_of _ _ y).1

theorem native_key (x:RcptE) (hb:Bytes8 x.v) (hn:x.v.length≤64):
    x.keySyms.length<P ∧ (∀a∈x.keySyms,a<P) ∧
      x.keySyms.take (x.keySyms.length-1)=NearSpec.accountKeyPath (toBytes x.v):=by
  have he:=Link.keySyms_eq x.toRcptV hb
  have hlen:=Link.keySyms_length x.toRcptV
  refine ⟨by unfold P;omega,?_,?_⟩
  · exact Link.keySyms_lt x.toRcptV (fun a ha=>Nat.lt_trans (hb a ha) (by decide))
  · rw [he]
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_sub_cancel]
    simp
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape
