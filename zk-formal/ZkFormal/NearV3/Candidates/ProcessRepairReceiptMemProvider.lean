import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemBalance
import ZkFormal.NearV3.Candidates.ProcessRepairAccountView
import ZkFormal.NearV3.Assembly.RcptCandidateTableTraffic
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemProvider
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof

theorem send_time {pub:List Fp} {ls:RcptV3Vs} {m:Msg}
    (hm:m∈rcptSends3 pub ls B_MEM):m.getD 1 0≤(flatR ls).length:=by
  simp only [rcptSends3,show B_MEM≠B_BYTES by decide,show B_MEM≠B_RCL by decide,
    ite_false,List.nil_append] at hm
  obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hm
  have hj:=List.mem_range.mp hj
  obtain ⟨⟨r,off,x⟩,hp,hm⟩:=List.mem_flatMap.mp hm
  have hget:ls.getD j default=ls[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  simp only [located,hget,List.mem_map,List.mem_range] at hp
  obtain ⟨k,hk,hp⟩:=hp
  cases hp
  simp only [rSends,show B_MEM≠B_BYTES by decide,show B_MEM≠B_KEYNIB by decide,
    ite_false,ite_true,List.mem_map] at hm
  obtain ⟨i,hi,rfl⟩:=hm
  have hh:=RcptLink.located_index_bound ls hj
  simp only [List.getD_cons_succ,List.getD_cons_zero]
  omega

theorem account_time (as:List AcctV) {m:Msg} (hm:m∈acctV3Sends as B_MEM):m.getD 1 0=0:=by
  simp only [acctV3Sends,show B_MEM≠B_VBYTES by decide,show B_MEM≠B_BYTES by decide,
    ite_false,ite_true,List.mem_flatMap,List.mem_map] at hm
  obtain ⟨a,ha,i,hi,rfl⟩:=hm
  rfl

theorem permutation {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {as:List AcctV} (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as))
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e):
    ((rcptSends3 pub (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_MEM ++
      acctV3Sends as B_MEM).map Msg.toFp).Perm
    ((rcptRecvs3 (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_MEM ++
      acctRecvs as B_MEM).map Msg.toFp):=by
  have hL:=Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)
  have hr:=Assembly.ReceiptCandidateProof.ListChain.view_traffic hL hc
  apply List.perm_iff_count.mpr
  intro msg
  have h:=ProcessRepairReceiptMemBalance.balance view hpub msg
  rw [(ha _ _).1,(ha _ _).2,(hr _ _).1,(hr _ _).2] at h
  simpa only [rcptTraffic3,acctV3Traffic,List.map_append,List.count_append] using h

theorem previous_canon {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) {bs:List ListBlock} {e:Nat}
    (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {x:RcptE} (hx:x∈flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))):x.tprev<P:=by
  obtain ⟨L,hL,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨B,hB,rfl⟩:=List.mem_map.mp hL
  change x∈B.receipts.map (rcptOf (ProcPriorRoutedReceiptView.receipt tr) 0) at hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  exact (Assembly.ReceiptCandidateProof.small_of _ _ y).2.1

theorem previous {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {x:RcptE} (hx:x∈flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))):
    x.tprev≤(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length:=by
  obtain ⟨as,_,ha⟩:=ProcessRepairAccountView.accounts view
  have hp:=permutation view hpub ha hc
  let msg:Msg:=[x.kslot,x.tprev,0,x.bef.getD 0 0,x.lk.getD 0 0,x.st.getD 0 0]
  have hm:msg∈rcptRecvs3 (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_MEM:=by
    rw [Assembly.ReceiptCandidateProof.memoryReadMsgs_view]
    apply List.mem_flatMap.mpr
    refine ⟨x,hx,List.mem_map.mpr ⟨0,by decide,rfl⟩⟩
  have hsend:=hp.mem_iff.mpr (List.mem_map.mpr ⟨msg,List.mem_append_left _ hm,rfl⟩)
  obtain ⟨m,hm,he⟩:=List.mem_map.mp hsend
  have htime:=congrArg (fun xs:List Fp=>(xs.getD 1 0).toNat) he
  change ((m.map Fp.ofNat).getD 1 (Fp.ofNat 0)).toNat=(Fp.ofNat x.tprev).toNat at htime
  rw [Link3.getD_map',Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (previous_canon view hc hx)] at htime
  rcases List.mem_append.mp hm with hm|hm
  · have hbound:=send_time hm
    have hmod:=Nat.mod_le (m.getD 1 0) P
    omega
  · rw [account_time as hm] at htime
    simp only [Nat.zero_mod] at htime
    omega
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemProvider
