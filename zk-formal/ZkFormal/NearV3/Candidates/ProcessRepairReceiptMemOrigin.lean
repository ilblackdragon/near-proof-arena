import ZkFormal.NearV3.Candidates.ProcessRepairReceiptWf
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof

theorem send_origin {pub:List Fp} {ls:RcptV3Vs} {m:Msg}
    (hm:m∈rcptSends3 pub ls B_MEM):
    ∃r,r<(flatR ls).length ∧ m.getD 1 0=r+1 ∧ m.getD 0 0=((flatR ls).getD r default).kslot:=by
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
  refine ⟨baseR ls j+k,by omega,rfl,?_⟩
  rw [ProcessRepairReceiptKeyOwner.flat_lookup ls hj k hk]
  rfl

theorem account_origin (as:List AcctV) {m:Msg} (hm:m∈acctV3Sends as B_MEM):
    ∃a∈as,m.getD 1 0=0 ∧ m.getD 0 0=a.k:=by
  simp only [acctV3Sends,show B_MEM≠B_VBYTES by decide,show B_MEM≠B_BYTES by decide,
    ite_false,ite_true,List.mem_flatMap,List.mem_map] at hm
  obtain ⟨a,ha,i,hi,rfl⟩:=hm
  exact ⟨a,ha,rfl,rfl⟩

theorem predecessor {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {as:List AcctV} (hwa:as=[] ∨ AcctV3Wf as)
    (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as))
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (r:Nat) (hr:r<(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length):
    let rs:=flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))
    (∃a∈as,a.k=rs[r].kslot) ∨ (∃j,j<r ∧ ∃hj:j<rs.length, rs[j].kslot=rs[r].kslot):=by
  let rs:=flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))
  let x:=rs[r]
  have hx:x∈rs:=List.getElem_mem hr
  obtain ⟨toks,_,_,hw,_⟩:=ProcessRepairReceiptWf.tokens view hpub hc
  have hsmall:=(hw r hr).small
  have hprev:=ProcessRepairReceiptWf.previous_le view hpub hc r hr
  have hcount:=ProcessRepairReceiptWf.count_bound view hc
  have hperm:=ProcessRepairReceiptMemProvider.permutation view hpub ha hc
  let msg:Msg:=[x.kslot,x.tprev,0,x.bef.getD 0 0,x.lk.getD 0 0,x.st.getD 0 0]
  have hm:msg∈rcptRecvs3 (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)) B_MEM:=by
    rw [Assembly.ReceiptCandidateProof.memoryReadMsgs_view]
    exact List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨0,by decide,rfl⟩⟩
  obtain ⟨m,hm,he⟩:=List.mem_map.mp (hperm.mem_iff.mpr
    (List.mem_map.mpr ⟨msg,List.mem_append_left _ hm,rfl⟩))
  have htime:=congrArg (fun xs:List Fp=>xs.getD 1 0) he
  have hslot:=congrArg (fun xs:List Fp=>xs.getD 0 0) he
  change (m.map Fp.ofNat).getD 1 (Fp.ofNat 0)=Fp.ofNat x.tprev at htime
  change (m.map Fp.ofNat).getD 0 (Fp.ofNat 0)=Fp.ofNat x.kslot at hslot
  rw [Link3.getD_map'] at htime hslot
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨j,hj,ht,hk⟩:=send_origin hm
    rw [ht] at htime
    have htimeNat:j+1=x.tprev:=Link.ofNat_inj (by unfold P;omega) hsmall.2.1 htime
    have hjr:j<r:=by change x.tprev≤r at hprev;omega
    have hjrs:j<rs.length:=hj
    have hget:rs.getD j default=rs[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hjrs]
    change m.getD 0 0=(rs.getD j default).kslot at hk
    rw [hk,hget] at hslot
    have heq:rs[j].kslot=x.kslot:=Link.ofNat_inj (hw j hj).small.1 hsmall.1 hslot
    exact Or.inr ⟨j,hjr,hj,heq⟩
  · obtain ⟨a,ham,ht,hk⟩:=account_origin as hm
    have haw:AcctV3Wf as:=by
      rcases hwa with rfl|haw
      · simp at ham
      · exact haw
    rw [hk] at hslot
    exact Or.inl ⟨a,ham,Link.ofNat_inj (haw.v1.len a ham).2.2.1 hsmall.1 hslot⟩

theorem slots {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    {as:List AcctV} (hwa:as=[] ∨ AcctV3Wf as)
    (ha:TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as))
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e):
    ∀r,(hr:r<(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length)→
      ∃a∈as,a.k=(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)))[r].kslot:=by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih=>
    intro hr
    rcases predecessor view hpub hwa ha hc r hr with ha|⟨j,hjr,hj,he⟩
    · exact ha
    · obtain ⟨a,ha,hk⟩:=ih j hjr hj
      exact ⟨a,ha,hk.trans he⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemOrigin
