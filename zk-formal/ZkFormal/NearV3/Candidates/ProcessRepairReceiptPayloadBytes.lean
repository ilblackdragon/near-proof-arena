import ZkFormal.NearV3.Candidates.ProcessRepairReceiptByteRange
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptCanon
import ZkFormal.Near.Link.Sha
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptPayloadBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof

theorem emitted {pub:List Fp} {ls:RcptV3Vs} {x:RcptE} (hx:x∈flatR ls)
    {y:Nat} (hy:y∈x.enc ∨ y∈x.peo ∨ (x.hr=true ∧ y∈x.encRefund)):
    ∃id pos,[id,pos,y]∈rcptSends3 pub ls B_BYTES:=by
  obtain ⟨L,hL,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨j,hj,hjL⟩:=List.mem_iff_getElem.mp hL
  obtain ⟨k,hk,hkx⟩:=List.mem_iff_getElem.mp hx
  have hl:ls.getD j default=L:=by rw [Link.getD_eq_getElem _ _ hj];exact hjL
  have hx:L.rs.getD k default=x:=by rw [Link.getD_eq_getElem _ _ hk];exact hkx
  have hloc:(baseR ls j+k,lOffs L.rs k,x)∈located ls j:=by
    unfold located
    rw [hl]
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,by rw [hx]⟩
  have he (id off:Nat) (bytes:List Nat) (hy:y∈bytes):
      ∃pos,[id,pos,y]∈emitAt id off bytes:=by
    obtain ⟨i,hi,hei⟩:=List.mem_iff_getElem.mp hy
    refine ⟨off+i,Link.mem_emitAt.mpr ⟨i,hi,?_⟩⟩
    rw [Link.getD_eq_getElem _ _ hi,hei]
  have hin {msg:Msg} (hm:msg∈rSends pub (flatR ls) j (baseR ls j+k) (lOffs L.rs k) x B_BYTES):
      msg∈rcptSends3 pub ls B_BYTES:=by
    unfold rcptSends3
    apply List.mem_flatMap.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_,hloc,hm⟩
  rcases hy with hy|hy|⟨hh,hy⟩
  · obtain ⟨pos,hp⟩:=he (msgId K_RC j) (lOffs L.rs k) x.enc hy
    exact ⟨msgId K_RC j,pos,hin (by simp [rSends,hp])⟩
  · obtain ⟨pos,hp⟩:=he (msgId K_PEO (baseR ls j+k)) 0 x.peo hy
    exact ⟨msgId K_PEO (baseR ls j+k),pos,hin (by simp [rSends,hp])⟩
  · obtain ⟨pos,hp⟩:=he K_RF (bOffs (flatR ls) (baseR ls j+k)) x.encRefund hy
    exact ⟨K_RF,pos,hin (by simp [rSends,hh,hp])⟩

theorem payload {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_BYTES false msg=0)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {x:RcptE} (hx:x∈flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))):
    Bytes8 x.gp ∧ Bytes8 x.dep ∧ Bytes8 x.burnt ∧ (x.hr=true→Bytes8 x.ramt):=by
  have hr:= (Assembly.ReceiptCandidateProof.ListChain.view_canon
    (Assembly.ReceiptCandidateProof.repaired_local_base (ProcessRepairForeignByteTags.local_receipt view)) hc).2 x hx
  have bounded (y:Nat) (hy:y∈x.toRcptV.raw)
      (he:y∈x.enc ∨ y∈x.peo ∨ (x.hr=true ∧ y∈x.encRefund)):y<256:=by
    have hcan:=hr y (by simp [RcptE.raw3,hy])
    obtain ⟨id,pos,hm⟩:=emitted hx he
    exact ProcessRepairReceiptByteRange.message view hpub hc hcan hm
  refine ⟨?_,?_,?_,?_⟩
  · intro y hy
    exact bounded y (by simp [RcptV.raw,hy]) (Or.inl (by simp [RcptV.enc,hy]))
  · intro y hy
    exact bounded y (by simp [RcptV.raw,hy]) (Or.inl (by simp [RcptV.enc,hy]))
  · intro y hy
    exact bounded y (by simp [RcptV.raw,hy]) (Or.inr (Or.inl (by simp [RcptV.peo,hy])))
  · intro hh y hy
    exact bounded y (by simp [RcptV.raw,hy]) (Or.inr (Or.inr ⟨hh,by simp [RcptV.encRefund,hy]⟩))
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptPayloadBytes
