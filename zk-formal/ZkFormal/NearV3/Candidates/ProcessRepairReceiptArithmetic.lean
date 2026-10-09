import ZkFormal.NearV3.Candidates.ProcessRepairReceiptPayloadBytes
import ZkFormal.NearV3.Candidates.ProcessRepairMemoryLanes
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemory
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptArithmetic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof Link

/-- Native receipt arithmetic after actual ordered MEM and checked SHA traffic.
The initial account bytes and public gas-price bytes remain explicit here. -/
theorem arithmetic {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubM:∀seg∈AP.pubSegs,seg.bus≠B_MEM)
    (hpubB:∀msg,pubCount AP pub B_BYTES false msg=0)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    {as:List AcctV}
    (hm:ProcessRepairReceiptMemoryOrder.Context pub
      ((flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).map RcptE.toRcptV) as)
    (initial:∀a∈as,Bytes8 a.pre) (bgp:Bytes8 (pubBytes pub PH_GP 16)):
    let rs:=flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))
    ∃toks:List Nat,toks.length=rs.length+1 ∧ toks.head?=some 0 ∧
      ∀r,(hr:r<rs.length)→
      let x:=rs[r]
      Bytes8 x.bef ∧ Bytes8 x.lk ∧ Bytes8 x.st ∧
      leN' x.aft=leN' x.bef+leN' x.dep ∧ leN' x.aft<NearSpec.Params.u128Max ∧
      leN' x.aft+leN' x.lk<NearSpec.Params.two128 ∧
      ((NearSpec.Params.storageAmountPerByte*leN' x.st)%NearSpec.Params.two128≤leN' x.aft+leN' x.lk ∨
        leN' x.st≤NearSpec.Params.zeroBalanceStorageLimit) ∧
      x.ge=decide (leN' (pubBytes pub PH_GP 16)≤leN' x.gp) ∧
      leN' x.burnt=(if x.sys then 0 else NearSpec.Params.G*min (leN' x.gp) (leN' (pubBytes pub PH_GP 16))) ∧
      (x.hr=true↔x.sys=false ∧ NearSpec.Params.G*(leN' x.gp-min (leN' x.gp) (leN' (pubBytes pub PH_GP 16)))≠0) ∧
      (x.hr=true→leN' x.ramt=NearSpec.Params.G*(leN' x.gp-min (leN' x.gp) (leN' (pubBytes pub PH_GP 16)))) ∧
      toks.getD (r+1) 0=toks.getD r 0+leN' x.burnt ∧ toks.getD (r+1) 0<NearSpec.Params.two128:=by
  let rs:=flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))
  obtain ⟨toks,hlen,hhead,hw,_⟩:=ProcessRepairReceiptWf.tokens view hpubM hc
  refine ⟨toks,hlen,hhead,?_⟩
  intro r hr
  have w:=hw r hr
  have hr':r<(rs.map RcptE.toRcptV).length:=by simpa using hr
  obtain ⟨a,ha,hak⟩:=ProcessRepairMemoryLanes.slot_acct hm r hr'
  have hafter:∀q,(hq:q<(rs.map RcptE.toRcptV).length)→Bytes8 (rs.map RcptE.toRcptV)[q].aft:=by
    intro q hq
    simpa only [List.getElem_map] using (hw q (by simpa using hq)).aft8
  have lanes:=ProcessRepairMemoryLanes.lanes hm initial hafter r hr' a ha hak
  simp only [List.getElem_map] at lanes
  have lens:=w.lens
  have hb:Bytes8 rs[r].bef:=bytes8_of_getD lens.2.2.2.2.2.1 (fun i hi=>(lanes i hi).2.2)
  have hl:Bytes8 rs[r].lk:=by
    apply bytes8_of_getD lens.2.2.2.2.2.2.1
    intro i hi
    rw [(lanes i hi).1]
    exact getD_lt_of_bytes8 (initial a ha) _
  have hs:Bytes8 rs[r].st:=by
    apply bytes8_of_getD lens.2.2.2.2.2.2.2.1
    intro i hi
    rw [(lanes i hi).2.1]
    split
    · exact getD_lt_of_bytes8 (initial a ha) _
    · decide
  obtain ⟨hgp,hdep,hburnt,hramt⟩:=ProcessRepairReceiptPayloadBytes.payload view hpubB hc (List.getElem_mem hr)
  exact ⟨hb,hl,hs,w.arith bgp hgp hdep hb hl hs hburnt hramt⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptArithmetic
