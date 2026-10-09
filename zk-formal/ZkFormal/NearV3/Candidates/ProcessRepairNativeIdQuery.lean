import ZkFormal.NearV3.Candidates.ProcessRepairNativeTopWord
import ZkFormal.NearV3.Candidates.ProcPriorRecordQueryActivity
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeIdQuery
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem limbs {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubD:∀msg,pubCount AP pub B_DIGEST true msg=0)
    (hpubB:∀msg,pubCount AP pub B_BYTES true msg=0)
    (hpubC:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (I:PubIdx AP pub Fp.ofNat) {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {vs:List NodeS3} {es:List ValE}
    (hNW:NodeWf3 vs) (hVW:ValWf es)
    (hN:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {v:List UpsSeg} (hw:Render.UpsRelay.Extract.Wf v) {hs:List HeadE} {K:Nat} {r0 rK:List Nat}
    (hchain:RootChain hs (v.map UpsRows.upsE) K r0 rK) (hK:K<33)
    (hU:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v))
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {r:Nat} (hr:r<tr.height 0)
    (hm:ProcPriorRecordQueryActivity.query.multNat (raw tr) 0 r pub≠0) :
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.record]?=some link ∧
      ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.lo=ProcPriorIdLimbs.lo (if ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.sender=1 then link.sender else link.receiver) ∧
      ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.mid=ProcPriorIdLimbs.mid (if ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.sender=1 then link.sender else link.receiver) ∧
      ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.hi=ProcPriorIdLimbs.hi (if ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.sender=1 then link.sender else link.receiver) := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨hs,htop,hwords⟩:=ProcPriorRecordQueryActivity.flags hv hr hm
  obtain ⟨f,bs,st,link,hfh,hff,htau,hbs,hd,hlink,hlo,hmid,hhi⟩:=ProcessRepairNativeTopWord.limbs view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hr hs htop
  have he:ProcPriorRecordNativeField.selected (raw tr) 0 r link=
      (if ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.sender=1 then link.sender else link.receiver):=by
    unfold ProcPriorRecordNativeField.selected
    by_cases hsend:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.sender=1
    · simp [hsend]
    · have hrecv:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.receiver=1:=by omega
      simp [hsend,hrecv]
  rw [he] at hlo hmid hhi
  exact ⟨f,bs,st,link,hfh,hff,htau,hbs,hd,hlink,hlo,hmid,hhi⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeIdQuery
