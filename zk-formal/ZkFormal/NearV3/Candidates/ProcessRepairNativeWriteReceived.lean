import ZkFormal.NearV3.Candidates.ProcessRepairNativeWrite
import ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteReceived
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem received {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubW:∀msg,pubCount AP pub 67 true msg=0)
    {tc rr:Nat} (ht:tc<AP.tables.length) (hr:rr<tr.height tc) {i:Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=67) (hsend:i.send=false)
    (hm:i.multNat tr tc rr pub≠0) :
    ∃r,r<tr.height 0 ∧
      ProcPriorRoutedFamilyWrite.verticalWrite.msgVal (raw tr) 0 r pub=i.msgVal tr tc rr pub ∧
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.record]?=some link ∧
            ProcPriorSummary.low (link.allowance)=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.lo ∧
      ProcPriorSummary.big (link.allowance)=decide (ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.big=1) ∧
      ∀fair:Nat,(if ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.big=1 then 4500000 else min (ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorRecordTable.lo+fair) 4500000)=
        min (min (link.allowance+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  obtain ⟨r,hr,hs,hgate,hmsg,_⟩:=ProcessRepairFamilyWrite.family_write_source view hpubW ht hr hi hb hsend hm
  refine ⟨r,hr,hmsg,?_⟩
  exact ProcessRepairNativeWrite.write view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hr hs hgate
end ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteReceived
