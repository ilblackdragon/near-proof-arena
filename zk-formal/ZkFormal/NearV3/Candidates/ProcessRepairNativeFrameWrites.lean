import ZkFormal.NearV3.Candidates.ProcessRepairNativeRecordCoverage
import ZkFormal.NearV3.Candidates.ProcessRepairNativeMemoryWrite
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeFrameWrites
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem frame {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    (hpub75:∀seg∈AP.pubSegs,seg.bus≠75)
    (hpub67:∀seg∈AP.pubSegs,seg.bus≠67)
    {r:Nat} (hr:r<tr.height 0)
    (hs:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:ZkFormal.Chacha.cv (raw tr) 0 r first=1) (hp:ZkFormal.Chacha.cv (raw tr) 0 r present=1) :
    ∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 r vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      (∀k,∀link:NearSpec.Bandwidth.LinkAllowance,st.links[k]?=some link→
        ∃q,q<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
          ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.amount=1 ∧
          ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.topLimb=1 ∧
          ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau=ZkFormal.Chacha.cv (raw tr) 0 r tau ∧
          ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.record=k ∧
          ProcPriorSummary.low link.allowance=ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.lo ∧
          ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.big=1) ∧
          (∀fair:Nat,(if ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.big=1 then 4500000 else min (ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.lo+fair) 4500000)=
            min (min (link.allowance+fair) NearSpecV3.Scheduler.u64Max) 4500000) ∧
          (ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.senderFound=1→
           ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.receiverFound=1→
           ∃w,w<tr.height 0 ∧ ProcPriorVerticalLastWrite.Live (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ∧
             ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.query=0 ∧
             ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.tau=ZkFormal.Chacha.cv (raw tr) 0 r tau ∧
             ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.link=(ProcPriorRecordTable.link.eval (raw tr) 0 q pub).toNat ∧
             ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.stamp=k ∧
             ProcPriorSummary.low link.allowance=ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.lo ∧
             ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.hi=1)) ) ∧
      ∀w,w<tr.height 0→ProcPriorVerticalLastWrite.Live (ProcPriorCodecFamilyLastWrite.memory tr) 0 w→
        ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.query=0→
        ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.tau=ZkFormal.Chacha.cv (raw tr) 0 r tau→
        ∃link:NearSpec.Bandwidth.LinkAllowance,
          st.links[ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.stamp]?=some link ∧
          ProcPriorSummary.low link.allowance=ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.lo ∧
          ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.hi=1) ∧
          ∀fair:Nat,(if ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.hi=1 then 4500000 else min (ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.lo+fair) 4500000)=
            min (min (link.allowance+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  obtain ⟨bs,st,hbs,hd,hcoverage⟩:=ProcessRepairNativeRecordCoverage.frame view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hpub75 hpub67 hr hs hf hp
  refine ⟨bs,st,hbs,hd,hcoverage,?_⟩
  intro w hwh hwa hwq hwt
  have h75:∀msg,pubCount AP pub 75 true msg=0:=fun msg=>
    ZkFormal.Chacha.pubCount_zero (fun seg hseg hb=>absurd hb (hpub75 seg hseg)) msg
  have h67:∀msg,pubCount AP pub 67 true msg=0:=fun msg=>
    ZkFormal.Chacha.pubCount_zero (fun seg hseg hb=>absurd hb (hpub67 seg hseg)) msg
  obtain ⟨f,cs,su,link,hfh,hfs,hff,hft,hcs,hdu,hlink,hlo,hbig,hfair⟩:=ProcessRepairNativeMemoryWrite.row view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU h75 hpubVP h67 hwh hwa hwq
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  have hfr:f=r:=ProcPriorRawTauUnique.first_unique (ProcessRepairRawBytes.overlay_local view) hh hfh hr hfs hs hff hf (hft.trans hwt)
  have hbytes:cs.map UInt8.toNat=bs.map UInt8.toNat:=by rw [hcs,hbs,hfr]
  have hstate:su=st:=ProcPriorDecodedIdentity.state cs bs su st hbytes hdu hd
  rw [hstate] at hlink
  exact ⟨link,hlink,hlo,hbig,hfair⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeFrameWrites
