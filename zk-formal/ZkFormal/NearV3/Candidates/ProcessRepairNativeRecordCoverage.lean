import ZkFormal.NearV3.Candidates.ProcessRepairNativeRecords
import ZkFormal.NearV3.Candidates.ProcessRepairRecordCoverage
import ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteField
import ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteCoverage
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeRecordCoverage
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
      ∀k,∀link:NearSpec.Bandwidth.LinkAllowance,st.links[k]?=some link→
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
             ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (ProcPriorCodecFamilyLastWrite.memory tr) 0 w ProcPriorMemoryTable.hi=1)) := by
  obtain ⟨bs,st,hbs,hd,hcount,_⟩:=ProcessRepairNativeRecords.records view hpubS hpubL hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP hr hs hf hp
  refine ⟨bs,st,hbs,hd,?_⟩
  intro k link hlink
  have hk:k<ZkFormal.Chacha.cv (raw tr) 0 r count:=by
    have h: k<st.links.length:=(List.getElem?_eq_some_iff.mp hlink).1
    omega
  obtain ⟨q,hq,hqs,hqa,hqt,hqtau,hqk⟩:=ProcessRepairRecordCoverage.frame view hpub75 hr hs hf k hk
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨a,haq,ha,has,haf⟩:=ProcPriorRecordBackwardBoundary.top_origin hv hq hqs hqt
  have h75:∀msg,pubCount AP pub 75 true msg=0:=by
    intro msg
    exact ZkFormal.Chacha.pubCount_zero (fun seg hseg hb=>absurd hb (hpub75 seg hseg)) msg
  obtain ⟨f,cs,su,lu,hfh,hfs,hff,hft,hcs,hdu,hlu,_,hlo,hbig,hfair⟩:=ProcessRepairNativeWord.word view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU h75 hpubVP ha has haf
  have hid:=ProcPriorRecordWordIdentity.limb_identity hv ha has haf 2 (by decide)
  rw [←haq] at hid
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  have hfr:f=r:=ProcPriorRawTauUnique.first_unique hv hh hfh hr hfs hs hff hf (hft.trans (hid.1.symm.trans hqtau))
  have hbytes:cs.map UInt8.toNat=bs.map UInt8.toNat:=by rw [hcs,hbs,hfr]
  have hstate:su=st:=ProcPriorDecodedIdentity.state cs bs su st hbytes hdu hd
  have hak:ZkFormal.Chacha.cv (raw tr) 0 a ProcPriorRecordTable.record=k:=hid.2.symm.trans hqk
  rw [hstate,hak] at hlu
  have hle:lu=link:=Option.some.inj (hlu.symm.trans hlink)
  have hselected:=ProcessRepairNativeWriteField.selected_allowance hv ha has haf (by rw [←haq];exact hqa) lu
  rw [hselected,hle,←haq] at hlo hbig hfair
  refine ⟨q,hq,hqs,hqa,hqt,hqtau,hqk,hlo,hbig,hfair,?_⟩
  intro hsf hrf
  obtain ⟨w,hw0,hwa,hwq,hwt,hwlink,hwk,hwl,hwh⟩:=ProcessRepairRecordWriteCoverage.emitted view hpub67 hq hqs hqa hqt hsf hrf
  exact ⟨w,hw0,hwa,hwq,hwt.trans hqtau,hwlink,hwk.trans hqk,hlo.trans hwl.symm,by rw [hwh];exact hbig⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeRecordCoverage
