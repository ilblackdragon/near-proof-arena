import ZkFormal.NearV3.Candidates.ProcessRepairNativeWriteReceived
import ZkFormal.NearV3.Candidates.ProcessRepairWriteStamp
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeMemoryWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorCodecFamilyLastWrite (memory)
theorem row {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    {r:Nat} (hr:r<tr.height 0)
    (ha:ProcPriorVerticalLastWrite.Live (memory tr) 0 r)
    (hq:ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.query=0):
    ∃f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.stamp]?=some link ∧
      ProcPriorSummary.low link.allowance=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.lo ∧
      ProcPriorSummary.big link.allowance=decide (ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.hi=1) ∧
      ∀fair:Nat,(if ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.hi=1 then 4500000 else min (ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.lo+fair) 4500000)=
        min (min (link.allowance+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:ProcPriorRoutedWriteStamp.write∈AP.tables[0]!.interactions:=by rw [view.wires];exact ProcPriorRoutedWriteStamp.write_member
  obtain ⟨q,hqh,hmsg,f,bs,st,link,hfh,hff,htau,hbs,hd,hlink,hlo,hbig,hfair⟩:=ProcessRepairNativeWriteReceived.received view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hpubW
    ht hr hi (show ProcPriorRoutedWriteStamp.write.bus=67 from rfl) (show ProcPriorRoutedWriteStamp.write.send=false from rfl)
    (ProcPriorRoutedWriteStamp.write_live ha hq)
  rw [ProcPriorRoutedWriteStamp.write_message] at hmsg
  have he0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  have he2:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  have he3:=congrArg (fun xs:List Fp=>xs[3]!.toNat) hmsg
  have he4:=congrArg (fun xs:List Fp=>xs[4]!.toNat) hmsg
  change ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.tau at he0
  change ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.record=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.stamp at he2
  change ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.lo=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.lo at he3
  change ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.big=ZkFormal.Chacha.cv (memory tr) 0 r ProcPriorMemoryTable.hi at he4
  rw [he2] at hlink
  rw [he3] at hlo
  rw [he4] at hbig
  rw [he3,he4] at hfair
  exact ⟨f,bs,st,link,hfh,hff,htau.trans he0,hbs,hd,hlink,hlo,hbig,hfair⟩
end ZkFormal.NearV3.Candidates.ProcessRepairNativeMemoryWrite
