import ZkFormal.NearV3.Candidates.ProcessRepairNativeIdReceived
import ZkFormal.NearV3.Candidates.ProcessRepairIdRequestRows
import ZkFormal.NearV3.Candidates.ProcessRepairRecordIdSource
import ZkFormal.NearV3.Candidates.ProcPriorRecordQueryMessage
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdRequestNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
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
    (hpub71:∀msg,pubCount AP pub 71 true msg=0)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {r:Nat} (hr:r<tr.height 0)
    (hstage:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 1)=1)
    (hactive:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.act=1)
    (hquery:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.isPublic=0):
    ∃q f,∃bs:NearSpec.Bytes,∃st:NearSpec.Bandwidth.State,∃link:NearSpec.Bandwidth.LinkAllowance,
      q<tr.height 0 ∧ f<tr.height 0 ∧ ZkFormal.Chacha.cv (raw tr) 0 f first=1 ∧
      ZkFormal.Chacha.cv (raw tr) 0 f tau=ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau ∧
      bs.map UInt8.toNat=(es[ZkFormal.Chacha.cv (raw tr) 0 f vid]!).bytes ∧
      NearSpec.Bandwidth.State.decode bs=some st ∧
      st.links[ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.record]?=some link ∧
      ProcessRepairIdRequestRows.requestRead.msgVal tr 0 r pub=
        [Fp.ofNat (ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau),
         Fp.ofNat (2*ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.record+ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.receiver),
         Fp.ofNat (ProcPriorIdLimbs.lo (if ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.sender=1 then link.sender else link.receiver)),
         Fp.ofNat (ProcPriorIdLimbs.mid (if ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.sender=1 then link.sender else link.receiver)),
         Fp.ofNat (ProcPriorIdLimbs.hi (if ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.sender=1 then link.sender else link.receiver))] := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:ProcessRepairIdRequestRows.requestRead∈AP.tables[0]!.interactions:=by
    rw [view.wires];exact ProcessRepairIdRequestRows.member
  exact ProcessRepairNativeIdReceived.received view hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec
    hNW hVW hN hV hw hchain hK hU hpubR hpub71 hpubVP ht hr hi (by rfl) (by rfl)
    (ProcessRepairIdRequestRows.live hstage hactive hquery)
end ZkFormal.NearV3.Candidates.ProcessRepairIdRequestNative
