import ZkFormal.NearV3.Candidates.ProcessRepairRecordParameters
import ZkFormal.NearV3.Candidates.ProcessRepairNativeIdReceived
import ZkFormal.NearV3.Candidates.ProcessRepairIdRequestRows
import ZkFormal.NearV3.Candidates.ProcessRepairRecordIdSource
import ZkFormal.NearV3.Candidates.ProcPriorRecordQueryMessage
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdRequestBounds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
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
    (hpub76:∀msg,pubCount AP pub 76 true msg=0)
    (hpub71:∀msg,pubCount AP pub 71 true msg=0)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {r:Nat} (hr:r<tr.height 0)
    (hstage:ZkFormal.Chacha.cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 1)=1)
    (hactive:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.act=1)
    (hquery:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.isPublic=0):
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.tau<33 ∧
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyLo<16777216 ∧
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyMid<16777216 ∧
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyHi<65536 := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:ProcessRepairIdRequestRows.requestRead∈AP.tables[0]!.interactions:=by
    rw [view.wires];exact ProcessRepairIdRequestRows.member
  have hm:=ProcessRepairIdRequestRows.live (pub:=pub) hstage hactive hquery
  obtain ⟨q,hq,hqm,hmsg⟩:=ProcessRepairRecordIdSource.source view hpub71 ht hr hi (by rfl) (by rfl) hm
  obtain ⟨f,bs,st,link,hfh,hff,htau,hbs,hd,hlink,hlo,hmid,hhi⟩:=ProcessRepairNativeIdQuery.limbs view
    hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubR hpubVP hq hqm
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨hqs,hqt,hqr⟩:=ProcPriorRecordQueryActivity.flags hv hq hqm
  have hqw:=ProcPriorRecordGeometry.words_bound hv hq hqs
  have haq:=ProcPriorRecordSound.flag hv hq hqs ProcPriorRecordTable.act (by simp)
  have hqa:ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.act=1:=by omega
  have hparam:=ProcessRepairRecordParameters.prepared_active_bounds view hpubS hpub76 I hprep fwd hrec hq hqs hqa
  have hmem:link∈st.links:=List.mem_of_getElem? hlink
  have hok:LinkOk link:=(ProcPriorDecode.decode_exact bs st hd).2.1 link hmem
  let key:=if ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.sender=1 then link.sender else link.receiver
  have hkey:key<18446744073709551616:=by
    dsimp only [key]
    split <;> exact (by rcases hok with ⟨h1,h2,h3⟩;assumption)
  have hb:=ProcPriorIdLimbs.bounds key hkey
  rw [ProcPriorRecordQueryMessage.message,hlo,hmid,hhi,ProcessRepairIdRequestRows.message] at hmsg
  have h0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  have h2:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  have h3:=congrArg (fun xs:List Fp=>xs[3]!.toNat) hmsg
  have h4:=congrArg (fun xs:List Fp=>xs[4]!.toNat) hmsg
  simp only [List.getElem!_cons_zero,List.getElem!_cons_succ,Fp.toNat_ofNat] at h0 h2 h3 h4
  have hpv:P=2013265921:=P_val
  have hc (c:Nat):ZkFormal.Chacha.cv (raw tr) 0 r c<P:=ZkFormal.Chacha.cv_lt _ _
  have hqcanon:ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau<P:=ZkFormal.Chacha.cv_lt _ _
  change ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau<33 ∧ _ at hparam
  change ProcPriorIdLimbs.lo key%P=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyLo%P at h2
  change ProcPriorIdLimbs.mid key%P=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyMid%P at h3
  change ProcPriorIdLimbs.hi key%P=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyHi%P at h4
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (hc _)] at h2 h3 h4
  change ZkFormal.Chacha.cv (raw tr) 0 q ProcPriorRecordTable.tau%P=ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.tau%P at h0
  rw [Nat.mod_eq_of_lt hqcanon,Nat.mod_eq_of_lt (hc _)] at h0
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairIdRequestBounds
