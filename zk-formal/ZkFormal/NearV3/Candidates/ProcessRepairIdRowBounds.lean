import ZkFormal.NearV3.Candidates.ProcessRepairIdRequestBounds
import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicRow
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdRowBounds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
theorem active {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubD:∀msg,pubCount AP pub B_DIGEST true msg=0)
    (hpubB:∀msg,pubCount AP pub B_BYTES true msg=0)
    (hpubC:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (I:PubIdx AP pub Fp.ofNat) {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (h70:∀msg,pubCount AP pub 70 true msg=0)
    (hdl:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
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
    (hactive:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.act=1):
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.tau<33 ∧
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyLo<16777216 ∧
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyMid<16777216 ∧
    ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyHi<65536 := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hf:=ProcPriorVerticalIdRows.component_value hv hr hstage
    (ZkFormal.Chacha.Table.boolC ProcPriorIdTable.isPublic) (by simp [ProcPriorIdTable.constraints])
  have hb:ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.isPublic≤1:=Codec.bool_of_eval (pub:=pub) hf
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hq|hP
  · exact ProcessRepairIdRequestBounds.bounds view hpubS hpubL hpubV hpubD hpubB hpubC I hprep fwd hrec
      hNW hVW hN hV hw hchain hK hU hpubR hpub76 hpub71 hpubVP hr hstage hactive hq
  · obtain ⟨ht,hj,hl,hm,hh⟩:=ProcessRepairIdPublicRow.authenticated view hpubS h70 I hprep sp hsp fwd hdl hrec hr hstage hactive hP
    change ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.ordinal<sp.ids.length at hj
    change ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyLo=ProcPriorIdLimbs.lo (sp.ids.getD (ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.ordinal) 0) at hl
    change ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyMid=ProcPriorIdLimbs.mid (sp.ids.getD (ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.ordinal) 0) at hm
    change ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.keyHi=ProcPriorIdLimbs.hi (sp.ids.getD (ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.ordinal) 0) at hh
    have hid:sp.ids.getD (ZkFormal.Chacha.cv (raw tr) 0 r ProcPriorIdTable.ordinal) 0<18446744073709551616:=by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
      exact prepD0_ids64 hprep sp hsp _ (List.getElem_mem hj)
    have hb:=ProcPriorIdLimbs.bounds _ hid
    exact ⟨ht,by rw [hl];exact hb.1,by rw [hm];exact hb.2.1,by rw [hh];exact hb.2.2⟩
end ZkFormal.NearV3.Candidates.ProcessRepairIdRowBounds
