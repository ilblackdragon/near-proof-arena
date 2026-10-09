import ZkFormal.NearV3.Candidates.ProcessRepairAccountComplete
import ZkFormal.NearV3.Candidates.ProcessRepairValueRange
import ZkFormal.Near.Link.RunAcc
namespace ZkFormal.NearV3.Candidates.ProcessRepairAccountNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Sched Link3

theorem authenticated {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
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
    (hHeadW:HeadWf hs) (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    (hpubP:∀seg∈AP.pubSegs,seg.bus≠B_PARENT)
    (hpubVP:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    : ∃as:List AcctV,(as=[] ∨ AcctV3Wf as) ∧
      TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as) ∧
      ∀a∈as,∃e∈es,e.vz=false ∧ e.vid=a.k ∧ e.bytes=a.pre ∧
        e.bytes.length=72 ∧ NearSpec.Account.decode (toBytes e.bytes)=some (Link.accOf a) := by
  obtain ⟨as,haw0,ha⟩:=ProcessRepairAccountView.accounts view
  have hb:=ProcessRepairValueRange.bytes view hpubS hpubV hpubD hpubB hpubC
    I hprep fwd hrec hNW hVW hN hV hw hchain hK hU hpubVP
  refine ⟨as,haw0,ha,?_⟩
  intro a ham
  obtain ⟨e,he,hz,hid,hbytes⟩:=ProcessRepairAccountComplete.value view hpubV hVW hV haw0 ha ham
  have haw:AcctV3Wf as:=by
    rcases haw0 with rfl|hw
    · simp at ham
    · exact hw
  have hpre:Bytes8 a.pre:=by rw [←hbytes];exact hb e he
  have hlen:=(haw.v1.len a ham).1
  refine ⟨e,he,hz,hid,hbytes,by rw [hbytes,hlen],?_⟩
  rw [hbytes]
  exact Link.decode_pre hlen hpre (haw.v1.notMax a ham (fun i _=>Link.getD_lt_of_bytes8 hpre i))
end ZkFormal.NearV3.Candidates.ProcessRepairAccountNative
