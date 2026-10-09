import ZkFormal.NearV3.Candidates.ProcPriorRoutedFusedForestBytes
import ZkFormal.NearV3.Candidates.ProcPriorMerkleByteTag
import ZkFormal.NearV3.Candidates.ProcPriorRoutedShaByteSource
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedGlobalForestBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem provider {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubC:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (I:PubIdx AP pub Fp.ofNat) {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {vs:List NodeS3} {es:List ValE}
    (hN:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hV:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {v:List UpsSeg} (hw:Render.UpsRelay.Extract.Wf v) {hs:List HeadE} {K:Nat} {r0 rK:List Nat}
    (hchain:RootChain hs (v.map UpsRows.upsE) K r0 rK) (hK:K<33)
    (hU:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v))
    (htag:msg[0]!.toNat%16=7 ∨ msg[0]!.toNat%16=8 ∨ msg[0]!.toNat%16=9)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_BYTES) (hsend:i.send=true)
    (hm:i.multNat tr t r pub≠0) (hmsg:i.msgVal tr t r pub=msg) :
    ProcPriorForestByteIdentity.Provider (vs:=vs) (es:=es) msg := by
  rcases ProcPriorRoutedByteInventory.physical htables ht hi hb hsend hm with rfl|rfl|rfl
  · have hc:=tableBusCount_pos hr hi hm
    rw [hb,hsend,hmsg,htables] at hc
    exact ProcPriorRoutedFusedForestBytes.provider hH htables hpubS hpubC I hprep fwd hrec
      hN hV hw hchain hK hU htag (Nat.pos_of_ne_zero hc)
  · have h:=ProcPriorAccountByteTag.tag hH htables hpubV hr hi hb hsend hm
    rw [hmsg,ProcPriorRoutedFusedForestBytes.head_zero] at h
    change msg[0]!.toNat%16=10 at h
    omega
  · have hc:=tableBusCount_pos hr hi hm
    rw [hb,hsend,hmsg] at hc
    have h:=ProcPriorMerkleByteTag.tag hH htables (Nat.pos_of_ne_zero hc)
    rw [ProcPriorRoutedFusedForestBytes.head_zero] at h
    change msg[0]!.toNat%16=6 at h
    omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedGlobalForestBytes
