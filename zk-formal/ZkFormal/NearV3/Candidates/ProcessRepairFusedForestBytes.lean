import ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag
import ZkFormal.NearV3.Candidates.ProcessRepairCodecByteTag
import ZkFormal.NearV3.Candidates.ProcessRepairForeignByteTags
import ZkFormal.NearV3.Candidates.ProcPriorRoutedFusedForestBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairFusedForestBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedByteInventory
open ProcPriorRoutedFusedForestBytes (head_zero source_count)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem provider {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubS:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
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
    (hm:0<tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_BYTES true msg) :
    ProcPriorForestByteIdentity.Provider (vs:=vs) (es:=es) msg := by
  obtain ⟨pr,hpr,hc⟩:=fused_source hm
  simp only [providers,List.mem_cons,List.mem_nil_iff,or_false] at hpr
  rcases hpr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change 0<tableBusCount NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub B_BYTES true msg at hc
    rw [(hN _ _).1] at hc
    unfold ProcPriorForestByteIdentity.Provider
    rw [List.map_append]
    exact List.mem_append_left _ (List.count_pos_iff.mp hc)
  · change 0<tableBusCount ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub B_BYTES true msg at hc
    rw [(hV _ _).1] at hc
    unfold ProcPriorForestByteIdentity.Provider
    rw [List.map_append]
    exact List.mem_append_right _ (List.count_pos_iff.mp hc)
  · change 0<tableBusCount Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub B_BYTES true msg at hc
    obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount (Nat.ne_of_gt hc)
    have h:=ProcPriorCompactUpsByteTag.source_tag hw hchain hK hU hr hi hb hs hm
    rw [he] at h
    omega
  · change 0<tableBusCount ProcPriorCodecActual.interactions (ProcPriorRoutedCodecProjection.codec tr) 0 pub B_BYTES true msg at hc
    obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount (Nat.ne_of_gt hc)
    have hmi:(ProcPriorRoutedCodecProjection.interaction i).multNat tr 0 r pub≠0:=by
      rw [ProcPriorRoutedCodecProjection.mult];exact hm
    have h:=ProcessRepairCodecByteTag.prepared view hpubS I hprep fwd hrec hr hi hb hs hmi
    rw [ProcPriorRoutedCodecProjection.message,he] at h
    omega
  · change 0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_BYTES true msg at hc
    have h:=ProcessRepairForeignByteTags.receipt_tag view hc
    rw [head_zero] at h
    omega
  all_goals
    unfold count at hc
    dsimp only [Prod.fst,Prod.snd] at hc
    rw [source_count] at hc
  · have h:=ProcessRepairSourceByteTag.tag view hpubC 0 (by decide) (Nat.ne_of_gt hc)
    omega
  · have h:=ProcessRepairSourceByteTag.tag view hpubC 1 (by decide) (Nat.ne_of_gt hc)
    omega
  · have h:=ProcessRepairSourceByteTag.tag view hpubC 2 (by decide) (Nat.ne_of_gt hc)
    omega
  · have h:=ProcessRepairSourceByteTag.tag view hpubC 3 (by decide) (Nat.ne_of_gt hc)
    omega
end ZkFormal.NearV3.Candidates.ProcessRepairFusedForestBytes
