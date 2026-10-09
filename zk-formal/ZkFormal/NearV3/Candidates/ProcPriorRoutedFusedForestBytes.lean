import ZkFormal.NearV3.Candidates.ProcPriorRoutedByteInventory
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedFusedForestBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedByteInventory

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem head_zero (msg:List Fp):msg.headD 0=msg[0]!:=by cases msg <;> rfl

theorem source_count (tr:Trace Fp) (pub msg:List Fp) (j:Nat) :
    tableBusCount (ProcPriorRoutedSourceView.base j).interactions
      (HorizontalTrace.project (ProcPriorRoutedSourceView.offset j) tr) 0 pub B_BYTES true msg=
    tableBusCount (ProcPriorRoutedSourceView.base j).interactions
      (ProcPriorRoutedSourceView.source tr) j pub B_BYTES true msg := by
  simp only [tableBusCount,Interaction.multNat,ProcPriorRoutedSourceBoundary.mult_focus]
  simp only [Interaction.msgVal,Expr.eval,rowEnv,HorizontalTrace.project,ProcPriorRoutedSourceView.source,Trace.height]
  rfl

/-- Inside the actual fused trace, node/value tags can only be supplied by
SAME extracted Node/Value inventories. All other installed providers have their
natural tag bounds proved from actual local constraints and authenticated buses. -/
theorem provider {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
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
    have h:=ProcPriorRoutedCodecByteTag.prepared hH htables hpubS I hprep fwd hrec hr hi hb hs hmi
    rw [ProcPriorRoutedCodecProjection.message,he] at h
    omega
  · change 0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_BYTES true msg at hc
    have h:=ProcPriorReceiptByteTags.physical hH htables hc
    rw [head_zero] at h
    omega
  all_goals
    unfold count at hc
    dsimp only [Prod.fst,Prod.snd] at hc
    rw [source_count] at hc
  · have h:=ProcPriorRoutedSourceByteTag.tag hH htables hpubC 0 (by decide) (Nat.ne_of_gt hc)
    omega
  · have h:=ProcPriorRoutedSourceByteTag.tag hH htables hpubC 1 (by decide) (Nat.ne_of_gt hc)
    omega
  · have h:=ProcPriorRoutedSourceByteTag.tag hH htables hpubC 2 (by decide) (Nat.ne_of_gt hc)
    omega
  · have h:=ProcPriorRoutedSourceByteTag.tag hH htables hpubC 3 (by decide) (Nat.ne_of_gt hc)
    omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedFusedForestBytes
