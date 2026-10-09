import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableCharges

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 Assembly Link3
open DedupProof SourceLog22

/-- Four actual source tables pay the very same reconstructed source dictionary.
Source public, RCL, SHA, and SIZE hypotheses refer to physical providers. -/
theorem physical_source_chain_paid
    {src rcpt : Trace Fp} {a b c d tr : Nat} {pub : List Fp}
    (ha : TableLocal (sourceTable firstTable) src a pub)
    (hb : TableLocal (sourceTable (middleTable 64 65)) src b pub)
    (hc : TableLocal (sourceTable (middleTable 65 66)) src c pub)
    (hd : TableLocal (sourceTable lastTable) src d pub)
    (hcarry : ∀ bus∈([64,65,66] : List Nat),∀ m,
      boundaryCount src a b c d pub bus true m=boundaryCount src a b c d pub bus false m)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain (variableTrace src a b c d) 0 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      (providerMessages src a b c d pub B_RCL false).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (rcOthers srcOthers : List Msg)
    (hrbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++rcOthers) m)
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<ZkFormal.Algebra.P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=(providerMessages src a b c d pub B_BYTES true).count m+cnt srcOthers m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<ZkFormal.Algebra.P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈providerMessages src a b c d pub B_DIGEST false,0<shaS B_DIGEST m)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : NearSpecV3.prepD0 cb hint=.ok p)
    (hsourcepub : ∀ m,(providerMessages src a b c d pub B_SRC false).count m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k)
    (x : ExtV3)
    {us : List UniqE} {others : List Msg}
    (hn : NodeWf3 x.nodes) (hh : HeadWf x.heads) (hv : ValWf x.values)
    (hu : UniqWf us) (hpar : ParentBal x.nodes x.heads)
    (hvpar : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    {ups : List UpsE} {r0 rK : List Nat}
    (hchain : RootChain x.heads ups p.hdr.K r0 rK)
    (hdict : x.dictionary=nativeDictionary p.lists p.hdr.own
      (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs (nativeFillers p.lists))
    {bytes : Bytes} (hbytes : countedPreparedBytes p k.c.chunkInner=some bytes)
    (hroots : Public.RootsSized p) (hpublic : pub=ZkFormal.Udr.pubOf Fp bytes)
    {sz : Trace Fp} {st : Nat} (hsize : TableLocal sizeTable sz st pub)
    (hpaid : ∀ m,tableBusCount sizeTable.interactions sz st pub B_SIZE false m=
      ([[0,(nodePayload x.nodes:Fp),((x.nodes.filter fun v => !v.dup).length:Fp)],
        [1,(valPayload x.values:Fp),((x.values.filter fun v => !v.dup).length:Fp)]] : List (List Fp)).count m+
        (providerMessages src a b c d pub B_SIZE true).count m)
    :
    (ZkFormal.V3.encodeSW (stateWitnessOfV3 k x)).length≤8388608 := by
  obtain ⟨hab,hbc,hcd⟩ := boundaries_cells hcarry
  have hsrc := variable_local ha hb hc hd hab hbc hcd
  have hcount := provider_chain_count ha hb hc hd hsrc hs
  have hbal : ∀ m,
      ((List.range ((variableTrace src a b c d).height 0)).flatMap
        (fun q => rowTraffic DedupTable.interactions (variableTrace src a b c d) 0 q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap
        (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m := by
    intro m
    rw [hs.all_traffic hsrc B_RCL false]
    exact (hcount B_RCL false (by decide) (by decide) (by decide) (by decide) m).symm.trans (hbalance m)
  have hbytesSrc : ∀ m,shaR B_BYTES m=
      cnt (sourceMsgs (variableTrace src a b c d) 0 bs B_BYTES true++srcOthers) m := by
    intro m
    rw [hsbytes,hcount B_BYTES true (by decide) (by decide) (by decide) (by decide)]
    simp only [cnt,List.map_append,List.count_append]
  have hdigestSrc : ∀ m∈sourceMsgs (variableTrace src a b c d) 0 bs B_DIGEST false,
      0<shaS B_DIGEST m.toFp := by
    intro m hm
    apply hdigest
    have he := provider_chain_messages ha hb hc hd hsrc hs B_DIGEST false (by decide) (by decide) (by decide)
    simp only [show B_DIGEST≠B_SIZE by decide,ite_false,List.map_id'] at he
    rw [he]
    exact List.mem_map.mpr ⟨m,hm,rfl⟩
  have hsrcpub : ∀ m,cnt (sourceMsgs (variableTrace src a b c d) 0 bs B_SRC false) m=
      cnt (SourcePublic.records p.lists) m := by
    intro m
    exact (hcount B_SRC false (by decide) (by decide) (by decide) (by decide) m).symm.trans (hsourcepub m)
  have hsz := provider_chain_size ha hb hc hd hsrc hs
  have hpaid' : ∀ m,tableBusCount sizeTable.interactions sz st pub B_SIZE false m=
      ([[0,(nodePayload x.nodes:Fp),((x.nodes.filter fun v => !v.dup).length:Fp)],
        [1,(valPayload x.values:Fp),((x.values.filter fun v => !v.dup).length:Fp)],
        [2,(DedupRender.size bs:Fp),0]] : List (List Fp)).count m := by
    intro m
    rw [hpaid,hsz]
    rw [←List.count_append]; rfl
  exact chain_authenticated_witness_paid hsrc hrcpt hs hr hpub hbal hsha rcOthers srcOthers
    hrbytes hrother hbytesSrc hsother hdigestSrc hprep hsrcpub hown hw x hn hh hv hu hpar hvpar
    H hD hDup hEnt hchain hdict hbytes hroots hpublic hsize hpaid'

/-- Actual four-table extraction supplies the source chain used by the entire
payment continuation; no separately supplied chain or source count is required. -/
theorem physical_source_payment
    {src rcpt : Trace Fp} {a b c d tr : Nat} {pub : List Fp}
    (ha : TableLocal (sourceTable firstTable) src a pub)
    (hb : TableLocal (sourceTable (middleTable 64 65)) src b pub)
    (hc : TableLocal (sourceTable (middleTable 65 66)) src c pub)
    (hd : TableLocal (sourceTable lastTable) src d pub)
    (hcarry : ∀ bus∈([64,65,66] : List Nat),∀ m,
      boundaryCount src a b c d pub bus true m=boundaryCount src a b c d pub bus false m)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    : ∃ bs se, BlockChain (variableTrace src a b c d) 0 0 bs se ∧
      ∀
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      (providerMessages src a b c d pub B_RCL false).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (rcOthers srcOthers : List Msg)
    (hrbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++rcOthers) m)
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<ZkFormal.Algebra.P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=(providerMessages src a b c d pub B_BYTES true).count m+cnt srcOthers m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<ZkFormal.Algebra.P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈providerMessages src a b c d pub B_DIGEST false,0<shaS B_DIGEST m)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : NearSpecV3.prepD0 cb hint=.ok p)
    (hsourcepub : ∀ m,(providerMessages src a b c d pub B_SRC false).count m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k)
    (x : ExtV3)
    {us : List UniqE} {others : List Msg}
    (hn : NodeWf3 x.nodes) (hh : HeadWf x.heads) (hv : ValWf x.values)
    (hu : UniqWf us) (hpar : ParentBal x.nodes x.heads)
    (hvpar : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    {ups : List UpsE} {r0 rK : List Nat}
    (hchain : RootChain x.heads ups p.hdr.K r0 rK)
    (hdict : x.dictionary=nativeDictionary p.lists p.hdr.own
      (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs (nativeFillers p.lists))
    {bytes : Bytes} (hbytes : countedPreparedBytes p k.c.chunkInner=some bytes)
    (hroots : Public.RootsSized p) (hpublic : pub=ZkFormal.Udr.pubOf Fp bytes)
    {sz : Trace Fp} {st : Nat} (hsize : TableLocal sizeTable sz st pub)
    (hpaid : ∀ m,tableBusCount sizeTable.interactions sz st pub B_SIZE false m=
      ([[0,(nodePayload x.nodes:Fp),((x.nodes.filter fun v => !v.dup).length:Fp)],
        [1,(valPayload x.values:Fp),((x.values.filter fun v => !v.dup).length:Fp)]] : List (List Fp)).count m+
        (providerMessages src a b c d pub B_SIZE true).count m)
    ,
    (ZkFormal.V3.encodeSW (stateWitnessOfV3 k x)).length≤8388608 := by
  obtain ⟨bs,se,hl,hs,hm⟩ := physical_source_provider ha hb hc hd hcarry
  refine ⟨bs,se,hs,?_⟩
  exact physical_source_chain_paid ha hb hc hd hcarry hrcpt hs

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
