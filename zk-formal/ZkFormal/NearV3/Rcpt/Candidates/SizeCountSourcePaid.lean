import ZkFormal.NearV3.Rcpt.Candidates.SizeCountWitnessFields
import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionarySizeBinding

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 Assembly Link3
open DedupProof

/-- Full source authentication supplies the exact dictionary charge to native
SIZE payment. All source and receipt facts concern the same physical chains. -/
theorem authenticated_dictionary_witness_paid
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (rcOthers srcOthers : List Msg)
    (hrbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++rcOthers) m)
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<ZkFormal.Algebra.P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=cnt (sourceMsgs src ts bs B_BYTES true++srcOthers) m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<ZkFormal.Algebra.P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs src ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : NearSpecV3.prepD0 cb hint=.ok p)
    (hsourcepub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k)
    (x : ExtV3)
    {us : List UniqE} {others : List Msg} {shaS shaR : Nat → List Fp → Nat}
    (hn : NodeWf3 x.nodes) (hh : HeadWf x.heads) (hv : ValWf x.values)
    (hu : UniqWf us) (hpar : ParentBal x.nodes x.heads)
    (hvpar : VParentBal x.nodes x.values)
    (H : ShaHyp x.nodes x.heads x.values others shaS shaR)
    (hD : DigsBal x.nodes x.heads us) (hDup : DupBal us x.nodes x.values)
    (hEnt : EntBal x.nodes x.values)
    (hheads : ∀ tau,tau≤k.implicitBlks.length → ∃ h∈x.heads,h.tau=tau)
    (hdict : x.dictionary=nativeDictionary p.lists p.hdr.own
      (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs (nativeFillers p.lists))
    {bytes : Bytes} (hbytes : countedPreparedBytes p k.c.chunkInner=some bytes)
    (hroots : Public.RootsSized p) (hpublic : pub=ZkFormal.Udr.pubOf Fp bytes)
    {sz : Trace Fp} {st : Nat} (hsize : TableLocal sizeTable sz st pub)
    (hpaid : ∀ m,tableBusCount sizeTable.interactions sz st pub B_SIZE false m=
      ([[0,(nodePayload x.nodes:Fp),((x.nodes.filter fun v => !v.dup).length:Fp)],
        [1,(valPayload x.values:Fp),((x.values.filter fun v => !v.dup).length:Fp)],
        [2,(DedupRender.size bs:Fp),0]] : List (List Fp)).count m)
    (he : k.c.epochId.length=32) :
    (ZkFormal.V3.encodeSW (stateWitnessOfV3 k x)).length≤8388608 := by
  have hcap := source_charge_cap hsrc hrcpt hs hr hbalance
  have hle : ∀ xs : List SrcpB,DedupRender.size xs≤(xs.map fun B => B.L+33*B.path.length).sum := by
    intro xs
    induction xs with
    | nil => simp [DedupRender.size]
    | cons B xs ih =>
      simp only [DedupRender.size,List.map_cons,List.sum_cons] at ih ⊢
      unfold DedupRender.sizeStep at ih ⊢
      split <;> omega
  have hsource := Nat.le_trans (hle bs) hcap
  have ha := witness_applied_hash_length k x
  have ht := witness_transition_lengths k x hh hheads
  have hd := hs.native_dictionary_size hsrc hrcpt hr hpub hbalance hsha rcOthers srcOthers
    hrbytes hrother hsbytes hsother hdigest hprep hsourcepub hown hw
  have hdictsize : (encList V3.encodeEntry (stateWitnessOfV3 k x).entries).length=
      DedupRender.size bs+44*p.lists.length+4 := by
    simpa only [stateWitnessOfV3_entries,hdict] using hd
  have hk : (stateWitnessOfV3 k x).implicit.length=p.hdr.K := by
    rw [stateWitnessOfV3_implicit_length,prepD0_implicit_count hprep hw]
  rw [hpublic] at hsize hpaid
  exact prepared_native_witness_paid hbytes hroots hsize k x hn hh hv hu hpar hvpar
    H hD hDup hEnt hheads (DedupRender.size bs) hsource hpaid he ha ht hdictsize rfl hk

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
