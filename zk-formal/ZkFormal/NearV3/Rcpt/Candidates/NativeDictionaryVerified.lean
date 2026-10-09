import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionary
import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceReuse

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open NearSpecV3 (Prep Hint)

/-- Actual source, receipt and SHA traffic authenticate each executable first-key
representative. Public metadata binds its key, from-shard and root; no assumed
leaf hash or dictionary lookup occurs in this theorem. -/
theorem BlockChain.native_first_verified
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
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=cnt (sourceMsgs src ts bs B_BYTES true++srcOthers) m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs src ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : NearSpecV3.prepD0 cb hint=.ok p)
    (hsourcepub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    (i : Nat) (hi : i<p.lists.length) (hd : Public.sourceDup p.lists i=false) :
    NearSpecV3.verifyReceiptProof (p.lists.getD i ⟨[],0,[]⟩).root
      (nativeEntryAt p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs i).entry=true := by
  have hb := hs.bind_prepared hsrc hprep hsourcepub
  have hbi : i<bs.length := by omega
  let B := bs[i]
  have hBm : B∈bs := List.getElem_mem hbi
  obtain ⟨rep,hrep⟩ := sourceViews_mem (tr := src) (tt := ts) (s := 0) hBm
  have hf := hb.2 (B,rep) hrep
  have hj : B.j=i := by
    have hh := hs.j_indices hsrc i hbi
    rw [(row0 hsrc).2.1] at hh
    simpa only [show Fp.toNat 0=0 from rfl,Nat.zero_add] using hh
  have hdup : B.dup=false := by rw [hf.2.1,hj,hd]
  have hv := hs.native_entry_verified hsrc hrcpt hr hpub hbalance hsha rcOthers srcOthers
    hrbytes hrother hsbytes hsother hdigest hown hBm hdup
    (p.lists.getD i ⟨[],0,[]⟩).key (p.lists.getD i ⟨[],0,[]⟩).fromShard
  obtain ⟨hri,_⟩ := hs.receipt_length hsrc hrcpt hr hbalance hBm hdup
  rw [hj] at hri
  rw [hf.2.2.2.1,hj] at hv
  simpa only [nativeEntryAt,getD_eq_getElem' bs default hbi,
    getD_eq_getElem' ls ⟨0,[]⟩ hri,
    getD_eq_getElem' (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) default
      (by simpa only [List.length_map] using hri),List.getElem_map] using hv

/-- Concrete dictionary selection for every prepared source, including repeated
keys. Unused fillers are retained explicitly and cannot override a source entry.
Cardinality, byte capacity, native slot coverage and routing are separate obligations. -/
theorem BlockChain.native_dictionary_selected
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
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=cnt (sourceMsgs src ts bs B_BYTES true++srcOthers) m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs src ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : prepSourceD0 cb hint=.ok p)
    (hsourcepub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    (fillers : List NearSpecV3.ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈p.lists,f.key≠s.key)
    {s : NearSpecV3.SrcList} (hsm : s∈p.lists) :
    ∃ e : Assembly.SourceEntryV3,
      Sum.inl e∈nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs fillers ∧
      NearSpecV3.lookupLast s.key
        ((nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs fillers).map
          Assembly.DictionaryEntryV3.entry)=some e.entry ∧
      e.fromShard=s.fromShard ∧ e.toShard=p.hdr.own ∧ NearSpecV3.verifyReceiptProof s.root e.entry=true := by
  obtain ⟨hp,hm⟩ := prepSourceD0_sound hprep
  apply nativeDictionary_selected p.lists p.hdr.own _ bs fillers hf hm _ hsm
  intro i hi hd
  exact hs.native_first_verified hsrc hrcpt hr hpub hbalance hsha rcOthers srcOthers
    hrbytes hrother hsbytes hsother hdigest hp hsourcepub hown i hi hd

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
