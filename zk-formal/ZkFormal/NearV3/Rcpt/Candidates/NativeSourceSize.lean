import ZkFormal.NearV3.Rcpt.Candidates.DedupListDigest
import ZkFormal.NearV3.Rcpt.Link.NativeListSize
import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionarySize
import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionaryVerified

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open NearSpecV3 (Prep Hint)

/-- The actual source SIZE length equals its native receipt-proof preimage length. -/
theorem BlockChain.native_receipt_size
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++others) m)
    (hother : ∀ m∈others,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    (hdigest : ∀ m∈sourceMsgs src ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {own : Nat} (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false) :
    ∃ hi : B.j<ls.length,
      (u64 own++encodeReceipts ((ls[B.j].view rcpt tr).rs.map (fun x => x.toRcptV.toReceipt))).length=B.L := by
  obtain ⟨hi,hlen⟩ := hs.receipt_length hsrc hrcpt hr hbalance hB hd
  have hi' : B.j<(ls.map (RcptV3Proof.ListBlock.view rcpt tr)).length := by simpa using hi
  have hw := (hs.payload_wf hsrc).computed hB hd
  have hcounts := RcptLink.physical_view_counts hrcpt hr
  have hlen' : (RcptLink.listEncoding pub ((ls.map (RcptV3Proof.ListBlock.view rcpt tr))[B.j])).length=B.L := by
    simpa only [List.getElem_map] using hlen
  have hdig := hdigest _ (source_leaf_recv hB hd)
  rw [←hlen'] at hdig
  have hh := RcptLink.list_sha_native_size (hr.view_wf hrcpt hpub) hcounts.1 hcounts.2 hsha others
    hbytes hother hi' (by rw [hlen']; exact hw.canon.2.1)
    (fun v hv => hw.canon.2.2.1 v (List.mem_append.mpr (Or.inr hv))) hdig hown
  refine ⟨hi,?_⟩
  simpa only [List.getElem_map,hlen] using hh

/-- Exact computed-entry charge at its shared public/source/receipt index. -/
theorem BlockChain.native_entry_charge
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
    entrySizeCharge (nativeEntryAt p.lists p.hdr.own
      (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs i).entry=
      (bs.getD i default).L+33*(bs.getD i default).path.length := by
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
  obtain ⟨hri,hsize⟩ := hs.native_receipt_size hsrc hrcpt hr hpub hbalance hsha rcOthers
    hrbytes hrother hdigest hown hBm hdup
  simp only [hj] at hri hsize
  simpa only [nativeEntryAt,getD_eq_getElem' bs default hbi,
    getD_eq_getElem' (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) default
      (by simpa only [List.length_map] using hri),List.getElem_map,
    nativeSourceEntry,Assembly.SourceEntryV3.entry,entrySizeCharge,NearSpecV3.encList,List.length_map,encodeReceipts,B]
    using congrArg (fun n => n+33*B.path.length) hsize

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
