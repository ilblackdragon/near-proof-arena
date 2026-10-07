import ZkFormal.NearV3.Rcpt.Candidates.DedupReceiptLengths
import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceVerify
import ZkFormal.NearV3.Rcpt.Link.ListSha

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Every computed source consumes the RC list digest at its exact source index. -/
theorem source_leaf_recv {tr : Trace Fp} {tt : Nat} {bs : List SrcpB} {B : SrcpB}
    (hB : B∈bs) (hd : B.dup=false) :
    digMsg (msgId K_RC B.j) B.L B.leaf∈sourceMsgs tr tt bs B_DIGEST false := by
  simp only [sourceMsgs,show B_DIGEST≠B_SIZE by decide,ite_false]
  apply chain_mem hB
  intro rep
  simp only [DedupRender.blockMsgs,hd,Bool.false_eq_true,ite_false,List.mem_append]
  right
  left
  simp [srcpLeafMsgs,B_DIGEST,B_BYTES]

/-- RCL balance identifies the actual complete receipt list and its ordinary
encoded length for every computed source block. -/
theorem BlockChain.receipt_length
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false) :
    ∃ hi : B.j<ls.length,(RcptLink.listEncoding pub (ls[B.j].view rcpt tr)).length=B.L := by
  have hm := source_rcl_recv (tr:=src) (tt:=ts) hB
  have hmem : Msg.toFp [B.j,B.L]∈
      (List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false) := by
    rw [hs.all_traffic hsrc]
    exact List.mem_map.mpr ⟨_,hm,rfl⟩
  have hp := List.count_pos_iff.mpr hmem
  rw [hbalance] at hp
  have hh := List.count_pos_iff.mp hp
  rw [hr.rcl_full hrcpt] at hh
  have hw := (hs.payload_wf hsrc).computed hB hd
  obtain ⟨hi,hlen⟩ := hr.rcl_decode hrcpt hw.canon.1 hw.canon.2.1 hh
  refine ⟨hi,?_⟩
  rw [RcptLink.list_encoding_length]
  exact hlen

/-- The source leaf hash is derived from actual receipt AIR, complete RC byte
traffic, SHA facts, and RCL ownership. There is no assumed leaf/native-list digest. -/
theorem BlockChain.receipt_leaf
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
    ∃ hi : B.j<ls.length,toBytes B.leaf=sha256
      (u64 own++encodeReceipts ((ls[B.j].view rcpt tr).rs.map (fun x => x.toRcptV.toReceipt))) := by
  obtain ⟨hi,hlen⟩ := hs.receipt_length hsrc hrcpt hr hbalance hB hd
  have hi' : B.j<(ls.map (RcptV3Proof.ListBlock.view rcpt tr)).length := by simpa using hi
  have hw := (hs.payload_wf hsrc).computed hB hd
  have hcounts := RcptLink.physical_view_counts hrcpt hr
  have hlen' : (RcptLink.listEncoding pub ((ls.map (RcptV3Proof.ListBlock.view rcpt tr))[B.j])).length=B.L := by
    simpa only [List.getElem_map] using hlen
  have hdig := hdigest _ (source_leaf_recv hB hd)
  rw [←hlen'] at hdig
  have hh := RcptLink.list_sha_native (hr.view_wf hrcpt hpub) hcounts.1 hcounts.2 hsha others
    hbytes hother hi' (by rw [hlen']; exact hw.canon.2.1)
    (fun v hv => hw.canon.2.2.1 v (List.mem_append.mpr (Or.inr hv))) hdig hown
  exact ⟨hi,by simpa only [List.getElem_map] using hh⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
