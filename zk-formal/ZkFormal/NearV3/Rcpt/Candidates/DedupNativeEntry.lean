import ZkFormal.NearV3.Rcpt.Candidates.DedupListDigest
import ZkFormal.NearV3.Assembly.Witness

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Executable native dictionary entry from one extracted receipt list and source path.
Public key/from-shard selection is supplied by the prepared-source binding. -/
def nativeSourceEntry (key : Bytes) (fromShard own : Nat) (L : ListV3) (B : SrcpB) : Assembly.SourceEntryV3 :=
  ⟨key,fromShard,own,L,B⟩

/-- Complete computed-source verification now uses actual RC bytes and path SHA
traffic, rather than an assumed native receipt-list leaf hash. -/
theorem BlockChain.native_entry_verified
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
    {own : Nat} (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false) (key : Bytes) (fromShard : Nat) :
    NearSpecV3.verifyReceiptProof (toBytes B.root)
      (nativeSourceEntry key fromShard own ((ls.getD B.j ⟨0,[]⟩).view rcpt tr) B).entry=true := by
  obtain ⟨hi,hleaf⟩ := hs.receipt_leaf hsrc hrcpt hr hpub hbalance hsha rcOthers hrbytes hrother hdigest hown hB hd
  apply hs.verifyReceiptProof hsrc hsha srcOthers hsbytes hsother hdigest hB hd
  · change toBytes B.leaf=sha256 (u64 own++encodeReceipts
      (((ls.getD B.j ⟨0,[]⟩).view rcpt tr).rs.map (fun x => x.toRcptV.toReceipt)))
    rw [getD_eq_getElem' ls ⟨0,[]⟩ hi]
    exact hleaf
  · rfl

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
