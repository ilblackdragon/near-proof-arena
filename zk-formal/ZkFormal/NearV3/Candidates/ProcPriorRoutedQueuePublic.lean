import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueueKey
import ZkFormal.NearV3.Assembly.RcptCandidateNaturalTotals
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges
import ZkFormal.NearV3.Sched.Pub.Prep
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedQueuePublic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3
open RcptV3Proof Assembly.ReceiptCandidateProof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem public_byte (p:Prep) (overhead j:Nat) :
    pubNat (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) j<256 := by
  unfold pubNat
  rw [Public.pub_getD]
  change PubVal.val (Public.byteF _) < 256
  rw [Public.byteF_val]
  exact UInt8.toNat_lt _

theorem receipt_count {AP:AirP} {tr:Trace Fp}
    {cb:NearSpec.Bytes} {hint:Hint} {p:Prep} (hp:prepD0 cb hint=.ok p) (overhead:Nat)
    (hH:HoldsP AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) tr)
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e) :
    (bs.map fun B=>B.receipts.length).sum=p.hdr.n ∧
    (bs.map fun B=>B.receipts.length).sum≤W_AK := by
  have he:=prepared_receipt_count hp overhead (Assembly.prepD0_roots hp)
  have hn:=prepD0_count_bound hp
  have hl:=Assembly.ReceiptCandidateProof.repaired_local_base
    (ProcPriorRoutedReceiptView.local_receipt hH htables)
  have hs:=ListChain.natural_count hl hc (by rw [he];exact hn.2)
    (fun i _=>public_byte p overhead (PH_N+i))
  rw [he] at hs
  refine ⟨hs,?_⟩
  rw [hs]
  change p.hdr.n≤8192
  omega

theorem queue_count {cb:NearSpec.Bytes} {hint:Hint} {p:Prep}
    (hp:prepD0 cb hint=.ok p) (overhead:Nat) (tr:Trace Fp) (tt r:Nat) :
    (Qv.Candidates.CombinedTable.kPublic.eval tr tt r
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))).toNat=p.hdr.K ∧ p.hdr.K<64 := by
  have hn:=Sched.prepD0_len hp
  have hs:=Assembly.prepD0_sched_count hp
  have hk:p.hdr.K<64:=by omega
  have he:leN' (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) 26 4)=p.hdr.K:=by
    apply public_u32_native _ _ _ (by omega)
    intro k hk4
    rw [Public.pub_getD,Public.prepared_header p overhead (Assembly.prepD0_roots hp) (by omega),
      Public.header_implicit_count p overhead hk4]
  have hcast:=Assembly.ReceiptCandidateProof.public_u32_eval tr tt r
    (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) 26
    (fun i _=>public_byte p overhead (26+i))
  change Qv.Candidates.CombinedTable.kPublic.eval tr tt r _=_ at hcast
  rw [hcast,he]
  constructor
  · exact (Fp.toNat_ofNat p.hdr.K).trans (Nat.mod_eq_of_lt (by unfold Algebra.P;omega))
  · exact hk
end ZkFormal.NearV3.Candidates.ProcPriorRoutedQueuePublic
