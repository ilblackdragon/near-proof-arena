import ZkFormal.NearV3.Rcpt.Candidates.PhysicalRepeatedOccurrence

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

private theorem chain_rcl_length (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) :
    (chainMsgs tr tt s bs B_RCL false).length=bs.length := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih =>
    rw [chainMsgs,List.length_append,ih]
    have hh : (DedupRender.blockMsgs B (repeatedAt tr tt s) B_RCL false).length=1 := by
      cases hd : B.dup <;>
        simp [DedupRender.blockMsgs,DedupRender.rootMsgs,srcpLeafMsgs,srcpItemMsgs,
          hd,B_RCL,B_SRC,B_DIGEST,B_BYTES,List.map_const']
    rw [hh]
    simp [Nat.add_comm]

theorem BlockChain.receipt_list_count
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    : bs.length=ls.length := by
  have hp := (List.perm_iff_count.mpr hbalance).length_eq
  rw [hs.all_traffic hsrc,hr.rcl_full hrcpt] at hp
  simp only [List.length_map,sourceMsgs,show B_RCL≠B_SIZE by decide,ite_false,
    chain_rcl_length] at hp
  exact hp

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
