import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceHashes
import ZkFormal.NearV3.Rcpt.Candidates.DedupPublicViews
import ZkFormal.NearV3.Rcpt.Extract.V.RclDecode

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Every candidate source block receives its list index and list length on RCL. -/
theorem source_rcl_recv {tr : Trace Fp} {tt : Nat} {bs : List SrcpB} {B : SrcpB} (hB : B∈bs) :
    [B.j,B.L]∈sourceMsgs tr tt bs B_RCL false := by
  simp only [sourceMsgs,show B_RCL≠B_SIZE by decide,ite_false]
  apply chain_mem hB
  intro rep
  simp [DedupRender.blockMsgs,DedupRender.rootMsgs,B_RCL,B_DIGEST,B_SRC]

/-- Extracted source indices are canonical even for skipped proof blocks. -/
theorem BlockChain.j_canonical {tr : Trace Fp} {tt s e : Nat} {bs : List SrcpB}
    (h : BlockChain tr tt s bs e) : ∀ B∈bs, B.j<P := by
  induction h with
  | last s n B hs _ => intro C hC; obtain rfl := List.mem_singleton.mp hC; exact hs.root_canon.1
  | cons s n B hs tail e ht ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl|hC
    · exact hs.root_canon.1
    · exact ih C hC

/-- Actual source/receipt RCL balance makes any source length twelve an empty
extracted receipt list at that exact source index. Bus ownership is explicit in
`hbalance`; there is no semantic receipt-view premise. -/
theorem BlockChain.receipt_empty_of_twelve
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {B : SrcpB} (hB : B∈bs) (hLen : B.L=12) :
    ∃ hi : B.j<ls.length, ls[B.j].receipts=[] := by
  have hm := source_rcl_recv (tr := src) (tt := ts) hB
  have hmem : Msg.toFp [B.j,B.L]∈
      (List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false) := by
    rw [hs.all_traffic hsrc]
    exact List.mem_map.mpr ⟨_,hm,rfl⟩
  have hp := List.count_pos_iff.mpr hmem
  rw [hbalance] at hp
  have hrmem := List.count_pos_iff.mp hp
  apply hr.physical_rcl_twelve_empty hrcpt (hs.j_canonical B hB)
  simpa only [Msg.toFp,List.map_cons,List.map_nil,hLen,natCast_eq] using hrmem

/-- Duplicate-skipped source proofs therefore apply an actually empty receipt list. -/
theorem BlockChain.duplicate_receipt_empty
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {B : SrcpB} (hB : B∈bs) (hDup : B.dup=true) :
    ∃ hi : B.j<ls.length, ls[B.j].receipts=[] := by
  have hh := hs.local hsrc B hB
  rw [hDup] at hh
  exact hs.receipt_empty_of_twelve hsrc hrcpt hr hbalance hB hh.1

/-- All repeated occurrences, including the first computed proof, apply an empty list. -/
theorem BlockChain.repeated_receipt_empty
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {B : SrcpB} (hB : B∈bs) (hRep : (B,true)∈sourceViews src ts 0 bs) :
    ∃ hi : B.j<ls.length, ls[B.j].receipts=[] := by
  have hh := (hs.views_facts hsrc (B,true) hRep).2 rfl
  exact hs.receipt_empty_of_twelve hsrc hrcpt hr hbalance hB hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
