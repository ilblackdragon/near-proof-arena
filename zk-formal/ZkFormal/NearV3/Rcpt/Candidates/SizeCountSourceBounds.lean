import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSourcePartitions
import ZkFormal.NearV3.Rcpt.Candidates.PhysicalSourceCount

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private theorem chain_rcl (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) :
    DedupProof.chainMsgs tr tt s bs B_RCL false=bs.map (fun B => [B.j,B.L]) := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih =>
    rw [DedupProof.chainMsgs,ih]
    have hh : DedupRender.blockMsgs B (DedupProof.repeatedAt tr tt s) B_RCL false=[[B.j,B.L]] := by
      cases hd : B.dup <;>
        simp [DedupRender.blockMsgs,DedupRender.rootMsgs,srcpLeafMsgs,srcpItemMsgs,
          hd,B_RCL,B_SRC,B_DIGEST,B_BYTES,List.map_const']
    rw [hh]
    rfl

private theorem sum_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ a∈xs,f a≤g a) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Exact global RCL traffic bounds the sum of natural source list lengths by
receipt rows, rather than bounding each length separately and losing multiplicity. -/
theorem source_lengths_bound
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : DedupProof.BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m) :
    (bs.map SrcpB.L).sum≤rcpt.height tr := by
  have hcanon : ∀ B∈bs,B.L<P := by
    intro B hB
    have hw := hs.local hsrc B hB
    cases hd : B.dup
    · rw [hd] at hw; exact hw.canon.2.1
    · rw [hd] at hw; rw [hw.1]; decide
  have hp := List.perm_iff_count.mpr hbalance
  rw [hs.all_traffic hsrc,hr.rcl_full hrcpt] at hp
  simp only [DedupProof.sourceMsgs,show B_RCL≠B_SIZE by decide,ite_false,chain_rcl] at hp
  have he := (hp.map (fun m => (m.getD 1 0).toNat)).sum_nat
  simp only [List.map_map,Function.comp_def] at he
  have hleft : bs.map (fun B => ((Msg.toFp [B.j,B.L]).getD 1 0).toNat)=bs.map SrcpB.L := by
    apply List.map_congr_left
    intro B hB
    simp [Msg.toFp,toNat_natCast,Nat.mod_eq_of_lt (hcanon B hB)]
  have hright : ls.map (fun B => ((RcptV3Proof.listRclRecord rcpt tr B).getD 1 0).toNat)=
      ls.map (fun B => lOffs (B.viewReceipts rcpt tr) (B.viewReceipts rcpt tr).length) := by
    apply List.map_congr_left
    intro B hB
    simp [RcptV3Proof.listRclRecord,toNat_natCast,Nat.mod_eq_of_lt ((hr.blocks B hB).encoded_lt_P hrcpt)]
  rw [hleft,hright] at he
  rw [he]
  have hb := sum_le ls (fun B => lOffs (B.viewReceipts rcpt tr) (B.viewReceipts rcpt tr).length)
    RcptV3Proof.ListBlock.rows (fun B _ => B.encoded_le_rows rcpt tr)
  have hrows := hr.rows
  have hend := hr.end_padding.1
  omega

private theorem sum_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun a => f a+g a).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem source_paths_bound {src : Trace Fp} {ts : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    {bs : List SrcpB} {se : Nat} (hs : DedupProof.BlockChain src ts 0 bs se) :
    (bs.map fun B => 33*B.path.length).sum≤src.height ts := by
  have hp : ∀ B∈bs,33*B.path.length≤1+DedupRender.payloadRows B := by
    intro B hB
    have hw := hs.local hsrc B hB
    cases hd : B.dup
    · simp [DedupRender.payloadRows,hd]; omega
    · rw [hd] at hw
      simp [DedupRender.payloadRows,hd,hw.2.1]
  have hh := sum_le bs (fun B => 33*B.path.length) (fun B => 1+DedupRender.payloadRows B) hp
  rw [←DedupRender.R_eq] at hh
  have hr := hs.rows
  have he := hs.bound
  omega

/-- The complete natural source charge is bounded by actual receipt rows plus
source rows, with RCL multiplicity preventing repeated counting of receipt data. -/
theorem source_charge_bound
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : DedupProof.BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m) :
    (bs.map fun B => B.L+33*B.path.length).sum≤rcpt.height tr+src.height ts := by
  rw [sum_add]
  have hL := source_lengths_bound hsrc hrcpt hs hr hbalance
  have hP := source_paths_bound hsrc hs
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
