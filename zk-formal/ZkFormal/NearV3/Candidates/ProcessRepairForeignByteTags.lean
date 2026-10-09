import ZkFormal.NearV3.Candidates.ProcessRepairShaFacts
import ZkFormal.NearV3.Candidates.ProcPriorReceiptByteTags
import ZkFormal.NearV3.Candidates.ProcPriorMerkleByteTag
namespace ZkFormal.NearV3.Candidates.ProcessRepairForeignByteTags
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open RcptV3Proof Assembly.ReceiptCandidateProof
open ProcPriorRoutedReceiptView (receipt)
open ProcPriorMerkleView (mirror node_bound)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem local_receipt {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    TableLocal Assembly.ReceiptCandidateRouting.candidateTable (receipt tr) 0 pub := by
  have h:=v.component 13 (by decide +kernel) (by decide)
  exact (ProcPriorComparatorRouting.local_iff _ _ _ _).mp h

theorem local_empty {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    TableLocal MerkleEmpty.table (mirror tr) T_MRK pub := by
  have h:=v.rest 10 (by rw [v.length];decide +kernel) (by decide)
  have hbase:=(InteractionTriples.local_iff MerkleEmpty.table tr 10 pub).mp h
  exact ⟨hbase.log_ge,hbase.log_le,hbase.constr,hbase.bits⟩
theorem receipt_view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    ∃bs e,RcptV3Proof.ListChain (receipt tr) 0 0 bs e ∧
      ((List.range (tr.height 0)).flatMap
        (fun r=>ZkFormal.Near.rowTraffic RcptV3.interactions (receipt tr) 0 r pub B_BYTES true)).Perm
        ((rcptSends3 pub (bs.map (ListBlock.view (receipt tr) 0)) B_BYTES).map Msg.toFp) ∧
      bs.length<2^22 ∧ (bs.map fun b=>b.receipts.length).sum<2^22 := by
  have hlocal:=Assembly.ReceiptCandidateProof.repaired_local_base (local_receipt v)
  obtain ⟨bs,e,hc⟩:=Assembly.ReceiptCandidateProof.extract_lists hlocal
  have htraffic:=Assembly.ReceiptCandidateProof.ListChain.bytes_full hlocal hc
  rw [Assembly.ReceiptCandidateProof.chainByteMsgs_eq_view] at htraffic
  have hrows:=Assembly.ReceiptCandidateProof.ListChain.rows hc
  have hend:=Assembly.ReceiptCandidateProof.ListChain.end_padding hc
  have hheight:=Assembly.ReceiptCandidateProof.height_le hlocal
  have hcount:=Assembly.ReceiptCandidateProof.receipt_counts_le_rows bs
  have hlen:bs.length≤(bs.map ListBlock.rows).sum := by
    clear hrows hend htraffic hc hcount
    induction bs with
    | nil=>simp
    | cons b bs ih=>
      have hb:1≤b.rows:=by unfold ListBlock.rows;omega
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  refine ⟨bs,e,hc,htraffic,?_,?_⟩ <;> omega
theorem receipt_tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    {msg:List Fp}
    (hm:0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_BYTES true msg) :
    1≤(msg.headD 0).toNat%16 ∧ (msg.headD 0).toNat%16≤5 := by
  obtain ⟨bs,e,hc,htraffic,hlen,hcount⟩:=receipt_view v
  rw [tableBusCount_eq] at hm
  have hmem:=List.count_pos_iff.mp hm
  have hmem:=htraffic.mem_iff.mp hmem
  obtain ⟨m,hm,heq⟩:=List.mem_map.mp hmem
  have hflat:(flatR (bs.map (ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length=
      (bs.map fun b=>b.receipts.length).sum := by
    rw [flat_views,List.length_map]
    simp only [List.length_flatMap]
  have hsafe:=ProcPriorReceiptByteTags.inventory pub _ (by simpa using hlen) (by omega) hm
  have hehead:msg.headD 0=Fp.ofNat (m.headD 0) := by
    rw [←heq]
    cases m <;> rfl
  rw [hehead,Fp.toNat_ofNat,Nat.mod_eq_of_lt hsafe.1]
  exact hsafe.2
theorem merkle_tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    {msg:List Fp}
    (hm:0<tableBusCount (AP.tables[10]!).interactions tr 10 pub B_BYTES true msg) :
    (msg.headD 0).toNat%16=K_MRK := by
  rw [v.wires,ProcPriorMerkleView.count] at hm
  have hl:=local_empty v
  have hnon:MerkleEmpty.countE.eval (mirror tr) T_MRK 0 pub≠0 := by
    intro hz
    have hzero:=(MerkleEmpty.empty_view hl hz).2 B_BYTES true msg
    omega
  obtain ⟨v,hw,hT⟩:=MerkleEmpty.nonempty_view hl hnon
  have hv:=node_bound hl.log_le hT
  rw [(hT B_BYTES msg).1] at hm
  obtain ⟨m,hm,heq⟩:=List.mem_map.mp (List.count_pos_iff.mp hm)
  have hsafe:=ProcPriorMerkleByteTag.semantic (MerklePublic.aliasPublic pub) v hv hm
  have hhead:msg.headD 0=Fp.ofNat (m.headD 0) := by
    rw [←heq]
    cases m <;> rfl
  rw [hhead,Fp.toNat_ofNat,Nat.mod_eq_of_lt hsafe.1]
  exact hsafe.2
end ZkFormal.NearV3.Candidates.ProcessRepairForeignByteTags
