import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableProvider
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountChainPaid

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

/-- Every valid extracted source block has exactly its renderer SIZE charge;
skipped occurrences have empty paths, derived from local constraints. -/
theorem chain_size_charge {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hl : TableLocal (DedupTable.table 24) tr tt pub)
    {bs : List SrcpB} {stop : Nat} (hs : DedupProof.BlockChain tr tt 0 bs stop) :
    (bs.map fun B => B.L+33*B.path.length).sum=DedupRender.size bs := by
  have hw := hs.payload_wf hl
  unfold DedupRender.size
  congr 1
  apply List.map_congr_left
  intro B hb
  unfold DedupRender.sizeStep
  cases hd : B.dup
  · rfl
  · have hh := hw.blocks B hb
    simp only [hd,ite_true] at hh
    simp [hh.2.1]

/-- Traffic of any chain extracted from the same reconstructed trace is the
actual physical provider traffic; there is no independently chosen source view. -/
theorem provider_chain_messages {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hl : TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub)
    {bs : List SrcpB} {stop : Nat}
    (hs : DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) :
    providerMessages tr a b c d pub bb sd=
      ((DedupProof.sourceMsgs (variableTrace tr a b c d) 0 bs bb sd).map Msg.toFp).map
        (fun m => if bb=B_SIZE then m++[0] else m) := by
  rw [providerMessages,counted_variable_external_messages ha hb hc hd bb sd h0 h1 h2,counted_messages]
  exact congrArg (List.map _) (hs.all_traffic hl bb sd)

/-- Physical source SIZE equals the charge of that very same extracted chain. -/
theorem provider_chain_size {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hl : TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub)
    {bs : List SrcpB} {stop : Nat}
    (hs : DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop) :
    providerMessages tr a b c d pub B_SIZE true=[[2,(DedupRender.size bs:Fp),0]] := by
  have hh := provider_size (provider_chain_messages ha hb hc hd hl hs B_SIZE true
    (by decide) (by decide) (by decide))
  rw [chain_size_charge hl hs] at hh
  exact hh

/-- Exact field-message count transfer on every non-SIZE external source bus. -/
theorem provider_chain_count {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hl : TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub)
    {bs : List SrcpB} {stop : Nat}
    (hs : DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) (hsize : bb≠B_SIZE)
    (m : List Fp) :
    (providerMessages tr a b c d pub bb sd).count m=
      cnt (DedupProof.sourceMsgs (variableTrace tr a b c d) 0 bs bb sd) m := by
  rw [provider_chain_messages ha hb hc hd hl hs bb sd h0 h1 h2]
  simp only [hsize,ite_false,List.map_id']
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
