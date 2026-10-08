import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableExtract
import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableMessages

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

def providerMessages (tr : Trace Fp) (a b c d : Nat) (pub : List Fp) (bb : Nat) (sd : Bool) : List (List Fp) :=
  physicalMessages (SizeCount.sourceTable firstTable) tr a pub bb sd ++
    physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr b pub bb sd ++
    physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr c pub bb sd ++
    physicalMessages (SizeCount.sourceTable lastTable) tr d pub bb sd

/-- One recovered source chain accounts for every external physical message,
including the SIZE arity extension. Heights are arbitrary within the cap. -/
theorem physical_source_provider {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hbal : ∀ bus∈([64,65,66] : List Nat), ∀ m,
      boundaryCount tr a b c d pub bus true m=boundaryCount tr a b c d pub bus false m) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub ∧
      DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop ∧
      ∀ bb, bb≠64 → bb≠65 → bb≠66 → ∀ sd,
        providerMessages tr a b c d pub bb sd=
          ((DedupProof.sourceMsgs (variableTrace tr a b c d) 0 bs bb sd).map Msg.toFp).map
            (fun m => if bb=B_SIZE then m++[0] else m) := by
  obtain ⟨bs,stop,hl,hbs,_,_⟩ := balanced_source_blocks ha hb hc hd hbal
  refine ⟨bs,stop,hl,hbs,?_⟩
  intro bb h0 h1 h2 sd
  rw [providerMessages,counted_variable_external_messages ha hb hc hd bb sd h0 h1 h2,
    counted_messages]
  have hh := hbs.all_traffic hl bb sd
  change (physicalMessages (DedupTable.table 24) (variableTrace tr a b c d) 0 pub bb sd).map _ = _
  rw [show physicalMessages (DedupTable.table 24) (variableTrace tr a b c d) 0 pub bb sd=
      (DedupProof.sourceMsgs (variableTrace tr a b c d) 0 bs bb sd).map Msg.toFp from hh]

/-- The same semantic chain is paid exactly once by the four physical SIZE
senders, with zero native-store records charged to the source component. -/
theorem provider_size {tr : Trace Fp} {a b c d : Nat} {pub : List Fp} {bs : List SrcpB}
    (h : providerMessages tr a b c d pub B_SIZE true=
      ((DedupProof.sourceMsgs (variableTrace tr a b c d) 0 bs B_SIZE true).map Msg.toFp).map
        (fun m => if B_SIZE=B_SIZE then m++[0] else m)) :
    providerMessages tr a b c d pub B_SIZE true=
      [[2,(((bs.map fun B => B.L+33*B.path.length).sum:Nat):Fp),0]] := by
  rw [h]
  simp [DedupProof.sourceMsgs,Msg.toFp]
  exact ⟨rfl,rfl⟩

theorem physical_source_size_sender {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hbal : ∀ bus∈([64,65,66] : List Nat), ∀ m,
      boundaryCount tr a b c d pub bus true m=boundaryCount tr a b c d pub bus false m) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub ∧
      DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop ∧
      providerMessages tr a b c d pub B_SIZE true=
        [[2,(((bs.map fun B => B.L+33*B.path.length).sum:Nat):Fp),0]] := by
  obtain ⟨bs,stop,hl,hbs,hm⟩ := physical_source_provider ha hb hc hd hbal
  exact ⟨bs,stop,hl,hbs,provider_size (hm B_SIZE (by decide) (by decide) (by decide) true)⟩

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
