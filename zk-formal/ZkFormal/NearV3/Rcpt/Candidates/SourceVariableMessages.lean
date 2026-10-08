import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableSound
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22MessageSplice

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

/-- Last-table acceptance forces complete endpoint silence, including the SIZE
gate. This is derived from actual physical constraints, not supplied separately. -/
theorem last_endpoint_silent {tr : Trace Fp} {d : Nat} {pub : List Fp}
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub) (bb : Nat) (sd : Bool) :
    cellMessages (tr.cell d (tr.height d-1)) bb sd=[] := by
  have hp : 0<tr.height d := Nat.two_pow_pos _
  have hi : Inactive (tr.cell d (tr.height d-1)) :=
    endpoint_inactive (pub:=pub) (by omega) (hd.constr _ (by omega))
  exact cell_messages_zero _ hi.sg hi.rt hi.gd hi.gz bb sd

/-- Logical power-of-two padding is silent for arbitrary unequal physical
heights. Only local height admission and the actual final endpoint are needed. -/
theorem variable_messages_splice {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (bb : Nat) (sd : Bool) :
    physicalMessages (DedupTable.table 24) (variableTrace tr a b c d) 0 pub bb sd=
      (List.range ((tr.height a-1)+(tr.height b-1)+(tr.height c-1)+tr.height d)).flatMap
      (fun r => cellMessages
        (variableCells (tr.height a-1) (tr.height b-1) (tr.height c-1)
          (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d) r) bb sd) := by
  have hA := local_height_bounds ha (by decide)
  have hB := local_height_bounds hb (by decide)
  have hC := local_height_bounds hc (by decide)
  have hD := local_height_bounds hd (by decide)
  let n := ownedSteps tr a b c d
  let C := variableCells (tr.height a-1) (tr.height b-1) (tr.height c-1)
    (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d)
  have hn : n≤2^24 := by dsimp [n,ownedSteps]; omega
  have hz : cellMessages (C n) bb sd=[] := by
    dsimp only [C,n,ownedSteps]
    rw [variable_terminal]
    exact last_endpoint_silent hd bb sd
  have hclamp := clamped_messages (2^24) n hn C (fun cell => cellMessages cell bb sd) hz
  have he : (tr.height a-1)+(tr.height b-1)+(tr.height c-1)+tr.height d=n+1 := by
    dsimp [n,ownedSteps]; omega
  rw [he]
  have hphysical : (List.range (n+1)).flatMap (fun r => cellMessages (C r) bb sd)=
      (List.range n).flatMap (fun r => cellMessages (C r) bb sd) := by
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,hz,List.append_nil]
  change physicalMessages (DedupTable.table 24) (variableTrace tr a b c d) 0 pub bb sd=
    (List.range (n+1)).flatMap (fun r => cellMessages (C r) bb sd)
  rw [hphysical]
  simpa only [physicalMessages,DedupTable.table,source_row_messages,variable_height,
    variableTrace,terminalPad,Trace.height,C,n] using hclamp

/-- Arbitrary locally accepted physical source traces and their reconstructed
logical trace have identical external messages. No honest placement, equal
height, or carry-equality premise is needed for this traffic identity. -/
theorem variable_external_messages {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) :
    physicalMessages firstTable tr a pub bb sd ++
      physicalMessages (middleTable 64 65) tr b pub bb sd ++
      physicalMessages (middleTable 65 66) tr c pub bb sd ++
      physicalMessages lastTable tr d pub bb sd=
    physicalMessages (DedupTable.table 24) (variableTrace tr a b c d) 0 pub bb sd := by
  rw [physical_four_splice tr a b c d pub bb sd h0 h1 h2,variable_messages_splice ha hb hc hd]
  rfl

/-- SIZE decoration commutes with arbitrary physical reconstruction too. -/
theorem counted_variable_external_messages {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) :
    physicalMessages (SizeCount.sourceTable firstTable) tr a pub bb sd ++
      physicalMessages (SizeCount.sourceTable (middleTable 64 65)) tr b pub bb sd ++
      physicalMessages (SizeCount.sourceTable (middleTable 65 66)) tr c pub bb sd ++
      physicalMessages (SizeCount.sourceTable lastTable) tr d pub bb sd=
    physicalMessages (SizeCount.sourceTable (DedupTable.table 24))
      (variableTrace tr a b c d) 0 pub bb sd := by
  rw [counted_four_messages,variable_external_messages ha hb hc hd bb sd h0 h1 h2,counted_messages]

/-- The same equality is available in the protocol's natural multiplicity form. -/
theorem counted_variable_external_counts {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (bb : Nat) (sd : Bool) (h0 : bb≠64) (h1 : bb≠65) (h2 : bb≠66) (m : List Fp) :
    tableBusCount (SizeCount.sourceTable firstTable).interactions tr a pub bb sd m +
    tableBusCount (SizeCount.sourceTable (middleTable 64 65)).interactions tr b pub bb sd m +
    tableBusCount (SizeCount.sourceTable (middleTable 65 66)).interactions tr c pub bb sd m +
    tableBusCount (SizeCount.sourceTable lastTable).interactions tr d pub bb sd m=
    tableBusCount (SizeCount.sourceTable (DedupTable.table 24)).interactions
      (variableTrace tr a b c d) 0 pub bb sd m := by
  have h := congrArg (fun xs => xs.count m)
    (counted_variable_external_messages ha hb hc hd bb sd h0 h1 h2)
  simpa only [List.count_append,physicalMessages,tableBusCount_eq] using h

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
