import ZkFormal.NearV3.Candidates.ProcRecordAllTraffic
namespace ZkFormal.NearV3.Candidates.ProcRecordParameterTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorRecordTable ProcPriorRecordRows

theorem header_message (ids : List Nat) (tv : Nat) :
    ProcRecordAllTraffic.messages (ProcPriorRecordCells.header ids tv) 76 false=
    [[Fp.ofNat tv,Fp.ofNat ids.length]] := by
  simp [ProcRecordAllTraffic.messages,ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,header,words,act,sender,receiver,amount,tau,shards,ProcPriorRecordCells.header,ProcPriorRecordCells.cell,ProcPriorCells.bit]
  rfl

theorem data_message (ids : List Nat) (tv : Nat) (r : Row) (hw:r.word<3) :
    ProcRecordAllTraffic.messages (ProcPriorRecordCells.cell ids tv r) 76 false=[] := by
  have hh:r.word=0∨r.word=1∨r.word=2:=by omega
  rcases hh with hh|hh|hh <;> simp [ProcRecordAllTraffic.messages,ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,header,words,act,sender,receiver,amount,tau,shards,ProcPriorRecordCells.header,ProcPriorRecordCells.cell,ProcPriorCells.bit,hh] <;> decide +kernel

theorem block (ids : List Nat) (b : NativeBlock) :
    (ProcRecordConcatTraffic.blockRows ids b).flatMap (fun row=>ProcRecordAllTraffic.messages row 76 false)=
    [[Fp.ofNat b.run.tau,Fp.ofNat ids.length]] := by
  simp only [ProcRecordConcatTraffic.blockRows,List.flatMap_cons,header_message,List.flatMap_assoc,List.flatMap_map]
  have hz:(List.range b.old.links.length).flatMap (fun j=>
      (rowsFor (b.old.links.getD j ⟨0,0,0⟩) j).flatMap
        (fun r=>ProcRecordAllTraffic.messages (ProcPriorRecordCells.cell ids b.run.tau r) 76 false))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j hj
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    apply data_message
    obtain ⟨w,hw,hr⟩:=List.mem_flatMap.mp hr
    obtain ⟨ll,hll,he⟩:=List.mem_map.mp hr
    subst r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    change w<3
    omega
  rw [hz,List.append_nil]

theorem physical (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcRecordConcatTraffic.rows ids bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRecordLinear.interactions 75 71 72 67 76) (ProcRecordConcatTraffic.trace ids bs) t r pub 76 false)=
    bs.map (fun b=>[Fp.ofNat b.run.tau,Fp.ofNat (ids b).length]) := by
  rw [ProcRecordAllTraffic.physical ids bs hcap,show
    bs.flatMap (fun b=>(ProcRecordConcatTraffic.blockRows (ids b) b).flatMap (fun row=>ProcRecordAllTraffic.messages row 76 false))=
    bs.flatMap (fun b=>[[Fp.ofNat b.run.tau,Fp.ofNat (ids b).length]]) from
    congrArg List.flatten (List.map_congr_left (fun b _=>block (ids b) b))]
  exact List.map_eq_flatMap.symm
end ZkFormal.NearV3.Candidates.ProcRecordParameterTraffic
