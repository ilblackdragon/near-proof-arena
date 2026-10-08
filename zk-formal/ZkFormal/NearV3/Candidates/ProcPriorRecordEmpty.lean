import ZkFormal.NearV3.Candidates.ProcPriorRecordHeader
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordEmpty
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open NearSpec NearSpec.Bandwidth
open ProcPriorCells ProcPriorRecordTable ProcPriorRecordCells

theorem empty_constraints (ids : List Nat) (tau : Nat)
    (fi : Fp) (hf:fi=0 ∨ tau=0) (e : Expr) (he:e∈constraints) :
    e.evalWith (env (ProcPriorRecordCells.header ids tau)
      (fun _=>0) fi 0 1)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hzero:Fp.ofNat 0=(0:Fp):=rfl
  have hf0:fi*Fp.ofNat tau=0:=by
    rcases hf with hf|hf
    · subst fi; grind
    · subst tau; rw [hzero]; grind
  have hz (x:Fp):(0:Fp)*x=0:=by grind
  have hzf (x:Fp):x*(0:Fp)=0:=by grind
  have ho (x:Fp):(1:Fp)*x=x:=by grind
  have ha (x:Fp):(0:Fp)+x=x:=by grind
  have hself (x:Fp):x+ -x=0:=by grind
  have hf:constraints.map (·.evalWith (env (ProcPriorRecordCells.header ids tau)
      (fun _=>0) fi 0 1))=List.replicate constraints.length (0:Fp) := by
    simp [constraints,ZkFormal.Chacha.Table.boolC,ProcPriorRecordTable.header,words,limbs,packed,
      adjacent,sameRecord,sameWord,notE,sub,k,c,n,Expr.evalWith,env,
      ProcPriorRecordCells.header,ProcPriorRecordCells.cell,
      act,ProcPriorRecordTable.tau,record,shards,sender,receiver,amount,firstLimb,midLimb,topLimb,
      byte0,byte1,byte2,lo,mid,hi,senderFound,senderIndex,receiverFound,receiverIndex,
      big,bigInv,writeGate,bit,hone,hzero,hz,hzf,ho,ha,hself,List.replicate]
    grind
  have hm:e.evalWith (env (ProcPriorRecordCells.header ids tau)
      (fun _=>0) fi 0 1)∈
      constraints.map (·.evalWith (env (ProcPriorRecordCells.header ids tau)
      (fun _=>0) fi 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcPriorRecordEmpty
