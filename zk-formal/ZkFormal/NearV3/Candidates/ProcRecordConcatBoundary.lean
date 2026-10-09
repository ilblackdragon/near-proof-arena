import ZkFormal.NearV3.Candidates.ProcPriorRecordLocal
namespace ZkFormal.NearV3.Candidates.ProcRecordConcatBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler
open ProcPriorCells ProcPriorRecordRows ProcPriorRecordTable ProcPriorRecordCells

theorem end_header (ids nextIds : List Nat) (tau j : Nat) (r : LinkAllowance)
    (hv:value ⟨j,2,2,r⟩<18446744073709551616) (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cell ids tau ⟨j,2,2,r⟩) (ProcPriorRecordCells.header nextIds (tau+1)) 0 0 1)=0 := by
  have ht:Fp.ofNat (tau+1)=Fp.ofNat tau+1:=by change ((tau+1:Nat):Fp)=(tau:Fp)+1; grind
  have hz:Fp.ofNat 0=(0:Fp):=rfl
  have ho:Fp.ofNat 1=(1:Fp):=rfl
  have hm:constraints.map (fun e=>e.evalWith
      (env (cell ids tau ⟨j,2,2,r⟩) (ProcPriorRecordCells.header nextIds (tau+1)) 0 0 1))=
      constraints.map (fun e=>e.evalWith (env (cell ids tau ⟨j,2,2,r⟩) (fun _=>0) 0 0 1)) := by
    simp [constraints,ZkFormal.Chacha.Table.boolC,ProcPriorRecordTable.header,words,limbs,packed,
      adjacent,sameRecord,sameWord,notE,sub,k,c,n,Expr.evalWith,env,
      ProcPriorRecordCells.header,ProcPriorRecordCells.cell,act,ProcPriorRecordTable.tau,record,shards,
      sender,receiver,amount,firstLimb,midLimb,topLimb,byte0,byte1,byte2,lo,mid,hi,
      senderFound,senderIndex,receiverFound,receiverIndex,big,bigInv,writeGate,bit,hz,ho,ht]
    all_goals grind
  rw [List.map_inj_left.mp hm e he]
  exact ProcPriorRecordEnd.end_constraints ids tau j r hv e he

theorem empty_header (ids nextIds : List Nat) (tau : Nat) (fi : Fp)
    (hf:fi=0 ∨ tau=0) (e : Expr) (he:e∈constraints) :
    e.evalWith (env (ProcPriorRecordCells.header ids tau)
      (ProcPriorRecordCells.header nextIds (tau+1)) fi 0 1)=0 := by
  have ht:Fp.ofNat (tau+1)=Fp.ofNat tau+1:=by change ((tau+1:Nat):Fp)=(tau:Fp)+1; grind
  have hz:Fp.ofNat 0=(0:Fp):=rfl
  have ho:Fp.ofNat 1=(1:Fp):=rfl
  have hm:constraints.map (fun e=>e.evalWith (env (ProcPriorRecordCells.header ids tau)
      (ProcPriorRecordCells.header nextIds (tau+1)) fi 0 1))=
      constraints.map (fun e=>e.evalWith (env (ProcPriorRecordCells.header ids tau) (fun _=>0) fi 0 1)) := by
    simp [constraints,ZkFormal.Chacha.Table.boolC,ProcPriorRecordTable.header,words,limbs,packed,
      adjacent,sameRecord,sameWord,notE,sub,k,c,n,Expr.evalWith,env,
      ProcPriorRecordCells.header,act,ProcPriorRecordTable.tau,record,shards,
      sender,receiver,amount,firstLimb,midLimb,topLimb,byte0,byte1,byte2,lo,mid,hi,
      senderFound,senderIndex,receiverFound,receiverIndex,big,bigInv,writeGate,hz,ho,ht]
    all_goals grind
  rw [List.map_inj_left.mp hm e he]
  exact ProcPriorRecordEmpty.empty_constraints ids tau fi hf e he
end ZkFormal.NearV3.Candidates.ProcRecordConcatBoundary
