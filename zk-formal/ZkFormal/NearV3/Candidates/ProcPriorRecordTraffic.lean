import ZkFormal.NearV3.Candidates.ProcPriorRecordCells
import ZkFormal.NearV3.Candidates.ProcRawNativeBytesList
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordTraffic
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorRecordRows

def messages (row : Nat→Fp) : List (List Fp) :=
  rowTraffic (ProcPriorRecordTable.interactions 75 71 72 67 76)
    ⟨fun _=>22,fun _ _=>row⟩ 0 0 [] 75 false

def bytes (tau j : Nat) (r : LinkAllowance) : List (List Fp) :=
  (List.range 24).map fun g=>[Fp.ofNat tau,Fp.ofNat j,Fp.ofNat g,Fp.ofNat (r.encode.getD g 0).toNat]

theorem row (row : Nat→Fp) : messages row=
    List.replicate (if row 4+row 5+row 6=1 then 1 else 0)
      [row 1,row 2,8*(row 5+2*row 6)+3*(row 8+2*row 9),row 10] ++
    List.replicate (if row 4+row 5+row 6=1 then 1 else 0)
      [row 1,row 2,8*(row 5+2*row 6)+3*(row 8+2*row 9)+1,row 11] ++
    List.replicate (if row 4+row 5+row 6-row 9=1 then 1 else 0)
      [row 1,row 2,8*(row 5+2*row 6)+3*(row 8+2*row 9)+2,row 12] := by
  simp [messages,rowTraffic,ProcPriorRecordTable.interactions,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    ProcPriorRecordTable.words,ProcPriorRecordTable.offset,ProcPriorRecordTable.act,
    ProcPriorRecordTable.tau,ProcPriorRecordTable.record,ProcPriorRecordTable.sender,
    ProcPriorRecordTable.receiver,ProcPriorRecordTable.amount,ProcPriorRecordTable.midLimb,
    ProcPriorRecordTable.topLimb,ProcPriorRecordTable.byte0,ProcPriorRecordTable.byte1,
    ProcPriorRecordTable.byte2,ZkFormal.Chacha.Table.E.sub,List.append_assoc]
  all_goals first | rfl | grind

theorem header (ids : List Nat) (tau : Nat) :
    messages (ProcPriorRecordCells.header ids tau)=[] := by
  rw [row]
  simp [ProcPriorRecordCells.header]
  all_goals grind

theorem record (ids : List Nat) (tau j : Nat) (r : LinkAllowance) :
    (rowsFor r j).flatMap (fun x=>messages (ProcPriorRecordCells.cell ids tau x))=bytes tau j r := by
  simp [rowsFor,row,ProcPriorRecordCells.cell,ProcPriorCells.bit,value,bytes,
    ProcPriorRecordLimbs.digit,LinkAllowance.encode,u64,leN,List.range_succ,List.getD]
  rfl
end ZkFormal.NearV3.Candidates.ProcPriorRecordTraffic
