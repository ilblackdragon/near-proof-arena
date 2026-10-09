import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryBalance
import ZkFormal.NearV3.Candidates.ProcRecordWriteTraffic
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest

def writeMessage (a : Tagged) : List Fp :=ProcRecordWriteTraffic.message a.tau a.row.event
def writeMessages (xs : List Tagged) : List (List Fp) :=
  xs.flatMap (fun a=>if a.row.event.query then [] else [writeMessage a])

theorem row_write (xs : List Tagged) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorMemoryTable.interactions 67 68 69) (trace xs) t r pub 67 false=
      match xs[r]? with | none=>[] | some a=>if a.row.event.query then [] else [writeMessage a] := by
  cases ha:xs[r]? with
  | none =>
    simp [rowTraffic,ProcPriorMemoryTable.interactions,Interaction.multNat,Interaction.multNat.go,
      Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,trace,cells,ha,ZkFormal.Chacha.Table.E.c,
      ProcPriorMemoryTable.act,ProcPriorMemoryTable.query,ProcPriorMemoryTable.notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k]
    decide +kernel
  | some a =>
    cases hq:a.row.event.query <;>
      simp [rowTraffic,ProcPriorMemoryTable.interactions,Interaction.multNat,Interaction.multNat.go,
        Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,trace,cells,ha,ZkFormal.Chacha.Table.E.c,
        ProcPriorMemoryTable.act,ProcPriorMemoryTable.query,ProcPriorCells.cell,ProcPriorCells.bit,hq,
        ProcPriorMemoryTable.tau,ProcPriorMemoryTable.link,ProcPriorMemoryTable.lo,ProcPriorMemoryTable.hi,ProcPriorMemoryTable.stamp,ProcPriorMemoryTable.notE,
        ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,writeMessage,ProcRecordWriteTraffic.message]
    all_goals grind

theorem physical_writes (xs : List Tagged) (hc:xs.length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic (ProcPriorMemoryTable.interactions 67 68 69)
      (trace xs) t r pub 67 false)=writeMessages xs := by
  simp only [row_write]
  rw [show 2^22=xs.length+(2^22-xs.length) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-xs.length)).flatMap (fun j=>match xs[xs.length+j]? with
      | none=>[] | some a=>if a.row.event.query then [] else [writeMessage a])=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [List.getElem?_eq_none (by omega)]
  rw [hz,List.append_nil]
  have hi:(List.range xs.length).map (fun r=>xs[r]!)=xs := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact getElem!_pos xs i hj
  unfold writeMessages
  conv => rhs; rw [←hi,List.flatMap_map]
  apply ProcCodecPublicIdEnumeration.flat_congr
  intro j hj
  rw [List.getElem?_eq_getElem (List.mem_range.mp hj),getElem!_pos xs j (List.mem_range.mp hj)]

end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
