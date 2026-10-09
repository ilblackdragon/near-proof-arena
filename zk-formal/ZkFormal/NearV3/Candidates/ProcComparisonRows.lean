import ZkFormal.NearV3.Candidates.ProcConcatGeometry
import ZkFormal.NearV3.Candidates.ProcActualRoundComparisonInventory
import ZkFormal.NearV3.Candidates.ProcBoundaryRepair
namespace ZkFormal.NearV3.Candidates.ProcComparisonRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete

def messages (X : PV) := rowTraffic ProcBoundaryRepair.table.interactions
  ⟨fun _=>22,fun _ _ c=>Fp.ofNat (X.cell c)⟩ 0 0 [] B_SCMP true

theorem eval (X : PV) : messages X=
    List.replicate (if Fp.ofNat X.cg=1 then 1 else 0) [Fp.ofNat X.cx,Fp.ofNat X.cy,1] := by
  simp [messages,ProcBoundaryRepair.table,Proc.table,Proc.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    PV.cell,Proc.cg,Proc.cx,Proc.cy,B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC]
  exact Or.inr rfl

theorem key (R : Run) (i : Nat) : messages (keyV R i)=[] := by
  rw [eval]
  simp [keyV,zeroV,show Fp.ofNat 0=(0:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem tail (R : Run) : messages (tailV R)=[] := by
  rw [eval]
  simp [tailV,zeroV,show Fp.ofNat 0=(0:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem pad : messages padPV=[] := by
  rw [eval]
  simp [padPV,zeroV,show Fp.ofNat 0=(0:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem round (R : Run) (rd : Gen.RoundD) :
    (roundVs R rd).flatMap messages=(ProcActualRoundComparisonInventory.requests rd).map cmpMsg := by
  simp only [roundVs,List.flatMap_cons,List.flatMap_map]
  have he (i : Nat) : messages (entV R rd rd.entries.toArray i)=cmpMsg (ProcActualRoundComparisonInventory.entryRequest rd i)::[] := by
    rw [eval]
    simp [entV,cmpMsg,ProcActualRoundComparisonInventory.entryRequest,show Fp.ofNat 1=(1:Fp) from rfl]
  simp only [he]
  rw [←List.map_eq_flatMap]
  rw [eval]
  by_cases hk:rd.K=0
  all_goals simp [hdrV,b2n,hk,ProcActualRoundComparisonInventory.requests,List.map_append,cmpMsg,
    show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,show (0:Fp)≠1 from by decide +kernel]

theorem run (R : Run) : (procVs R).flatMap messages=
    (R.rounds.flatMap ProcActualRoundComparisonInventory.requests).map cmpMsg := by
  rw [procVs,List.flatMap_append]
  have hz:(keyVs R).flatMap messages=[] := by
    simp [keyVs,List.flatMap_map,key]
  rw [hz,List.nil_append,List.flatMap_assoc,List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  exact round R rd
end ZkFormal.NearV3.Candidates.ProcComparisonRows
