import ZkFormal.NearV3.Candidates.ProcPriorVertical4DataEval
import ZkFormal.NearV3.Candidates.ProcPriorIdPadding
import ZkFormal.NearV3.Candidates.ProcPriorRawPadding
import ZkFormal.NearV3.Candidates.ProcPriorRecordPadding
import ZkFormal.NearV3.Candidates.ProcPriorBoundary
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayPadding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorCells ProcPriorVertical4Linear

theorem memory (nxt : Nat→Fp) (fi la tr : Fp) (hn:tr=0 ∨ nxt 0=0)
    (e : Expr) (he:e∈(ProcPriorMemoryGated.table 67 68 69).constraints) :
    e.evalWith (env (fun _=>0) nxt fi la tr)=0 := by
  rcases List.mem_append.mp he with he|he
  · exact ProcPriorBoundary.padding_constraints nxt fi la tr hn e he
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    all_goals simp only [ZkFormal.Chacha.Table.boolC,ProcPriorMemoryGated.gateEq,ProcPriorMemoryGated.gateExpr,
      ProcPriorMemoryTable.adjacent,ProcPriorMemoryTable.notE,sub,c,n,k,Expr.evalWith,env,Bool.false_eq_true,ite_false,ite_true]
    all_goals grind

/-- Every selected component accepts an all-zero ending row with arbitrary
next-stage data. Therefore truncation occurs only at a proved padding row. -/
theorem constraints (T : Air.Table) (hT:T∈components) (nxt : Nat→Fp) (fi la tr : Fp)
    (hn:tr=0 ∨ nxt 0=0) (e : Expr) (he:e∈T.constraints) :
    e.evalWith (env (fun _=>0) nxt fi la tr)=0 := by
  simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hT
  rcases hT with rfl|rfl|rfl|rfl
  · exact memory nxt fi la tr hn e he
  · exact ProcPriorIdPadding.padding_constraints nxt fi la tr hn e he
  · exact ProcPriorRawPadding.padding_constraints nxt fi la tr hn e he
  · exact ProcPriorRecordPadding.padding_constraints nxt fi la tr hn e he

theorem multiplicity (T : Air.Table) (hT:T∈components) (nxt : Nat→Fp) (fi la tr : Fp)
    (i : Interaction) (hi:i∈T.interactions) (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (fun _=>0) nxt fi la tr)=0 := by
  have hzm (x:Fp):(0:Fp)*x=0:=by grind
  have hmz (x:Fp):x*(0:Fp)=0:=by grind
  have ha (x:Fp):(0:Fp)+x=x:=by grind
  have haz (x:Fp):x+(0:Fp)=x:=by grind
  have hnz:-(0:Fp)=0:=by grind
  have hf:(T.interactions.flatMap Interaction.mult).map (·.evalWith (env (fun _=>0) nxt fi la tr))=
      List.replicate (T.interactions.flatMap Interaction.mult).length (0:Fp) := by
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hT
    rcases hT with rfl|rfl|rfl|rfl
    all_goals simp [ProcPriorMemoryGated.table,ProcPriorMemoryGated.interactions,
      ProcPriorMemoryTable.table,ProcPriorMemoryTable.interactions,ProcPriorMemoryTable.adjacent,ProcPriorMemoryTable.notE,
      ProcPriorIdTable.table,ProcPriorIdTable.interactions,ProcPriorIdTable.adjacent,ProcPriorIdTable.notE,
      ProcPriorRawFrame.table,ProcPriorRawFrame.interactions,ProcPriorRecordLinear.table,ProcPriorRecordLinear.interactions,
      ProcPriorRecordTable.table,ProcPriorRecordTable.interactions,ProcPriorRecordTable.words,ProcPriorRecordTable.queryGate,
      ProcPriorRecordTable.header,sub,c,n,k,Expr.evalWith,env,hzm,hmz,ha,haz,hnz,List.replicate]
  have hm:e.evalWith (env (fun _=>0) nxt fi la tr)∈
      (T.interactions.flatMap Interaction.mult).map (·.evalWith (env (fun _=>0) nxt fi la tr)):=
    List.mem_map.mpr ⟨e,List.mem_flatMap.mpr ⟨i,hi,he⟩,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2
end ZkFormal.NearV3.Candidates.ProcPriorOverlayPadding
