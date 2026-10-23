import NearCompression.RecursiveSharedBranches
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def recursiveSharedOutputNodes (start target even odd : Nat) : List (TerminalDAGNode K) :=
  [.input target,.input (target+1),.binary .sub even start,.binary .sub odd (start+1)]

omit [Field K] in
theorem recursive_shared_output_acyclic (start target even odd : Nat) (he : even<start) (ho : odd<start) :
    TerminalDAGAcyclic start (recursiveSharedOutputNodes (K:=K) start target even odd) := by
  simp only [recursiveSharedOutputNodes,TerminalDAGAcyclic,TerminalNodeBefore,true_and,and_true]
  grind

theorem recursive_shared_output_value (start target even odd : Nat) (inputs previous : Nat → K)
    (he : even<start) (ho : odd<start) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedOutputNodes start target even odd)
    result (start+2)=previous even-inputs target ∧ result (start+3)=previous odd-inputs (target+1) := by
  dsimp only
  let nodes:=recursiveSharedOutputNodes (K:=K) start target even odd
  have ac:=recursive_shared_output_acyclic (K:=K) start target even odd he ho
  have h0:=terminal_dag_node_equation inputs previous nodes start ac 0 (by simp [nodes,recursiveSharedOutputNodes])
  have h1:=terminal_dag_node_equation inputs previous nodes start ac 1 (by simp [nodes,recursiveSharedOutputNodes])
  have h2:=terminal_dag_node_equation inputs previous nodes start ac 2 (by simp [nodes,recursiveSharedOutputNodes])
  have h3:=terminal_dag_node_equation inputs previous nodes start ac 3 (by simp [nodes,recursiveSharedOutputNodes])
  have pe:=terminal_dag_preserves_earlier inputs previous nodes start even he
  have po:=terminal_dag_preserves_earlier inputs previous nodes start odd ho
  simp only [nodes,recursiveSharedOutputNodes,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero,terminalNodeValue,gkrGateValue] at h0 h1 h2 h3
  change terminalDAGRun inputs start previous nodes start=inputs target at h0
  change terminalDAGRun inputs start previous nodes (start+1)=inputs (target+1) at h1
  change terminalDAGRun inputs start previous nodes (start+2)=terminalDAGRun inputs start previous nodes even-terminalDAGRun inputs start previous nodes start at h2
  change terminalDAGRun inputs start previous nodes (start+3)=terminalDAGRun inputs start previous nodes odd-terminalDAGRun inputs start previous nodes (start+1) at h3
  change terminalDAGRun inputs start previous nodes (start+2)=_ ∧terminalDAGRun inputs start previous nodes (start+3)=_
  grind

def recursiveSharedQueryCost (query : RecursiveSourceQuery) : Nat := recursiveSharedBranchesCost query.branches+4

def recursiveSharedQueryNodes (start : Nat) (query : RecursiveSourceQuery) : List (TerminalDAGNode K) :=
  recursiveSharedBranchesProgram start 0 0 0 query.branches ++
    recursiveSharedOutputNodes (start+recursiveSharedBranchesCost query.branches) query.expectedStart
      (recursiveSharedBranchesIndex start 0 false query.branches) (recursiveSharedBranchesIndex start 0 true query.branches)

omit [Field K] in
theorem recursive_shared_query_length (start : Nat) (query : RecursiveSourceQuery) :
    (recursiveSharedQueryNodes (K:=K) start query).length=recursiveSharedQueryCost query := by
  simp only [recursiveSharedQueryNodes,List.length_append,recursive_shared_branches_length,
    recursiveSharedOutputNodes,List.length_cons,List.length_nil,recursiveSharedQueryCost]

theorem recursive_shared_query_acyclic (start : Nat) (query : RecursiveSourceQuery) (positive : 0<start) :
    TerminalDAGAcyclic start (recursiveSharedQueryNodes (K:=K) start query) := by
  apply recursive_shared_acyclic_append
  · exact recursive_shared_branches_acyclic start 0 0 0 query.branches positive positive positive
  · rw [recursive_shared_branches_length]
    exact recursive_shared_output_acyclic _ _ _ _
      (recursive_shared_branches_index_bound start 0 false query.branches positive)
      (recursive_shared_branches_index_bound start 0 true query.branches positive)

/-- Exact compiled query, including shared source target input nodes. -/
theorem recursive_shared_query_value (start : Nat) (query : RecursiveSourceQuery)
    (inputs previous : Nat → K) (positive : 0<start) (zero : previous 0=0) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedQueryNodes start query)
    result (start+recursiveSharedBranchesCost query.branches+2)=recursiveSourceOutputValue inputs query false ∧
    result (start+recursiveSharedBranchesCost query.branches+3)=recursiveSourceOutputValue inputs query true := by
  dsimp only
  rw [recursiveSharedQueryNodes,recursive_shared_run_append,recursive_shared_branches_length]
  let middle:=terminalDAGRun inputs start previous (recursiveSharedBranchesProgram start 0 0 0 query.branches)
  have branch:=recursive_shared_branches_value start 0 0 0 query.branches inputs previous positive positive positive zero
  have output:=recursive_shared_output_value (start+recursiveSharedBranchesCost query.branches) query.expectedStart
    (recursiveSharedBranchesIndex start 0 false query.branches) (recursiveSharedBranchesIndex start 0 true query.branches)
    inputs middle (recursive_shared_branches_index_bound start 0 false query.branches positive)
      (recursive_shared_branches_index_bound start 0 true query.branches positive)
  dsimp only at branch
  rw [zero] at branch
  dsimp only [middle] at output
  rw [branch.1,branch.2] at output
  simpa only [recursiveSourceOutputValue,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using output


def recursiveSharedQueriesCost : List RecursiveSourceQuery → Nat
  | [] => 0
  | query::rest => recursiveSharedQueryCost query+recursiveSharedQueriesCost rest

def recursiveSharedQueriesNodes (start : Nat) : List RecursiveSourceQuery → List (TerminalDAGNode K)
  | [] => []
  | query::rest => recursiveSharedQueryNodes start query ++
      recursiveSharedQueriesNodes (start+recursiveSharedQueryCost query) rest

def recursiveSharedQueriesOutputs (start : Nat) : List RecursiveSourceQuery → List Nat
  | [] => []
  | query::rest => [start+recursiveSharedBranchesCost query.branches+2,start+recursiveSharedBranchesCost query.branches+3] ++
      recursiveSharedQueriesOutputs (start+recursiveSharedQueryCost query) rest

omit [Field K] in
theorem recursive_shared_queries_length (start : Nat) (queries : List RecursiveSourceQuery) :
    (recursiveSharedQueriesNodes (K:=K) start queries).length=recursiveSharedQueriesCost queries := by
  induction queries generalizing start with
  | nil => rfl
  | cons q qs ih => simp only [recursiveSharedQueriesNodes,List.length_append,recursive_shared_query_length,ih,recursiveSharedQueriesCost]

theorem recursive_shared_queries_output_count (start : Nat) (queries : List RecursiveSourceQuery) :
    (recursiveSharedQueriesOutputs start queries).length=2*queries.length := by
  induction queries generalizing start with
  | nil => rfl
  | cons q qs ih =>
    simp only [recursiveSharedQueriesOutputs,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem recursive_shared_queries_acyclic (start : Nat) (queries : List RecursiveSourceQuery)
    (positive : 0<start) : TerminalDAGAcyclic start (recursiveSharedQueriesNodes (K:=K) start queries) := by
  induction queries generalizing start with
  | nil => trivial
  | cons q qs ih =>
    apply recursive_shared_acyclic_append
    · exact recursive_shared_query_acyclic start q positive
    · rw [recursive_shared_query_length]
      exact ih _ (by omega)

/-- All query outputs read from the final shared DAG, including preservation
of earlier query outputs while subsequent queries append their nodes. -/
theorem recursive_shared_queries_value (start : Nat) (queries : List RecursiveSourceQuery)
    (inputs previous : Nat → K) (positive : 0<start) (zero : previous 0=0) :
    (recursiveSharedQueriesOutputs start queries).map
      (terminalDAGRun inputs start previous (recursiveSharedQueriesNodes start queries))=
    queries.flatMap (fun q=>[false,true].map (fun side=>recursiveSourceOutputValue inputs q side)) := by
  induction queries generalizing start previous with
  | nil => rfl
  | cons q qs ih =>
    rw [recursiveSharedQueriesNodes,recursive_shared_run_append,recursive_shared_query_length]
    let middle:=terminalDAGRun inputs start previous (recursiveSharedQueryNodes start q)
    have first:=recursive_shared_query_value start q inputs previous positive zero
    have mz : middle 0=0 := by
      unfold middle
      rw [terminal_dag_preserves_earlier inputs previous _ start 0 positive]
      exact zero
    have rest:=ih (start+recursiveSharedQueryCost q) middle (by omega) mz
    have e:=terminal_dag_preserves_earlier inputs middle
      (recursiveSharedQueriesNodes (start+recursiveSharedQueryCost q) qs)
      (start+recursiveSharedQueryCost q) (start+recursiveSharedBranchesCost q.branches+2)
      (by simp only [recursiveSharedQueryCost];omega)
    have o:=terminal_dag_preserves_earlier inputs middle
      (recursiveSharedQueriesNodes (start+recursiveSharedQueryCost q) qs)
      (start+recursiveSharedQueryCost q) (start+recursiveSharedBranchesCost q.branches+3)
      (by simp only [recursiveSharedQueryCost];omega)
    dsimp only at first
    change middle (start+recursiveSharedBranchesCost q.branches+2)=_ ∧
      middle (start+recursiveSharedBranchesCost q.branches+3)=_ at first
    change (recursiveSharedQueriesOutputs start (q::qs)).map
      (terminalDAGRun inputs (start+recursiveSharedQueryCost q) middle
        (recursiveSharedQueriesNodes (start+recursiveSharedQueryCost q) qs))=_
    simp only [recursiveSharedQueriesOutputs,List.map_append,List.map_cons,List.map_nil,List.flatMap_cons]
    rw [e,o,first.1,first.2,rest]
    simp only [List.map_cons,List.map_nil]

/-- One shared zero node, followed by the exact stateful emitter. -/
def recursiveSharedSourceNodes (queries : List RecursiveSourceQuery) : List (TerminalDAGNode K) :=
  .constant 0 :: recursiveSharedQueriesNodes 1 queries

theorem recursive_shared_source_acyclic (queries : List RecursiveSourceQuery) :
    TerminalDAGAcyclic 0 (recursiveSharedSourceNodes (K:=K) queries) :=
  ⟨True.intro,recursive_shared_queries_acyclic 1 queries (by decide)⟩

/-- Entire exact shared source compiler: no supplied route, node equations,
or callback correctness. Native metadata/operand authentication remains
external, and captured Python-layout equality is checked independently. -/
theorem recursive_shared_source_value (offset : Nat) (queries : List RecursiveSourceQuery)
    (values : Nat → K) :
    (recursiveSharedQueriesOutputs 1 queries).map
      (terminalDAGRun (fun i=>values (offset+i)) 0 (fun _=>0) (recursiveSharedSourceNodes queries))=
      recursiveSourceResiduals (recursiveSourceProgramPairs offset queries values) := by
  rw [recursiveSharedSourceNodes,terminalDAGRun]
  rw [recursive_shared_queries_value 1 queries _ _ (by decide) (by simp [terminalStore,terminalNodeValue])]
  exact (recursive_source_program_residuals offset queries values).symm

end NearCompression
