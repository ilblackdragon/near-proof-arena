import ZkFormal.PQ.Aggregation.D3Recursion

/-!
# `D3RecursionAudit` — axiom audit for the recursive-step foundation

Prints the axiom set of each theorem in `Aggregation/D3Recursion.lean`.  Requirement: every one is
within `{propext, Classical.choice, Quot.sound}`.  Run with
`lake env lean ZkFormal/PQ/Aggregation/D3RecursionAudit.lean`.
-/

open ZkFormal.PQ.Aggregation

#print axioms ZkFormal.PQ.Aggregation.d3Stmt_merge_accepted
#print axioms ZkFormal.PQ.Aggregation.d3Stmt_compose₂_accepted
#print axioms ZkFormal.PQ.Aggregation.d3Stmt_composeFrom_accepted
#print axioms ZkFormal.PQ.Aggregation.d3Stmt_compose_accepted
#print axioms ZkFormal.PQ.Aggregation.d3Stmt_tree_sound
#print axioms ZkFormal.PQ.Aggregation.d3Stmt_root_boundary
