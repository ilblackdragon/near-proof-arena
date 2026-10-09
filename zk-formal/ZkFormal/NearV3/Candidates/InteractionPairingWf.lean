import ZkFormal.NearV3.Candidates.InteractionPairing
namespace ZkFormal.NearV3.Candidates.InteractionPairing
open ZkFormal.Air

theorem exprs_perm (T : Air.Table) :
    ({T with interactions:=reorder T.interactions}:Air.Table).exprs.Perm T.exprs :=
  List.Perm.append_left _ (List.Perm.flatMap_right _ (reorder_perm T.interactions))

theorem constraints_perm (T : Air.Table) :
    ({T with interactions:=reorder T.interactions}:Air.Table).allConstraints.Perm T.allConstraints :=
  List.Perm.append_left _ (List.Perm.flatMap_right _ (reorder_perm T.interactions))

/-- Reordering changes auxiliary grouping, but cannot change expression bounds,
constraint degrees, bus bounds, or multiplicity bit bounds. -/
theorem wf (T : Air.Table) (A : Air) (degree : Nat) :
    ({T with interactions:=reorder T.interactions}:Air.Table).wf A degree=T.wf A degree := by
  unfold Table.wf
  rw [(exprs_perm T).all_eq,(constraints_perm T).all_eq]
  rw [(reorder_perm T.interactions).all_eq]

end ZkFormal.NearV3.Candidates.InteractionPairing
