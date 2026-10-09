import ZkFormal.NearV3.Candidates.ProcModelStep
namespace ZkFormal.NearV3.Candidates.ProcPushPerm
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem insert_perm (p : Push) (ps : List Push) : (insertTs p ps).Perm (p::ps) := by
  induction ps with
  | nil => exact List.Perm.refl _
  | cons q qs ih =>
    simp only [insertTs]
    split
    · exact List.Perm.refl _
    · exact (ih.cons q).trans (List.Perm.swap _ _ _)

theorem fold_perm (ps acc : List Push) :
    (ps.foldl (fun acc p=>insertTs p acc) acc).Perm (acc++ps) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    have h := (ih (insertTs p acc)).trans ((insert_perm p acc).append_right ps)
    exact h.trans List.perm_middle.symm

theorem sort_perm (ps : List Push) : (sortTs ps).Perm ps := by
  simpa [sortTs] using fold_perm ps []

/-- Popping the maximal-key bucket partitions the pending multiset exactly;
the timestamp sort changes only order. -/
theorem pop_perm (ps : List Push) (K : Nat) :
    ((ps.filter (fun p=>p.key != K))++sortTs (ps.filter (fun p=>p.key==K))).Perm ps := by
  have hp := (List.Perm.refl (ps.filter (fun p=>p.key != K))).append (sort_perm (ps.filter (fun p=>p.key==K)))
  apply hp.trans
  have hf := List.filter_append_perm (fun p : Push=>p.key != K) ps
  simpa only [bne,Bool.not_not] using hf
end ZkFormal.NearV3.Candidates.ProcPushPerm
