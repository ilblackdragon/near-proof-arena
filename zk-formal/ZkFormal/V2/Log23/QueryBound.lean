import ZkFormal.V2.Log23.Verifier
import ZkFormal.Stark.SchedOk
import ZkFormal.Stark.QueryBound

/-! Candidate schedule and actual compiled-verifier oracle-query bounds. These
proofs use the candidate header, without assuming deployed log22 admissibility. -/
namespace ZkFormal.V2.Log23

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Air ZkFormal.Stark

theorem schedule_bound (A : Air) (prm : Params) (hdr : List Nat)
    (hq : queryLog A prm hdr ≤ prm.maxLogLde) :
    (schedule A prm hdr).length ≤ schedBound A prm := by
  unfold schedule schedBound
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h1 := length_flatMap_le (List.range (batchRounds (layout A prm hdr) - 1))
    (fun _ => [Slot.msg [], Slot.chal false]) 2 (by intro _ _; simp)
  rw [List.length_range] at h1
  have h2 := friSchedule_length_le A prm hdr
  have h3 := batchRounds_le A prm hdr
  have h4 := finalLayer_le_queryLog A prm hdr
  omega

theorem oracles_bound (A : Air) (prm : Params) (hdr : List Nat)
    (hq : queryLog A prm hdr ≤ prm.maxLogLde) :
    (schedOracles (schedule A prm hdr)).length ≤ oracleBound prm := by
  rw [schedOracles_schedule, schedOracles_fri]
  have := length_flatMap_le (List.range (finalLayer A prm hdr)) (friOracleAt A prm hdr) 1 (by
    intro i _; unfold friOracleAt; cases (friCommits A prm hdr).lookup i <;> simp)
  rw [List.length_range] at this
  have := finalLayer_le_queryLog A prm hdr
  simp only [List.length_append, List.length_cons, List.length_nil, oracleBound]
  omega

section
variable {F K : Type} [Field F] [Field K] [StarkField F K]
  [DecidableEq F] [DecidableEq K] [PubVal F]

theorem schedule_ok (AP : AirP) (g : Nat) : Bcs.Adapter.SchedOk (iop F K AP g) where
  first := fun _ _ => ⟨_, _, rfl⟩
  roots := fun hdr _ parts h => Nat.lt_of_le_of_lt
    (schedule_msg_roots AP.toAir (params g) hdr parts h) (by decide)
  depth := fun hdr _ o ho => oracles_depth_le_queryLog AP.toAir (params g) hdr o ho

theorem iop_bounds (AP : AirP) (g : Nat) :
    IopBounds (iop F K AP g) (schedBound AP.toAir (params g)) (oracleBound (params g)) 27 where
  sched := fun hdr h => schedule_bound AP.toAir (params g) hdr (verifierHeader_bounds h).2.2.2.2.2
  oracles := fun hdr h => oracles_bound AP.toAir (params g) hdr (verifierHeader_bounds h).2.2.2.2.2
  depth := fun hdr h o ho => Nat.le_trans
    (oracles_depth_le_queryLog AP.toAir (params g) hdr o ho) (verifierHeader_bounds h).2.2.2.2.2

theorem verifier_query_bound (AP : AirP) (g : Nat) (pub cb pb : Bytes) :
    OracleComp.QueryBound unitWeight ((verifier F K AP g).tree pub cb pb)
      (NVu AP.toAir (params g)) := by
  exact compile_queryBound F K (iop F K AP g) _ _ _ (iop_bounds AP g) pub cb pb

end

end ZkFormal.V2.Log23
