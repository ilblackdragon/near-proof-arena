import ZkFormal.Stark.NpBounds
import ZkFormal.Bcs.StarkAdapter

/-!
# ZkFormal.Stark.SchedOk — L2's shape conditions for `np-udr-stark-v1`

`Adapter.SchedOk (Iop.verifier F K A prm)`: on admissible headers the first
slot is the header message, every message commits at most one tree (< 256),
and every tree's depth is at most the query log.
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind ZkFormal.Air ZkFormal.Bcs

section
variable (A : Air) (prm : Params) (hdr : List Nat)

/-- Every tree of the schedule has depth at most the query log. -/
theorem oracles_depth_le_queryLog :
    ∀ o ∈ schedOracles (schedule A prm hdr), treeLog o ≤ queryLog A prm hdr := by
  have hl : ∀ L ∈ layout A prm hdr, L.lde ≤ queryLog A prm hdr := fun L hL =>
    le_foldr_max (List.mem_map.mpr ⟨L, hL, rfl⟩)
  intro o ho
  apply treeLog_le_of
  rw [schedOracles_schedule, schedOracles_fri] at ho
  simp only [List.cons_append, List.mem_cons, List.nil_append, List.mem_flatMap] at ho
  rcases ho with rfl | rfl | rfl | ⟨i, _, hi⟩
  · intro p hp; simp only [List.mem_map] at hp; obtain ⟨L, hL, rfl⟩ := hp; exact hl L hL
  · intro p hp; simp only [List.mem_map] at hp; obtain ⟨L, hL, rfl⟩ := hp; exact hl L hL
  · intro p hp; simp only [List.mem_map] at hp; obtain ⟨L, hL, rfl⟩ := hp; exact hl L hL
  · unfold friOracleAt at hi
    cases hc : (friCommits A prm hdr).lookup i with
    | none => rw [hc] at hi; cases hi
    | some a =>
      rw [hc] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simp only
      omega

/-- Every message slot of the FRI schedule commits at most one tree. -/
theorem fri_msg_roots (parts : List Part) (h : Slot.msg parts ∈ friSchedule A prm hdr) :
    (Adapter.oracleShapes parts).length ≤ 1 := by
  unfold friSchedule at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at h
  rcases h with (⟨i, _, hi⟩ | hr) | hf
  · try simp only [List.mem_append] at hi
    rcases hi with hi | hi
    · split at hi <;> simp_all [Adapter.oracleShapes]
    · split at hi <;> simp_all [Adapter.oracleShapes]
  · split at hr <;> simp_all [Adapter.oracleShapes]
  · simp_all [Adapter.oracleShapes]

theorem schedule_msg_roots (parts : List Part) (h : Slot.msg parts ∈ schedule A prm hdr) :
    (Adapter.oracleShapes parts).length ≤ 1 := by
  unfold schedule at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at h
  rcases h with (h0 | ⟨_, _, hb⟩) | hf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
    rcases h0 with h | h | h | h | h | h | h | h | h | h <;> simp_all [Adapter.oracleShapes]
  · simp_all [Adapter.oracleShapes]
  · exact fri_msg_roots A prm hdr parts hf

end

/-- **`SchedOk` for the np-udr-stark IOP** (L2's `Adapter.SchedOk`). -/
theorem schedOk {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    (A : Air) (prm : Params) : Adapter.SchedOk (Iop.verifier F K A prm) where
  first := fun hdr _ => ⟨_, _, rfl⟩
  roots := fun hdr _ parts h => Nat.lt_of_le_of_lt (schedule_msg_roots A prm hdr parts h) (by decide)
  depth := fun hdr _ o ho => oracles_depth_le_queryLog A prm hdr o ho

end ZkFormal.Stark
