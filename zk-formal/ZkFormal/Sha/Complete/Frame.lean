import ZkFormal.Sha.Complete.Frame3

/-! # Completeness: `cFrame` -/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

theorem complete_cFrame : CompleteFamStmt cFrame := by
  intro msgs hok t pub r hr e he
  apply eval_honest_zero
  rw [henv_eq]
  have hs := step_at msgs hok t r hr
  generalize rowAt msgs r = cur at hs ⊢
  generalize rowAt msgs ((r + 1) % (honestTrace msgs).height t) = nx at hs ⊢
  generalize (if r = 0 then 1 else 0 : Int) = f
  generalize (if r + 1 = (honestTrace msgs).height t then 1 else 0 : Int) = lst
  generalize (fun i => ((pub.getD i 0).toNat : Int)) = p
  have hc := curRow_of_step cur nx hs
  simp only [cFrame, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with ((((((((he | he) | he) | he) | he) | he) | he) | he) | he)
  · simp only [List.mem_map, List.mem_range] at he
    obtain ⟨q, hq, rfl⟩ := he
    exact fr_mono f lst p cur nx hc q hq
  · rcases he with rfl | rfl | rfl
    · exact fr_F0prev f lst p cur nx hc
    · exact fr_msgC f lst p cur nx hc
    · exact fr_R0prev f lst p cur nx hc
  · simp only [List.mem_map, List.mem_range'_1] at he
    obtain ⟨j, hj, rfl⟩ := he
    exact fr_Fchain f lst p cur nx hs j (by omega) (by omega)
  · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fr_Nd f lst p cur nx hs
    · exact fr_Id f lst p cur nx hs
    · exact fr_Seen f lst p cur nx hs
    · exact fr_P80 f lst p cur nx hs
    · exact fr_Last f lst p cur nx hs
    · exact fr_SeenR0 f lst p cur nx hs
    · exact fr_Pn f lst p cur nx hc
    · exact fr_SeenP80 f lst p cur nx hc
  · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fr_blk1 f lst p cur nx hc
    · exact fr_blk2 f lst p cur nx hc
    · exact fr_blk3 f lst p cur nx hc
    · exact fr_blk4 f lst p cur nx hc
    · exact fr_blk5 f lst p cur nx hc
    · exact fr_blk6 f lst p cur nx hc
    · exact fr_blk7 f lst p cur nx hc
    · exact fr_blk8 f lst p cur nx hc
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at he
    obtain ⟨j, hj, q, hq, rfl⟩ := he
    exact fr_padbyte f lst p cur nx hc j q hj hq
  · simp only [List.mem_map, List.mem_range] at he
    obtain ⟨k, hk, rfl⟩ := he
    exact fr_len14 f lst p cur nx hc k hk
  · simp only [List.mem_map, List.mem_range'_1] at he
    obtain ⟨k, hk, rfl⟩ := he
    exact fr_len15 f lst p cur nx hc k (by omega) (by omega)
  · rcases he with rfl | rfl | rfl
    · exact fr_lenNd f lst p cur nx hc
    · exact fr_Dmult1 f lst p cur nx hc
    · exact fr_Dmult2 f lst p cur nx hc

end ZkFormal.Sha.Complete
