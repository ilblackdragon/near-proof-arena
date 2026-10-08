import ZkFormal.NearV3.Rcpt.Candidates.MerkleShaJobs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec ZkFormal.Near Rcpt.Candidates Render Render.MrkGen

private theorem hash_bytes (xs : List Nat) : ∀b∈Render.shaN xs,b<256 := by
  intro b hb
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact UInt8.toNat_lt v

private theorem get_digest_bytes (xs : List MNode)
    (h : ∀m∈xs,∀b∈m.dig,b<256) (i : Nat) :
    ∀b∈(xs.getD i default).dig,b<256 := by
  by_cases hi : i<xs.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length≤i),Option.getD_none]
    intro b hb
    change b∈([] : List Nat) at hb
    contradiction

/-- Internal outcome-Merkle SHA inputs are always actual hash bytes, even when
input leaves have not yet been authenticated. -/
theorem merkle_level_digest_bytes (leaves : List (List Nat)) :
    ∀j,∀m∈levelsFromLeaves leaves j,∀b∈m.dig,b<256
  | 0,m,hm => by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact hash_bytes _
  | j+1,m,hm => by
    simp only [levelsFromLeaves,List.mem_map,List.mem_range] at hm
    obtain ⟨i,hi,rfl⟩ := hm
    split
    · exact hash_bytes _
    · exact get_digest_bytes _ (merkle_level_digest_bytes leaves j) _

theorem merkle_sha_job_bytes (leaves : List (List Nat)) :
    ∀m∈merkleShaJobs leaves,∀b∈m.bytes,b<256 := by
  intro m hm b hb
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
  simp only [List.mem_append] at hb
  rcases hb with hb|hb <;>
    exact get_digest_bytes _ (merkle_level_digest_bytes leaves _) _ b hb

end ZkFormal.NearV3.Assembly.RcptSkeleton
