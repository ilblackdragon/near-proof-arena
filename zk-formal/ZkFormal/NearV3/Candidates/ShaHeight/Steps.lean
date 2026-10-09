import ZkFormal.Sha.Complete.Rows
namespace ZkFormal.NearV3.Candidates.ShaHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Complete ZkFormal.Sha.Gen

/-- The honest row stream is valid at any fitting height, including its changed
cyclic final edge. This proves the boundary rather than assuming padding. -/
theorem step_at_height (msgs : List Msg) (hok : MsgsOk msgs) (H r : Nat)
    (hlen : (honestRows msgs).length≤H) (hr : r<H) :
    Step (rowAt msgs r) (rowAt msgs ((r+1)%H)) := by
  have hm := mok_of msgs hok
  have hhead := honestRows_head msgs
  by_cases h1 : r + 1 < (honestRows msgs).length
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact honestRows_chain msgs hm r h1
  · have hX : rowAt msgs ((r + 1) % H) = .pad ∨ ∃ id, rowAt msgs ((r + 1) % H) = .start id := by
      by_cases h2 : r + 1 < H
      · left; rw [Nat.mod_eq_of_lt h2]; unfold rowAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      · rw [show r + 1 = H by omega, Nat.mod_self]; exact hhead
    by_cases h3 : r < (honestRows msgs).length
    · have hne : honestRows msgs ≠ [] := by intro h; rw [h] at h3; simp at h3
      have e : rowAt msgs r = (honestRows msgs).getLast hne := by
        unfold rowAt
        rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3,
          Option.getD_some]
        congr 1; omega
      rw [e]; exact honestRows_last msgs hm hne _ hX
    · have e : rowAt msgs r = .pad := by
        unfold rowAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [e]; exact Step.pad _ hX

end ZkFormal.NearV3.Candidates.ShaHeight
