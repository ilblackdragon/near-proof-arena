import ZkFormal.NearV3.Rcpt.Extract.Srcp.ListCounter

/-! Complete leaf-unit traffic and its adjacency to the source root row. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- Exact traffic of a leaf unit on every bus except the final SIZE output. -/
theorem leaf_traffic {s : Nat} (hu : IsU tr tt s 32)
    (hH : s + 32 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range 32).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd) =
      (srcpLeafMsgs (tr.cell tt s j).toNat (tr.cell tt s L).toNat
        (tr.cell tt s q).toNat (regsN tr tt s) bb sd).map Msg.toFp := by
  cases sd
  · by_cases he : bb = B_DIGEST
    · subst bb
      rw [leaf_digest_traffic hL hu hH hrt hlf]
      simp [srcpLeafMsgs, B_BYTES, B_DIGEST]
    · have hz : (List.range 32).flatMap (fun o =>
          rowTraffic SrcpV3.interactions tr tt (s + o) pub bb false) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [leafRowT hL hu hH hrt hlf (List.mem_range.mp ho) hb false]
        simp [he]
      rw [hz]
      simp [srcpLeafMsgs, he]
  · by_cases he : bb = B_BYTES
    · subst bb
      rw [leaf_bytes_traffic hL hu hH hrt hlf]
      simp [srcpLeafMsgs]
    · have hz : (List.range 32).flatMap (fun o =>
          rowTraffic SrcpV3.interactions tr tt (s + o) pub bb true) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [leafRowT hL hu hH hrt hlf (List.mem_range.mp ho) hb true]
        simp [he]
      rw [hz]
      simp [srcpLeafMsgs, he]

/-- Every root row is followed by a complete 32-row leaf unit. -/
theorem root_leaf_unit {r : Nat} (hr : r < tr.height tt) (ht : tr.cell tt r rt = 1) :
    r + 1 + 32 ≤ tr.height tt ∧ IsU tr tt (r + 1) 32 ∧
    tr.cell tt (r + 1) lf = 1 ∧
    (tr.cell tt (r + 1) q).toNat = (tr.cell tt r q).toNat + 1 ∧
    ∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hn := root_not_last hL hr ht
  have hf := afterRoot hL hn ht
  have huFirst : uFirst tr tt (r + 1) = true := by simp [uFirst, isOne, hf.2.2.1]
  obtain ⟨ℓ, hH, hu⟩ := seg_from (segFacts hL) (r + 1) hn huFirst
  have hnrt : tr.cell tt (r + 1) rt = 0 := by
    have hz := (local_ hL hn).1
    rw [hf.1] at hz; grind
  have h32 : ℓ = 32 := by
    rcases (segShape hL hu hH hnrt).1 with h | h
    · exact h.2
    · rw [hf.2.1] at h; exact False.elim (by simpa using h.1)
  subst ℓ
  exact ⟨hH, hu, hf.2.1, root_q_succ hL hn ht, hf.2.2.2.2⟩

end ZkFormal.NearV3.SrcpProof
