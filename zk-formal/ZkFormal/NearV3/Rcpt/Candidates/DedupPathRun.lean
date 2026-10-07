import ZkFormal.NearV3.Rcpt.Candidates.DedupPathUnit

/-! Finite path runs after a leaf or path segment; this is the block parser's recursion. -/

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

structure PathRun (tr : Trace Fp) (tt r m : Nat) : Prop where
  bound : r + 64 * m < tr.height tt
  sl_end : tr.cell tt (r + 64 * m) sl = 1
  stop : tr.cell tt ((r + 64 * m + 1) % tr.height tt) sg = 0
  q_end : (tr.cell tt (r + 64 * m) q).toNat = (tr.cell tt r q).toNat + m
  lf_end : tr.cell tt (r + 64 * m) lf = if m = 0 then tr.cell tt r lf else 0
  list : ∀ x ∈ listConst, tr.cell tt (r + 64 * m) x = tr.cell tt r x
  units : ∀ i, i < m →
    IsU tr tt (r + 1 + 64 * i) 64 ∧
    tr.cell tt (r + 1 + 64 * i) rt = 0 ∧ tr.cell tt (r + 1 + 64 * i) lf = 0 ∧
    (tr.cell tt (r + 1 + 64 * i) q).toNat = (tr.cell tt r q).toNat + 1 + i ∧
    (tr.cell tt (r + 1 + 64 * i) pl).toNat =
      (if i = 0 then (if tr.cell tt r lf = 1 then 32 else 64) else 64) ∧
    ∀ x ∈ listConst, tr.cell tt (r + 1 + 64 * i) x = tr.cell tt r x

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- Local table legality yields a finite sequence of complete path units up to a list boundary. -/
theorem path_run {r : Nat} (hr : r < tr.height tt) (hl : tr.cell tt r sl = 1) :
    ∃ m, PathRun tr tt r m := by
  have gen : ∀ fuel r, tr.height tt - r ≤ fuel → r < tr.height tt → tr.cell tt r sl = 1 →
      ∃ m, PathRun tr tt r m := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro r hf hr hl
      have hnH : (r + 1) % tr.height tt < tr.height tt := Nat.mod_lt _ (by omega)
      rcases isBool hL hnH (x := sg) (by simp [SrcpProof.bools]) with hs | hs
      · refine ⟨0, ?_⟩
        exact ⟨by simpa using hr, by simpa using hl, by simpa using hs,
          by simp, by simp, by simp, by intro i hi; omega⟩
      · obtain ⟨huH, hu, hut, huf, huq, -, hul⟩ := next_path_unit hL hr hl hs
        have rows := (segRows hL hu huH hut).2.2.2.2.2.2 63 (by omega)
        have hend : r + 1 + 63 = r + 64 := by omega
        have heH : r + 64 < tr.height tt := by omega
        have heSl : tr.cell tt (r + 64) sl = 1 := by
          simpa using (segRows hL hu huH hut).2.2.2.2.1
        have heLf : tr.cell tt (r + 64) lf = 0 := by
          rw [← hend, rows.2.2.2.2 lf (by simp [segConst]), huf]
        have heQ : (tr.cell tt (r + 64) q).toNat = (tr.cell tt r q).toNat + 1 := by
          rw [← hend, rows.2.2.2.2 q (by simp [segConst]), huq]
        have heList : ∀ x ∈ listConst, tr.cell tt (r + 64) x = tr.cell tt r x := by
          intro x hx
          rw [← hend, rows.2.2.2.1 x hx, hul x hx]
        obtain ⟨m, hm⟩ := ih (tr.height tt - (r + 64)) (by omega) (r + 64) (by omega) heH heSl
        have he : r + 64 * (m + 1) = r + 64 + 64 * m := by omega
        refine ⟨m + 1, ?_⟩
        constructor
        · rw [he]; exact hm.bound
        · rw [he]; exact hm.sl_end
        · rw [he]; exact hm.stop
        · rw [he, hm.q_end, heQ]; omega
        · rw [he, hm.lf_end]
          simp [heLf]
        · intro x hx; rw [he, hm.list x hx, heList x hx]
        · intro i hi
          cases i with
          | zero =>
            simp only [Nat.mul_zero, Nat.add_zero]
            exact ⟨hu, hut, huf, huq, by simpa using next_path_length hL hr hl hs, hul⟩
          | succ i =>
            have hei : r + 1 + 64 * (i + 1) = r + 64 + 1 + 64 * i := by omega
            rw [hei]
            obtain ⟨hui, hti, hfi, hqi, hpi, hli⟩ := hm.units i (by omega)
            refine ⟨hui, hti, hfi, ?_, ?_, ?_⟩
            · rw [hqi, heQ]; omega
            · rw [hpi]; simp [heLf]
            · intro x hx; rw [hli x hx, heList x hx]
  exact gen (tr.height tt - r) r (by omega) hr hl

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
