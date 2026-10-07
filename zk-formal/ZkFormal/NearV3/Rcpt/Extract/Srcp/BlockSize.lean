import ZkFormal.NearV3.Rcpt.Extract.Srcp.BlockTraffic

/-! The natural size charges of an extracted block are exactly L plus 33 per path item. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

def chargeSpan (tr : Trace Fp) (tt s n : Nat) : Nat :=
  ((List.range n).map fun o => rowSize tr tt (s + o)).sum

theorem chargeSpan_add (tr : Trace Fp) (tt s n k : Nat) :
    chargeSpan tr tt s (n + k) = chargeSpan tr tt s n + chargeSpan tr tt (s + n) k := by
  simp [chargeSpan, List.range_add, List.map_append, List.sum_append, List.map_map, Function.comp_def, Nat.add_assoc]

variable {tr : Trace Fp} {pub : List Fp} {tt s m : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem leaf_size (hu : IsU tr tt s 32) (hH : s + 32 ≤ tr.height tt)
    (ht : tr.cell tt s rt = 0) (hf : tr.cell tt s lf = 1) : chargeSpan tr tt s 32 = 0 := by
  have he : ∀ o, o < 32 → rowSize tr tt (s + o) = 0 := by
    intro o ho
    have hrows := (segRows hL hu hH ht).2.2.2.2.2.2 o ho
    have hlf : tr.cell tt (s + o) lf = 1 := by
      rw [hrows.2.2.2.2 lf (by simp [segConst]), hf]
    simp [rowSize, hrows.2.1, hlf]
  unfold chargeSpan
  rw [List.map_congr_left (fun o ho => he o (List.mem_range.mp ho))]
  decide +kernel

theorem path_size (hu : IsU tr tt s 64) (hH : s + 64 ≤ tr.height tt)
    (ht : tr.cell tt s rt = 0) (hf : tr.cell tt s lf = 0) : chargeSpan tr tt s 64 = 33 := by
  have he : ∀ o, o < 64 → rowSize tr tt (s + o) = if o = 0 then 33 else 0 := by
    intro o ho
    have hrows := (segRows hL hu hH ht).2.2.2.2.2.2 o ho
    have hlf : tr.cell tt (s + o) lf = 0 := by
      rw [hrows.2.2.2.2 lf (by simp [segConst]), hf]
    have hsf : tr.cell tt (s + o) sf = if o = 0 then 1 else 0 := by
      by_cases hz : o = 0
      · subst o; simpa using (segRows hL hu hH ht).1
      · have hn := hu.2.2.2.2.1 (s + o) (by omega) (by omega)
        simp only [uFirst, Bool.or_eq_false_iff] at hn
        rw [if_neg hz]
        exact zero_of_not_one hL (by omega) (by simp [bools]) hn.2
    rw [rowSize, hrows.1, hrows.2.1, hlf, hsf]
    by_cases hz : o = 0 <;> simp [hz]
  unfold chargeSpan
  rw [List.map_congr_left (fun o ho => he o (List.mem_range.mp ho)),
    show 64 = 63 + 1 from rfl, List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]
  decide +kernel

/-- Every parsed path unit contributes 33 to the natural size sum. -/
theorem path_run_size {r : Nat} (hm : PathRun tr tt r m) :
    chargeSpan tr tt (r + 1) (64 * m) = 33 * m := by
  have gen : ∀ k, k ≤ m → chargeSpan tr tt (r + 1) (64 * k) = 33 * k := by
    intro k
    induction k with
    | zero => intro _; simp [chargeSpan]
    | succ k ih =>
      intro hk
      obtain ⟨hu, ht, hf, -⟩ := hm.units k (by omega)
      rw [Nat.mul_succ, chargeSpan_add, ih (by omega),
        path_size hL hu (by have := hm.bound; omega) ht hf]
      omega
  exact gen m (by omega)

/-- Block charges agree with the semantic SIZE definition, over natural numbers. -/
theorem block_size (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
    (hm : PathRun tr tt (s + 32) m) :
    chargeSpan tr tt s (33 + 64 * m) =
      (blockOf tr tt s m).L + 33 * (blockOf tr tt s m).path.length := by
  obtain ⟨hH, hu, hlf, -, -⟩ := root_leaf_unit hL hs ht
  have hs0 : tr.cell tt s sg = 0 := by
    have he := (local_ hL hs).1
    rw [ht] at he; grind
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := (local_ hL (r := s + 1) (by omega)).1
    rw [(afterRoot hL (by omega) ht).1] at he; grind
  rw [show 33 + 64 * m = 1 + (32 + 64 * m) by omega, chargeSpan_add, chargeSpan_add,
    leaf_size hL hu hH hrt hlf, show s + 1 + 32 = s + 32 + 1 by omega,
    path_run_size hL hm]
  simp [chargeSpan, rowSize, ht, hs0, blockOf, pathItems]

end ZkFormal.NearV3.SrcpProof
