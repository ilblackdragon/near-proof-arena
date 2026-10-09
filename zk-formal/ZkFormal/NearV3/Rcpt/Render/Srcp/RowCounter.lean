import ZkFormal.NearV3.Rcpt.Render.Srcp.CrossCounter

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

theorem row_counter {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat) (hH : R bs ≤ H)
    (P : Nat → Int) (fst lst : Int) (n : Nat) (hi : n ∈ counterIndices) :
    ev (fun x => (cell bs r x : Int)) (fun x => (cell bs ((r + 1) % H) x : Int))
      fst lst (if r + 1 = H then 0 else 1) P (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  by_cases hr : r < R bs
  · have hI := (mem_recs (descriptor_mem hr)).1
    have hB := counter_facts h _ hI
    by_cases hn : r + 1 < R bs
    · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hm]
      rcases adjAt hn with ⟨hk, he⟩ | ⟨hk, hd⟩
      · simp only [cell, hr, hn, ite_true, rowFrame]
        rw [he]
        exact counter_step_polynomials _ hB _ _ _ _ _ (mem_recs (descriptor_mem hr)).2 hk
          P fst lst _ n hi
      · have hlast := none_last _ _ (mem_recs (descriptor_mem hr)).2 hk
        have hI' := (mem_recs (descriptor_mem hn)).1
        rw [hd] at hI'
        simp only at hI'
        simp only [cell, hr, hn, ite_true, rowFrame]
        rw [hlast, hd]
        apply counter_end_polynomials _ hB _ _ _ P fst lst _ ?_ ?_ ?_ n hi
        · rfl
        · change _ * 1 * (((rootFrame _ 0).q : Int) - _) = 0
          rw [cross_q h _ _ hI']
          simp
        · change _ * 1 * (((bs.getD _ default).j : Int) - (((bs.getD _ default).j : Int) + 1)) = 0
          rw [cross_j h _ hI']
          simp
    · have he : r = R bs - 1 := by omega
      have hlast : ((recs bs).getD r default).2 =
          lastKind (bs.getD ((recs bs).getD r default).1 default) := by
        rw [he, lastAt h]
      have hc : (fun x => (cell bs r x : Int)) =
          (fun x => (({ frame (bs.getD ((recs bs).getD r default).1 default)
            (before bs ((recs bs).getD r default).1)
            (lastKind (bs.getD ((recs bs).getD r default).1 default))
              with gz := decide (r + 1 = R bs) }).cell x : Int)) := by
        funext x
        simp only [cell, hr, ite_true, rowFrame]
        rw [hlast]
      rw [hc]
      apply counter_end_polynomials _ hB _ _ _ P fst lst _ ?_ ?_ ?_ n hi
      · simp [last_next_sg h H r hH hr hn]
      · by_cases hh : r + 1 = H
        · simp [hh]
        · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
          have hp : R bs ≤ r + 1 := by omega
          simp [hh, hm, padding_cell hp, SrcpV3.rt, SrcpV3.sz]
      · by_cases hh : r + 1 = H
        · simp [hh]
        · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
          have hp : R bs ≤ r + 1 := by omega
          simp [hh, hm, padding_cell hp, SrcpV3.rt, SrcpV3.sz]
  · have hp : R bs ≤ r := by omega
    apply counter_padding _ _ P fst lst _ ?_ ?_ n hi
    all_goals simp [padding_cell hp, SrcpV3.rt, SrcpV3.sl, SrcpV3.sz]

theorem counter_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x))
    (n : Nat) (hi : n ∈ counterIndices) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => (cell bs ((r + 1) % tr.height tt) x : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [hd x, ofNat_int]
  · exact row_counter h _ r hH _ _ _ n hi

end ZkFormal.NearV3.Render.SrcpGen
