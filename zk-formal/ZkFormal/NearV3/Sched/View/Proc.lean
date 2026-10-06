import ZkFormal.NearV3.Sched.View.Mem
import ZkFormal.NearV3.Sched.Tables.Proc

/-!
# ZkFormal.NearV3.Sched.View.Proc — row facts of the process table `sprV3` (entries)

From `PLocal`: on an entry row, `ok = cS·cR·cL`, `last = [rem = 0]`, `za = [alOut = 0]`,
`zn = za·(z + 1)`, the push multiplicity `pm = ok·(1 − last)`, and the comparator operands
(`(next ts or T, ts + 1)`).
-/

namespace ZkFormal.NearV3.Sched.Proc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

abbrev PLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop := Local constraints tr t pub

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem bool_of (hL : PLocal tr tp pub) {r : Nat} (hr : r < tr.height tp) {x : Nat}
    (hx : x ∈ boolCols) : cv tr tp r x ≤ 1 :=
  hL.bool hr (by
    unfold constraints cKind
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem hx)))))

/-- A constraint `kE·(a − b)` on an entry row gives `a = b` for cells. -/
theorem eq_on_entry (hL : PLocal tr tp pub) {r : Nat} (hr : r < tr.height tp) {a b : Nat}
    (he : Expr.mul (c kE) (sub (c a) (c b)) ∈ constraints) (hk : cv tr tp r kE = 1) :
    cv tr tp r a = cv tr tp r b := by
  have c1 := hL.zc hr he
  simp only [zev_mul, zev_sub, zev_c, cur_cv, hk] at c1
  have := c1 (by have := cv_lt (tr := tr) (t := tp) r a; have := cv_lt (tr := tr) (t := tp) r b; push_cast; omega)
    (by have := cv_lt (tr := tr) (t := tp) r a; have := cv_lt (tr := tr) (t := tp) r b; push_cast; omega)
  push_cast at this; omega

/-- **Entry row.** -/
theorem entry_row (hL : PLocal tr tp pub) {r : Nat} (hr : r < tr.height tp) (hk : cv tr tp r kE = 1) :
    cv tr tp r ok = cv tr tp r cS * cv tr tp r cR * cv tr tp r cL ∧
      (cv tr tp r lastf = 1 ↔ cv tr tp r rem = 0) ∧
      (cv tr tp r za = 1 ↔ cv tr tp r alOut = 0) ∧
      cv tr tp r pm = cv tr tp r ok * (1 - cv tr tp r lastf) ∧
      cv tr tp r cS ≤ 1 ∧ cv tr tp r cR ≤ 1 ∧ cv tr tp r cL ≤ 1 ∧ cv tr tp r ok ≤ 1 := by
  have b := fun x (hx : x ∈ boolCols) => bool_of hL hr hx
  have hS := b cS (by simp [boolCols]); have hR := b cR (by simp [boolCols])
  have hLc := b cL (by simp [boolCols]); have hO := b ok (by simp [boolCols])
  have hlf := b lastf (by simp [boolCols]); have hza := b za (by simp [boolCols])
  have hpm := b pm (by simp [boolCols])
  -- ok
  have c1 := hL.zc hr (e := .mul (c kE) (sub (c ok) (mul3 (c cS) (c cR) (c cL)))) (by simp [constraints, cEnt])
  simp only [mul3, zev_mul, zev_sub, zev_c, cur_cv, hk] at c1
  have eok : cv tr tp r ok = cv tr tp r cS * cv tr tp r cR * cv tr tp r cL := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hR with h2 | h2 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hLc with h3 | h3 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hO with h4 | h4 <;>
    simp only [h1, h2, h3, h4] at c1 ⊢ <;> push_cast at c1 <;>
    first | rfl | exact (c1 trivial trivial).elim | (have := c1 (by omega) (by omega); omega) | omega
  -- last
  have c2 := hL.zc hr (e := .mul (c kE) (sub (c lastf) (notE (.mul (c rem) (c irem))))) (by simp [constraints, cEnt])
  obtain ⟨q3, c3⟩ := Mem.zdvd hL hr (e := .mul (c rem) (c lastf)) (by simp [constraints, cEnt])
  simp only [notE, zev_mul, zev_sub, zev_c, zev_k, cur_cv, hk] at c2 c3
  have hrem := cv_lt (tr := tr) (t := tp) r rem
  have elast : cv tr tp r lastf = 1 ↔ cv tr tp r rem = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hlf with h | h <;> rw [h] at c2 c3 ⊢ <;> push_cast at c2 c3
    · -- lastf = 0: rem·irem ≡ 1, so rem ≠ 0
      constructor
      · intro h'; omega
      · intro h'; rw [h'] at c2; simp at c2
    · constructor
      · intro _; omega
      · intro _; rfl
  -- za
  have c4 := hL.zc hr (e := .mul (c kE) (sub (c za) (notE (.mul (c alOut) (c ia))))) (by simp [constraints, cEnt])
  obtain ⟨q5, c5⟩ := Mem.zdvd hL hr (e := mul3 (c kE) (c alOut) (c za)) (by simp [constraints, cEnt])
  simp only [mul3, notE, zev_mul, zev_sub, zev_c, zev_k, cur_cv, hk] at c4 c5
  have hal := cv_lt (tr := tr) (t := tp) r alOut
  have eza : cv tr tp r za = 1 ↔ cv tr tp r alOut = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hza with h | h <;> rw [h] at c4 c5 ⊢ <;> push_cast at c4 c5
    · constructor
      · intro h'; omega
      · intro h'; rw [h'] at c4; simp at c4
    · constructor
      · intro _; omega
      · intro _; rfl
  -- pm
  have c6 := hL.zc hr (e := sub (c pm) (mul3 (c kE) (c ok) (notE (c lastf)))) (by simp [constraints, cEnt])
  simp only [mul3, notE, zev_mul, zev_sub, zev_c, zev_k, cur_cv, hk] at c6
  have epm : cv tr tp r pm = cv tr tp r ok * (1 - cv tr tp r lastf) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hO with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hlf with h2 | h2 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hpm with h3 | h3 <;>
    simp only [h1, h2, h3] at c6 ⊢ <;> push_cast at c6 <;>
    first | rfl | exact (c6 trivial trivial).elim | (have := c6 (by omega) (by omega); omega) | omega
  exact ⟨eok, elast, eza, epm, hS, hR, hLc, hO⟩

end

end ZkFormal.NearV3.Sched.Proc
