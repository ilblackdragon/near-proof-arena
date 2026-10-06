import ZkFormal.Chacha.Local
import ZkFormal.NearV3.Sched.Tables.Mem

/-!
# ZkFormal.NearV3.Sched.View.Mem — row facts of the memory table `smmV3`

From `MLocal` (every constraint on every row): flags are bits and one-hot, segments continue
with carried values, `INIT` / `READ` / `GRANT` rows have their value semantics. Value equations
are stated over naturals modulo `P` where the cells are arbitrary field elements; the link layer
adds the comparator's ranges.
-/

namespace ZkFormal.NearV3.Sched.Mem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

abbrev MLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop := Local constraints tr t pub

section
variable {tr : Trace Fp} {tm : Nat} {pub : List Fp}

/-- A vanishing constraint is a multiple of `P` over the integers. -/
theorem zdvd {cs : List Expr} (hL : Local cs tr tm pub) {r : Nat} (hr : r < tr.height tm) {e : Expr}
    (he : e ∈ cs) : ∃ q : Int, zev (tenv tr tm r pub) e = 2013265921 * q := by
  have h := hL r hr e he
  rw [eval_eq] at h
  have := (Lean.Grind.IsCharP.intCast_eq_zero_iff (α := Fp) P _).mp h
  rw [P_val] at this
  exact ⟨zev (tenv tr tm r pub) e / 2013265921, by omega⟩

theorem bool_of (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) {x : Nat}
    (hx : x ∈ boolCols) : cv tr tm r x ≤ 1 :=
  hL.bool hr (by
    unfold constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))))

/-- **Flags.** -/
theorem row_flags (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) :
    cv tr tm r act ≤ 1 ∧ cv tr tm r fst ≤ 1 ∧ cv tr tm r lst ≤ 1 ∧ cv tr tm r isRd ≤ 1 ∧
      cv tr tm r isGr ≤ 1 ∧ cv tr tm r al ≤ 1 ∧ cv tr tm r isL ≤ 1 ∧ cv tr tm r ok ≤ 1 ∧
      cv tr tm r cc ≤ 1 ∧ cv tr tm r sf ≤ 1 ∧
      cv tr tm r act = cv tr tm r fst + cv tr tm r isRd + cv tr tm r isGr ∧
      cv tr tm r lst ≤ cv tr tm r act := by
  have b := fun x (hx : x ∈ boolCols) => bool_of hL hr hx
  have hA := b act (by simp [boolCols]); have hF := b fst (by simp [boolCols])
  have hLs := b lst (by simp [boolCols]); have hR := b isRd (by simp [boolCols])
  have hG := b isGr (by simp [boolCols])
  refine ⟨hA, hF, hLs, hR, hG, b al (by simp [boolCols]), b isL (by simp [boolCols]),
    b ok (by simp [boolCols]), b cc (by simp [boolCols]), b sf (by simp [boolCols]), ?_, ?_⟩
  · have := hL.zc hr (e := sub (c act) (.add (c fst) (.add (c isRd) (c isGr)))) (by simp [constraints])
    simp only [zev_sub, zev_add, zev_c, cur_cv] at this
    have := this (by omega) (by omega); omega
  · have := hL.zc hr (e := .mul (c lst) (sub (k 1) (c act))) (by simp [constraints, notE])
    simp only [zev_sub, zev_mul, zev_c, zev_k, cur_cv] at this
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hLs with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hA with h' | h' <;> simp_all

theorem tenv_first_zero {r : Nat} (h : r ≠ 0) : (tenv tr tm r pub).first = 0 := by
  simp [tenv, h]

theorem tenv_last_zero {r : Nat} (h : r + 1 < tr.height tm) : (tenv tr tm r pub).last = 0 := by
  simp [tenv]; omega

theorem tenv_last_one {r : Nat} (h : r + 1 = tr.height tm) : (tenv tr tm r pub).last = 1 := by
  simp [tenv, h]

/-- **Segment continuation.** -/
theorem row_next (hL : MLocal tr tm pub) {r : Nat} (hr : r + 1 < tr.height tm)
    (ha : cv tr tm r act = 1) (hl : cv tr tm r lst = 0) :
    cv tr tm (r + 1) act = 1 ∧ cv tr tm (r + 1) fst = 0 ∧
      cv tr tm (r + 1) addr = cv tr tm r addr ∧ cv tr tm (r + 1) vin = cv tr tm r v ∧
      cv tr tm (r + 1) tp = cv tr tm r t ∧ cv tr tm (r + 1) wp = cv tr tm r w ∧
      cv tr tm (r + 1) al = cv tr tm r al ∧ cv tr tm (r + 1) isL = cv tr tm r isL := by
  have hr0 : r < tr.height tm := by omega
  have F1 := row_flags hL hr
  have c1 := hL.zc hr0 (e := .mul gE (notE (n act))) (by simp [constraints])
  have c2 := hL.zc hr0 (e := .mul gE (n fst)) (by simp [constraints])
  have cc' : ∀ a b, (a, b) ∈ carried → zev (tenv tr tm r pub) (.mul gE (sub (n b) (c a))) = 0 := by
    intro a b hab
    have := hL.zc hr0 (e := .mul gE (sub (n b) (c a))) (by
      unfold constraints
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨(a, b), hab, rfl⟩)))
    simp only [gE, zev_sub, zev_mul, zev_c, zev_n, cur_cv, nxt_cv hr, ha, hl] at this ⊢
    exact this (by have := cv_lt (tr := tr) (t := tm) (r + 1) b; have := cv_lt (tr := tr) (t := tm) r a; push_cast; omega)
      (by have := cv_lt (tr := tr) (t := tm) (r + 1) b; have := cv_lt (tr := tr) (t := tm) r a; push_cast; omega)
  simp only [gE, notE, zev_sub, zev_mul, zev_c, zev_n, zev_k, cur_cv, nxt_cv hr, ha, hl] at c1 c2
  have hA' := (row_flags hL hr).1
  have hF' := (row_flags hL hr).2.1
  have e1 := c1 (by push_cast; omega) (by push_cast; omega)
  have e2 := c2 (by push_cast; omega) (by push_cast; omega)
  have k : ∀ a b, (a, b) ∈ carried → cv tr tm (r + 1) b = cv tr tm r a := fun a b h => by
    have := cc' a b h
    simp only [gE, zev_sub, zev_mul, zev_c, zev_n, cur_cv, nxt_cv hr, ha, hl] at this
    push_cast at this
    omega
  refine ⟨by push_cast at e1; omega, by push_cast at e2; omega, k addr addr (by simp [carried]),
    k v vin (by simp [carried]), k t tp (by simp [carried]), k w wp (by simp [carried]),
    k al al (by simp [carried]), k isL isL (by simp [carried])⟩

/-- After a segment's last row comes a new segment (or padding). -/
theorem row_after_lst (hL : MLocal tr tm pub) {r : Nat} (hr : r + 1 < tr.height tm)
    (hl : cv tr tm r lst = 1) (ha : cv tr tm (r + 1) act = 1) : cv tr tm (r + 1) fst = 1 := by
  have hr0 : r < tr.height tm := by omega
  have hF := (row_flags hL hr).2.1
  have c1 := hL.zc hr0 (e := mul3 (c lst) (n act) (notE (n fst))) (by simp [constraints])
  simp only [mul3, notE, zev_sub, zev_mul, zev_c, zev_n, zev_k, cur_cv, nxt_cv hr, hl, ha] at c1
  have := c1 (by push_cast; omega) (by push_cast; omega)
  push_cast at this; omega

/-- Padding is a suffix. -/
theorem row_pad (hL : MLocal tr tm pub) {r : Nat} (hr : r + 1 < tr.height tm)
    (ha : cv tr tm r act = 0) : cv tr tm (r + 1) act = 0 := by
  have hr0 : r < tr.height tm := by omega
  have hA := (row_flags hL hr).1
  have c1 := hL.zc hr0 (e := mul3 .isTransition (notE (c act)) (n act)) (by simp [constraints])
  simp only [mul3, notE, zev_sub, zev_mul, zev_c, zev_n, zev_k, cur_cv, nxt_cv hr, ha] at c1
  simp only [zev, tenv_last_zero hr] at c1
  have := c1 (by push_cast; omega) (by push_cast; omega)
  push_cast at this; omega

theorem row_last (hL : MLocal tr tm pub) (h1 : 1 ≤ tr.height tm) :
    cv tr tm (tr.height tm - 1) act = 0 := by
  have hr : tr.height tm - 1 < tr.height tm := by omega
  have hA := (row_flags hL hr).1
  have c1 := hL.zc hr (e := .mul .isLast (c act)) (by simp [constraints])
  simp only [zev_mul, zev_c, cur_cv, zev, tenv_last_one (show tr.height tm - 1 + 1 = tr.height tm by omega)] at c1
  have := c1 (by push_cast; omega) (by push_cast; omega)
  push_cast at this; omega

theorem row_first (hL : MLocal tr tm pub) (h1 : 0 < tr.height tm) (ha : cv tr tm 0 act = 1) :
    cv tr tm 0 fst = 1 := by
  have hF := (row_flags hL h1).2.1
  have c1 := hL.zc h1 (e := .mul .isFirst (sub (c act) (c fst))) (by simp [constraints])
  simp only [zev_mul, zev_sub, zev_c, cur_cv, ha] at c1
  simp only [zev, tenv, if_pos] at c1
  have := c1 (by push_cast; omega) (by push_cast; omega)
  push_cast at this; omega

/-- A constraint `x·(a − b)` with `x = 1` gives `a = b` for cells. -/
theorem eq_of_gate (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) {x a b : Nat}
    (he : Expr.mul (c x) (sub (c a) (c b)) ∈ constraints) (hx : cv tr tm r x = 1) :
    cv tr tm r a = cv tr tm r b := by
  have c1 := hL.zc hr he
  simp only [zev_mul, zev_sub, zev_c, cur_cv, hx] at c1
  have := c1 (by have := cv_lt (tr := tr) (t := tm) r a; have := cv_lt (tr := tr) (t := tm) r b; push_cast; omega)
    (by have := cv_lt (tr := tr) (t := tm) r a; have := cv_lt (tr := tr) (t := tm) r b; push_cast; omega)
  push_cast at this; omega

/-- A constraint `x·a` with `x = 1` gives `a = 0`. -/
theorem zero_of_gate (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) {x a : Nat}
    (he : Expr.mul (c x) (c a) ∈ constraints) (hx : cv tr tm r x = 1) : cv tr tm r a = 0 := by
  have c1 := hL.zc hr he
  simp only [zev_mul, zev_c, cur_cv, hx] at c1
  have := c1 (by have := cv_lt (tr := tr) (t := tm) r a; push_cast; omega)
    (by have := cv_lt (tr := tr) (t := tm) r a; push_cast; omega)
  push_cast at this; omega

/-- **INIT row.** -/
theorem row_init (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (hf : cv tr tm r fst = 1) :
    cv tr tm r t = 0 ∧ cv tr tm r vin = cv tr tm r al ∧ cv tr tm r inc = cv tr tm r w ∧
      cv tr tm r ok = 0 ∧ cv tr tm r cc = 0 ∧ cv tr tm r sf = 0 ∧ cv tr tm r wp = cv tr tm r w :=
  ⟨zero_of_gate hL hr (by simp [constraints]) hf, eq_of_gate hL hr (by simp [constraints]) hf,
   eq_of_gate hL hr (by simp [constraints]) hf, zero_of_gate hL hr (by simp [constraints]) hf,
   zero_of_gate hL hr (by simp [constraints]) hf, zero_of_gate hL hr (by simp [constraints]) hf,
   eq_of_gate hL hr (by simp [constraints]) hf⟩

/-- **READ row.** -/
theorem row_read (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (hd : cv tr tm r isRd = 1) :
    cv tr tm r v = cv tr tm r vin ∧ cv tr tm r w = cv tr tm r wp ∧ cv tr tm r inc = 0 ∧
      cv tr tm r ok = 0 ∧ cv tr tm r cc = 0 ∧ cv tr tm r sf = 0 :=
  ⟨eq_of_gate hL hr (by simp [constraints]) hd, eq_of_gate hL hr (by simp [constraints]) hd,
   zero_of_gate hL hr (by simp [constraints]) hd, zero_of_gate hL hr (by simp [constraints]) hd,
   zero_of_gate hL hr (by simp [constraints]) hd, zero_of_gate hL hr (by simp [constraints]) hd⟩

/-- **GRANT row.** The condition is `al` (link) or `sf` (budget), `ok ⇒ cond`; the value drops
by `inc` (`ok ∧ sf`), to 0 (`ok ∧ ¬sf`), or stays; links add `ok·inc` to the granted value
(modulo `P`; the link layer bounds the cells). -/
theorem row_grant (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (hg : cv tr tm r isGr = 1) :
    cv tr tm r cc = (if cv tr tm r isL = 1 then cv tr tm r al else cv tr tm r sf) ∧
      cv tr tm r ok ≤ cv tr tm r cc ∧
      (cv tr tm r ok = 0 → cv tr tm r v = cv tr tm r vin) ∧
      (cv tr tm r ok = 1 → cv tr tm r sf = 1 → (cv tr tm r v + cv tr tm r inc) % 2013265921 = cv tr tm r vin) ∧
      (cv tr tm r ok = 1 → cv tr tm r sf = 0 → cv tr tm r v = 0) ∧
      (cv tr tm r isL = 1 → cv tr tm r ok = 1 → (cv tr tm r wp + cv tr tm r inc) % 2013265921 = cv tr tm r w) ∧
      (cv tr tm r isL = 0 ∨ cv tr tm r ok = 0 → cv tr tm r w = cv tr tm r wp) := by
  obtain ⟨-, -, -, -, -, hAl, hIL, hOk, hC, hSf, -, -⟩ := row_flags hL hr
  have lt := fun x => cv_lt (tr := tr) (t := tm) r x
  have hv := lt v; have hvin := lt vin; have hinc := lt inc; have hw := lt w; have hwp := lt wp
  -- condition
  have c1 := hL.zc hr (e := .mul (c isGr) (sub (c cc) (.add (.mul (c isL) (c al)) (.mul (notE (c isL)) (c sf)))))
    (by simp [constraints])
  simp only [notE, zev_mul, zev_sub, zev_add, zev_c, zev_k, cur_cv, hg] at c1
  -- ok ⇒ cond
  have c2 := hL.zc hr (e := mul3 (c isGr) (c ok) (notE (c cc))) (by simp [constraints])
  simp only [mul3, notE, zev_mul, zev_sub, zev_c, zev_k, cur_cv, hg] at c2
  -- value
  obtain ⟨q3, c3⟩ := zdvd hL hr (e := .mul (c isGr) (sub (c v) (sub (c vin)
      (.mul (c ok) (.add (.mul (c sf) (c inc)) (.mul (notE (c sf)) (c vin))))))) (by simp [constraints])
  simp only [notE, zev_mul, zev_sub, zev_add, zev_c, zev_k, cur_cv, hg] at c3
  -- granted
  obtain ⟨q4, c4⟩ := zdvd hL hr (e := .mul (c isGr) (sub (c w) (.add (c wp) (mul3 (c isL) (c ok) (c inc)))))
    (by simp [constraints])
  simp only [mul3, zev_mul, zev_sub, zev_add, zev_c, cur_cv, hg] at c4
  have e1 : (cv tr tm r cc : Int) = cv tr tm r isL * cv tr tm r al + (1 - cv tr tm r isL) * cv tr tm r sf := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hIL with hI | hI <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hSf with hS | hS <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hAl with hA | hA <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hC with hCc | hCc <;>
    simp only [hI, hS, hA, hCc] at c1 ⊢ <;> push_cast at c1 ⊢ <;>
    first
    | exact (c1 trivial trivial).elim
    | (have h := c1 (by omega) (by omega); omega)
    | omega
  have e2 : cv tr tm r ok ≤ cv tr tm r cc := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hOk with hO | hO <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hC with hCc | hCc <;>
    simp only [hO, hCc] at c2 ⊢ <;> push_cast at c2 <;>
    first
    | exact (c2 trivial trivial).elim
    | (have h := c2 (by omega) (by omega); omega)
    | omega
  refine ⟨?_, e2, fun hO => ?_, fun hO hS => ?_, fun hO hS => ?_, fun hI hO => ?_, fun h => ?_⟩
  · split
    · next hI => rw [hI] at e1; push_cast at e1; omega
    · next hI =>
      have hI0 : cv tr tm r isL = 0 := by omega
      rw [hI0] at e1; push_cast at e1; omega
  · simp only [hO] at c3; push_cast at c3; omega
  · simp only [hO, hS] at c3; push_cast at c3; omega
  · simp only [hO, hS] at c3; push_cast at c3; omega
  · simp only [hI, hO] at c4; push_cast at c4; omega
  · rcases h with h | h <;> simp only [h] at c4 <;> push_cast at c4 <;>
      first | omega | (simp at c4; omega)

end

end ZkFormal.NearV3.Sched.Mem
