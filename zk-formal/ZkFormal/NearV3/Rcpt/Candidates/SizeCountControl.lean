import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSound
import ZkFormal.NearV3.Rcpt.Extract.SizeProof
namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount.Control
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SizeV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
theorem mem2 {e : Expr} (h : e ∈ ([ .mul .isFirst (Dsl.not (c act)), .mul .isFirst (c t),
    .mul .isFirst (sub (c tot) (c x)), .mul .isFirst (sub (c base) (c x)),
    .mul .isFirst (Dsl.not (n lb)),
    .mul (c lb) (sub (c t) (k 1)), .mul (c la) (sub (c t) (k (NT - 1))),
    .mul (c lb) (Dsl.not (c act)), .mul (c la) (Dsl.not (c act)),
    .mul (mul3 .isTransition (c act) (Dsl.not (c la))) (Dsl.not (n act)),
    mul3 .isTransition (c la) (n act),
    mul3 .isTransition (Dsl.not (c act)) (n act),
    .mul .isLast (.mul (c act) (Dsl.not (c la))),
    mul3 .isTransition (c act) (sub (n t) (.add (c t) (k 1))),
    mul3 .isTransition (n act) (sub (n tot) (.add (c tot) (n x))),
    mul3 .isTransition (n act) (sub (n base) (.add (c base) (.mul (n lb) (n x)))),
    .mul (c lb) (sub bitsE (sub (k 3000000) (c base))) ] : List Expr)) :
    e ∈ sizeTable.constraints := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst e; simp [sizeTable,SizeV3.constraints,oldTotalBound]; exact Or.inl (by decide +kernel)

section
variable (hL : TableLocal sizeTable tr tt pub)
include hL

theorem con {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ sizeTable.constraints) :
    e.eval tr tt r pub = 0 := hL.constr r hr e he

theorem isB {r : Nat} (hr : r < tr.height tt) {y : Nat} (hy : y ∈ [act, lb, la] ++ (List.range 24).map bt) :
    tr.cell tt r y = 0 ∨ tr.cell tt r y = 1 := by
  have := con hL hr (e := Dsl.bool (c y)) (by
    apply List.mem_append_left
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_append_left _ (List.mem_map_of_mem (f := fun y => Dsl.bool (c y)) hy)
    · simp [List.range_succ,bt,act,lb,la] at hy
      rcases hy with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy
      all_goals subst y; decide +kernel)
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem rowF {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r lb = 1 → tr.cell tt r t = 1 ∧ tr.cell tt r act = 1) ∧
    (tr.cell tt r la = 1 → tr.cell tt r t = 2 ∧ tr.cell tt r act = 1) := by
  have h1 := con hL hr (e := .mul (c lb) (sub (c t) (k 1))) (mem2 (by simp))
  have h2 := con hL hr (e := .mul (c la) (sub (c t) (k (NT - 1)))) (mem2 (by simp))
  have h3 := con hL hr (e := .mul (c lb) (Dsl.not (c act))) (mem2 (by simp))
  have h4 := con hL hr (e := .mul (c la) (Dsl.not (c act))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_sub, eval_k, eval_not, NT] at h1 h2 h3 h4
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; exact ⟨by grind, by grind⟩
  · rw [h] at h2 h4; exact ⟨by grind, by grind⟩

theorem trF {r : Nat} (hr : r + 1 < tr.height tt) :
    (tr.cell tt r act = 1 → tr.cell tt r la = 0 → tr.cell tt (r + 1) act = 1) ∧
    (tr.cell tt r la = 1 → tr.cell tt (r + 1) act = 0) ∧
    (tr.cell tt r act = 1 → tr.cell tt (r + 1) t = tr.cell tt r t + 1) ∧
    (tr.cell tt (r + 1) act = 1 → tr.cell tt (r + 1) tot = tr.cell tt r tot + tr.cell tt (r + 1) x ∧
      tr.cell tt (r + 1) base = tr.cell tt r base + tr.cell tt (r + 1) lb * tr.cell tt (r + 1) x) := by
  have hr' : r < tr.height tt := by omega
  have nx : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt hr
  have nt : ¬ (r + 1 = tr.height tt) := by omega
  have h1 := con hL hr' (e := .mul (mul3 .isTransition (c act) (Dsl.not (c la))) (Dsl.not (n act))) (mem2 (by simp))
  have h2 := con hL hr' (e := mul3 .isTransition (c la) (n act)) (mem2 (by simp))
  have h3 := con hL hr' (e := mul3 .isTransition (c act) (sub (n t) (.add (c t) (k 1)))) (mem2 (by simp))
  have h4 := con hL hr' (e := mul3 .isTransition (n act) (sub (n tot) (.add (c tot) (n x)))) (mem2 (by simp))
  have h5 := con hL hr' (e := mul3 .isTransition (n act) (sub (n base) (.add (c base) (.mul (n lb) (n x)))))
    (mem2 (by simp))
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_sub, eval_add, eval_k, eval_not, eval_isTransition,
    nx, nt, if_false] at h1 h2 h3 h4 h5
  refine ⟨fun ha hl => ?_, fun hl => ?_, fun ha => ?_, fun ha => ?_⟩
  · rw [ha, hl] at h1; grind
  · rw [hl] at h2; grind
  · rw [ha] at h3; grind
  · rw [ha] at h4 h5; exact ⟨by grind, by grind⟩

theorem firstF (h2 : 1 < tr.height tt) :
    tr.cell tt 0 act = 1 ∧ tr.cell tt 0 t = 0 ∧ tr.cell tt 0 tot = tr.cell tt 0 x ∧
    tr.cell tt 0 base = tr.cell tt 0 x ∧ tr.cell tt 1 lb = 1 := by
  have h0 : 0 < tr.height tt := by omega
  have nx : (0 + 1) % tr.height tt = 1 := Nat.mod_eq_of_lt h2
  have a1 := con hL h0 (e := .mul .isFirst (Dsl.not (c act))) (mem2 (by simp))
  have a2 := con hL h0 (e := .mul .isFirst (c t)) (mem2 (by simp))
  have a3 := con hL h0 (e := .mul .isFirst (sub (c tot) (c x))) (mem2 (by simp))
  have a4 := con hL h0 (e := .mul .isFirst (sub (c base) (c x))) (mem2 (by simp))
  have a5 := con hL h0 (e := .mul .isFirst (Dsl.not (n lb))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_n, eval_sub, eval_not, eval_isFirst, if_pos rfl, nx] at a1 a2 a3 a4 a5
  exact ⟨by grind, by grind, by grind, by grind, by grind⟩

theorem lastF (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) la = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _) (e := .mul .isLast (.mul (c act) (Dsl.not (c la))))
    (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind


end

theorem layout (hL : TableLocal sizeTable tr tt pub) :
    tr.height tt=4 ∧ tr.cell tt 0 act=1 ∧ tr.cell tt 1 act=1 ∧
    tr.cell tt 2 act=1 ∧ tr.cell tt 3 act=0 ∧
    tr.cell tt 0 t=0 ∧ tr.cell tt 1 t=1 ∧ tr.cell tt 2 t=2 ∧ tr.cell tt 2 la=1 := by
  have hH : tr.height tt = 2 ∨ tr.height tt = 4 := by
    have h1 := hL.log_ge
    have h2 := hL.log_le
    simp only [sizeTable,SizeV3.table, SizeV3.maxLog] at h2
    unfold Trace.height
    have : tr.log tt = 1 ∨ tr.log tt = 2 := by omega
    rcases this with h | h <;> simp [h]
  have h2 : 1 < tr.height tt := by omega
  obtain ⟨a0, t0, tot0, base0, lb1⟩ := firstF hL h2
  have ne : ∀ a b : Nat, a < P → b < P → a ≠ b → ¬ ((a : Fp) = (b : Fp)) := fun a b ha hb h e =>
    h (ofNat_inj ha hb e)
  -- row 0 is not the last active row
  have la0 : tr.cell tt 0 SizeV3.la = 0 := by
    rcases isB hL (r := 0) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exact h
    · have := ((rowF hL (r := 0) (by omega)).2 h).1
      rw [t0] at this; exact absurd (show ((0 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 0 2 (by decide) (by decide) (by decide))
  obtain ⟨a1, -, t1', -⟩ := trF hL (r := 0) h2
  have act1 := a1 a0 la0
  have t1 : tr.cell tt 1 SizeV3.t = 1 := by rw [t1' a0, t0]; grind
  have la1 : tr.cell tt 1 SizeV3.la = 0 := by
    rcases isB hL (r := 1) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exact h
    · have := ((rowF hL (r := 1) (by omega)).2 h).1
      rw [t1] at this; exact absurd (show ((1 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 1 2 (by decide) (by decide) (by decide))
  have h4 : tr.height tt = 4 := by
    rcases hH with h | h
    · exfalso
      have := lastF hL (by omega) (by rw [h]; exact act1)
      rw [h] at this; simp only [show 2 - 1 = 1 from rfl] at this; rw [la1] at this; exact fp_zero_ne_one this
    · exact h
  obtain ⟨b1, -, t2', tb2⟩ := trF hL (r := 1) (by omega)
  have act2 := b1 act1 la1
  have t2 : tr.cell tt 2 SizeV3.t = 2 := by rw [t2' act1, t1]; grind
  obtain ⟨c1, c2, t3', -⟩ := trF hL (r := 2) (by omega)
  have la2 : tr.cell tt 2 SizeV3.la = 1 := by
    rcases isB hL (r := 2) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exfalso
      have act3 := c1 act2 h
      have t3 : tr.cell tt 3 SizeV3.t = 3 := by rw [t3' act2, t2]; grind
      have := lastF hL (by omega) (by rw [h4]; exact act3)
      rw [h4] at this
      have := ((rowF hL (r := 3) (by omega)).2 this).1
      rw [t3] at this; exact absurd (show ((3 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 3 2 (by decide) (by decide) (by decide))
    · exact h
  have act3 : tr.cell tt 3 SizeV3.act = 0 := c2 la2
  exact ⟨h4,a0,act1,act2,act3,t0,t1,t2,la2⟩

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount.Control
