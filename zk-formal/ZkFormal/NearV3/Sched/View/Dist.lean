import ZkFormal.NearV3.Sched.View.Mem
import ZkFormal.NearV3.Sched.Tables.Dist

/-!
# ZkFormal.NearV3.Sched.View.Dist — the divisions of `sdsV3` are exact integer divisions

The quotients are range-checked (`q < 2^23`, 23 bits) and so are the remainders (`r < 64`, 6 bits,
and `N − 1 − r < 64`), so `L = q·N + r` holds over the naturals (`q·N + r < 2^30 < P`) with
`r < N`; hence `q = L / N`, `r = L % N` (`div_of_row`). Every other cell is a function of these.

* `cell_div` — an allowed cell: `SL = q1·SN + r1`, `r1 < SN`, `RL = q2·RN + r2`, `r2 < RN`,
  `q1 = SL / SN`, `q2 = RL / RN`, and `gb = cb ? q2 : q1`;
* `shard_div` — a shard row with `links ≠ 0`: `left = avg·links + rem`, `avg = left / links`;
  with `links = 0`: `avg = 0`.
-/

namespace ZkFormal.NearV3.Sched.Dist

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

abbrev DLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop := Local constraints tr t pub

section
variable {tr : Trace Fp} {td : Nat} {pub : List Fp}

theorem mem_bool_bt1 {i : Nat} (hi : i < 6) : bt1 i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi)))))))
theorem mem_bool_bt2 {i : Nat} (hi : i < 6) : bt2 i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi))))))
theorem mem_bool_qb1 {i : Nat} (hi : i < 23) : qb1 i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi)))))
theorem mem_bool_qb2 {i : Nat} (hi : i < 23) : qb2 i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi))))
theorem mem_bool_rb1 {i : Nat} (hi : i < 6) : rb1 i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi)))
theorem mem_bool_rb2 {i : Nat} (hi : i < 6) : rb2 i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi))

theorem bool_of (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) {x : Nat}
    (hx : x ∈ boolCols) : cv tr td r x ≤ 1 :=
  hL.bool hr (by
    unfold constraints cKind
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem hx)))))

/-- A bit-decomposed expression evaluates to `numv`, below `2^len`. -/
theorem num_eval (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) (col : Nat → Nat) (len : Nat)
    (hc : ∀ i, i < len → col i ∈ boolCols) :
    zev (tenv tr td r pub) (ZkFormal.Chacha.Rng.Table.num col len) = (numv tr td r col len : Int) ∧
      numv tr td r col len < 2 ^ len := by
  refine ⟨?_, nbits_le_of (fun i hi => bool_of hL hr (hc i hi))⟩
  unfold ZkFormal.Chacha.Rng.Table.num numv
  exact zev_sum_pow _ (fun b => .col (col b) false) (fun b => cv tr td r (col b)) len (fun _ _ => rfl)

/-- A cell equal to a bit decomposition (constraint `x − num col len`) is below `2^len`. -/
theorem range_of (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) {x : Nat} {col : Nat → Nat}
    {len : Nat} (he : sub (c x) (ZkFormal.Chacha.Rng.Table.num col len) ∈ constraints)
    (hc : ∀ i, i < len → col i ∈ boolCols) (hlen : len ≤ 30) : cv tr td r x < 2 ^ len := by
  obtain ⟨e, b⟩ := num_eval hL hr col len hc
  have h := hL.zc hr he
  simp only [zev_sub, zev_c, cur_cv, e] at h
  have hx := cv_lt (tr := tr) (t := td) r x
  have : (2 : Nat) ^ len ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hlen
  have := h (by omega) (by omega)
  omega

/-- Ranges of the quotients and remainders (every row). -/
theorem ranges (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) :
    cv tr td r q1 < 2 ^ 23 ∧ cv tr td r q2 < 2 ^ 23 ∧ cv tr td r r1 < 64 ∧ cv tr td r r2 < 64 :=
  ⟨range_of hL hr (by simp [constraints, cRange]) (fun _ hi => mem_bool_qb1 hi) (by decide),
   range_of hL hr (by simp [constraints, cRange]) (fun _ hi => mem_bool_qb2 hi) (by decide),
   range_of hL hr (by simp [constraints, cRange]) (fun _ hi => mem_bool_rb1 hi) (by decide),
   range_of hL hr (by simp [constraints, cRange]) (fun _ hi => mem_bool_rb2 hi) (by decide)⟩

/-- **Exact division.** From `x·(L − (q·N + r)) ≡ 0` and `x·(N − 1 − r − bits) ≡ 0` with `x = 1`,
`q < 2^23`, `r < 64`, 6 bits: `L = q·N + r` over the naturals and `r < N`. -/
theorem div_of_row {L q N rr : Nat} (hL : L < 2013265921) (hN : N < 2013265921) (hq : q < 2 ^ 23)
    (hr : rr < 64) {bits : Nat} (hb : bits < 64) (k : Int)
    (h1 : (L : Int) - ((q * N : Nat) + rr) = 2013265921 * k) (h2 : (N : Int) - 1 - rr - bits = 0) :
    L = q * N + rr ∧ rr < N ∧ q = L / N ∧ rr = L % N := by
  have hN' : N ≤ 127 := by omega
  have hX : q * N ≤ (2 ^ 23 - 1) * 127 := Nat.mul_le_mul (by omega) hN'
  have hLe : L = q * N + rr := by omega
  have hlt : rr < N := by omega
  refine ⟨hLe, hlt, ?_, ?_⟩
  · rw [hLe, Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hlt]; omega
  · rw [hLe, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- **Allowed cell.** -/
theorem cell_div (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) (ha : cv tr td r al = 1) :
    cv tr td r L1 = cv tr td r q1 * cv tr td r N1 + cv tr td r r1 ∧ cv tr td r r1 < cv tr td r N1 ∧
      cv tr td r q1 = cv tr td r L1 / cv tr td r N1 ∧
      cv tr td r L2 = cv tr td r q2 * cv tr td r N2 + cv tr td r r2 ∧ cv tr td r r2 < cv tr td r N2 ∧
      cv tr td r q2 = cv tr td r L2 / cv tr td r N2 ∧
      cv tr td r gb = (if cv tr td r cb = 1 then cv tr td r q2 else cv tr td r q1) := by
  obtain ⟨hq1, hq2, hr1, hr2⟩ := ranges hL hr
  have lt := fun x => cv_lt (tr := tr) (t := td) r x
  obtain ⟨k1, d1⟩ := Mem.zdvd hL hr (e := .mul (c al) (sub (c L1) (.add (.mul (c q1) (c N1)) (c r1))))
    (by simp [constraints, cGrid])
  obtain ⟨k2, d2⟩ := Mem.zdvd hL hr (e := .mul (c al) (sub (c L2) (.add (.mul (c q2) (c N2)) (c r2))))
    (by simp [constraints, cGrid])
  have c3 := hL.zc hr (e := .mul (c al) (sub (sub (sub (c N1) (k 1)) (c r1)) bits1E)) (by simp [constraints, cGrid])
  have c4 := hL.zc hr (e := .mul (c al) (sub (sub (sub (c N2) (k 1)) (c r2)) bits2E)) (by simp [constraints, cGrid])
  have c5 := hL.zc hr (e := .mul (c al) (sub (c gb) (.add (.mul (c cb) (c q2)) (.mul (sub (k 1) (c cb)) (c q1)))))
    (by simp [constraints, cGrid, notE])
  obtain ⟨e1, b1⟩ := num_eval hL hr bt1 6 (fun _ hi => mem_bool_bt1 hi)
  obtain ⟨e2, b2⟩ := num_eval hL hr bt2 6 (fun _ hi => mem_bool_bt2 hi)
  simp only [bits1E, bits2E, zev_mul, zev_sub, zev_add, zev_c, zev_k, cur_cv, ha, e1, e2] at d1 d2 c3 c4 c5
  push_cast at d1 d2 c3 c4 c5
  have hN1 := lt N1; have hN2 := lt N2
  have f3 := c3 (by omega) (by omega)
  have f4 := c4 (by omega) (by omega)
  rw [← Int.natCast_mul] at d1 d2
  have D1 := div_of_row (lt L1) hN1 hq1 hr1 b1 k1 (by omega) (by omega)
  have D2 := div_of_row (lt L2) hN2 hq2 hr2 b2 k2 (by omega) (by omega)
  refine ⟨D1.1, D1.2.1, D1.2.2.1, D2.1, D2.2.1, D2.2.2.1, ?_⟩
  have hcb := bool_of hL hr (x := cb) (by simp [boolCols])
  have hgb := lt gb
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcb with h | h <;> rw [h] at c5 ⊢ <;> push_cast at c5 <;>
    simp only [ite_true, show ¬ ((0 : Nat) = 1) from by decide, ite_false] <;>
    (have := c5 (by omega) (by omega); omega)

/-- **Shard row.** `links ≠ 0`: `left = avg·links + rem`, `avg = left / links`; `links = 0`: `avg = 0`. -/
theorem shard_div (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) (hs : cv tr td r kSh = 1) :
    (cv tr td r N2 ≠ 0 → cv tr td r L2 = cv tr td r q2 * cv tr td r N2 + cv tr td r r2 ∧
        cv tr td r r2 < cv tr td r N2 ∧ cv tr td r q2 = cv tr td r L2 / cv tr td r N2) ∧
      (cv tr td r N2 = 0 → cv tr td r q2 = 0) := by
  obtain ⟨-, hq2, -, hr2⟩ := ranges hL hr
  have lt := fun x => cv_lt (tr := tr) (t := td) r x
  have hzc := bool_of hL hr (x := zc) (by simp [boolCols])
  -- zc = [N2 = 0]
  have z1 := hL.zc hr (e := .mul (c kSh) (sub (c zc) (notE (.mul (c N2) (c icnt))))) (by simp [constraints, cShard])
  obtain ⟨kz, z2⟩ := Mem.zdvd hL hr (e := mul3 (c kSh) (c N2) (c zc)) (by simp [constraints, cShard])
  obtain ⟨k2, d2⟩ := Mem.zdvd hL hr (e := mul3 (c kSh) (notE (c zc)) (sub (c L2) (.add (.mul (c q2) (c N2)) (c r2))))
    (by simp [constraints, cShard])
  have c4 := hL.zc hr (e := mul3 (c kSh) (notE (c zc)) (sub (sub (sub (c N2) (k 1)) (c r2)) bits2E))
    (by simp [constraints, cShard])
  have c6 := hL.zc hr (e := mul3 (c kSh) (c zc) (c q2)) (by simp [constraints, cShard])
  obtain ⟨e2, b2⟩ := num_eval hL hr bt2 6 (fun _ hi => mem_bool_bt2 hi)
  simp only [mul3, notE, bits2E, zev_mul, zev_sub, zev_add, zev_c, zev_k, cur_cv, hs, e2] at z1 z2 d2 c4 c6
  have hN2 := lt N2; have hq := lt q2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hzc with h | h <;> rw [h] at z1 z2 d2 c4 c6 <;>
    push_cast at z1 z2 d2 c4 c6
  · -- zc = 0: N2 ≠ 0 (from N2·icnt = 1) and an exact division
    refine ⟨fun _ => ?_, fun h0 => ?_⟩
    · have f4 := c4 (by omega) (by omega)
      rw [← Int.natCast_mul] at d2
      have D := div_of_row (lt L2) hN2 hq2 hr2 b2 k2 (by omega) (by omega)
      exact ⟨D.1, D.2.1, D.2.2.1⟩
    · rw [h0] at z1; simp at z1
  · -- zc = 1: N2 = 0 and q2 = 0
    refine ⟨fun hne => ?_, fun _ => ?_⟩
    · exfalso; apply hne; omega
    · have := c6 (by omega) (by omega); omega

end

end ZkFormal.NearV3.Sched.Dist
