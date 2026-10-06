import ZkFormal.Chacha.Rng.Table
import ZkFormal.Chacha.Local
import ZkFormal.Chacha.RngSpec

/-!
# ZkFormal.Chacha.Rng.Row — one draw row of `genV3`

On an active row whose word limbs are `< 2^16`: `1 ≤ n < 2^14`, the row accepts iff
`accepts n v` (Lemire), and `m2 = v·n / 2^32` (`draw_row`).
-/

namespace ZkFormal.Chacha.Rng

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Table

abbrev GLocal := Local Rng.Table.constraints

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem mem_cB {x : Nat} (hx : x ∈ boolCols) : ZkFormal.Chacha.Table.boolC x ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; left; left; left; exact List.mem_map.mpr ⟨x, hx, rfl⟩
theorem mem_cH {e : Expr} (h : e ∈ cH) : e ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; left; left; right; exact h
theorem mem_cM {e : Expr} (h : e ∈ cM) : e ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; left; right; exact h
theorem mem_cK {e : Expr} (h : e ∈ cK) : e ∈ constraints := by
  unfold constraints; simp only [List.mem_append]; right; exact h

theorem bit (hL : GLocal tr t pub) {r x : Nat} (hr : r < tr.height t) (h1 : 17 ≤ x) (h2 : x < 136)
    (h3 : x < 21 ∨ 23 ≤ x) : cv tr t r x ≤ 1 :=
  hL.bool hr (mem_cB (by unfold boolCols; simp only [List.mem_append, List.mem_range'_1]; omega))

theorem zev_num (r : Nat) (col : Nat → Nat) (len : Nat) :
    zev (tenv tr t r pub) (num col len) = (numv tr t r col len : Int) :=
  zev_sum_pow _ _ _ len (fun b _ => rfl)

theorem zev_numN {r : Nat} (hr : r + 1 < tr.height t) (col : Nat → Nat) (len : Nat) :
    zev (tenv tr t r pub) (num col len true) = (numv tr t (r + 1) col len : Int) :=
  zev_sum_pow _ _ _ len (fun b _ => by show ((tenv tr t r pub).nxt _ : Int) = _; rw [nxt_cv hr])

theorem numv_lt (hL : GLocal tr t pub) {r : Nat} (hr : r < tr.height t) {col : Nat → Nat} {len : Nat}
    (hb : ∀ b, b < len → cv tr t r (col b) ≤ 1) : numv tr t r col len < 2 ^ len := nbits_lt hb

/-! ## `nbits` facts -/

theorem nbits_ge {f : Nat → Nat} {n i : Nat} (hi : i < n) (h : f i = 1) : 2 ^ i ≤ nbits f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [nbits]
    by_cases e : i = n
    · subst e; rw [h]; omega
    · have := ih (by omega); omega

theorem nbits_low {f : Nat → Nat} {m n : Nat} (hmn : m ≤ n) (h : ∀ b, m ≤ b → b < n → f b = 0) :
    nbits f n = nbits f m := by
  induction n with
  | zero => rw [show m = 0 by omega]
  | succ n ih =>
    by_cases e : m = n + 1
    · rw [e]
    · simp only [nbits]; rw [h n (by omega) (by omega), ih (by omega) (fun b h1 h2 => h b h1 (by omega))]
      simp

theorem le_sum_mem (f : Nat → Nat) : ∀ (l : List Nat) (x : Nat), x ∈ l → f x ≤ (l.map f).sum
  | [], _, hx => absurd hx (List.not_mem_nil)
  | z :: l, x, hx => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := le_sum_mem f l x hx'; omega

/-- A sum of `0/1` values equal to `1` has exactly one `1`. -/
theorem sum_one {f : Nat → Nat} (hb : ∀ i, f i ≤ 1) :
    ∀ len, ((List.range len).map f).sum = 1 → ∃ i, i < len ∧ f i = 1 ∧ ∀ i', i' < len → i' ≠ i → f i' = 0
  | 0, h => by simp at h
  | len + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    have := hb len
    rcases (show f len = 0 ∨ f len = 1 by omega) with e | e
    · rw [e] at h
      obtain ⟨i, hi, h1, h0⟩ := sum_one hb len (by omega)
      exact ⟨i, by omega, h1, fun i' hi' hne => by
        rcases Nat.lt_or_ge i' len with h' | h'
        · exact h0 i' h' hne
        · rw [show i' = len by omega]; exact e⟩
    · rw [e] at h
      have hz : ((List.range len).map f).sum = 0 := by omega
      refine ⟨len, by omega, e, fun i' hi' hne => ?_⟩
      have : f i' ≤ ((List.range len).map f).sum :=
        le_sum_mem f _ i' (List.mem_range.mpr (by omega))
      omega

theorem sum_range_le {f : Nat → Nat} (hb : ∀ i, f i ≤ 1) : ∀ len, ((List.range len).map f).sum ≤ len
  | 0 => by simp
  | len + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := sum_range_le hb len; have := hb len; omega

/-! ## The leading bit -/

theorem zev_sumc (Z : ZEnv) (l : List Nat) (col : Nat → Nat) :
    zev Z (ZkFormal.Chacha.Table.E.sum (l.map fun x => ZkFormal.Chacha.Table.E.c (col x))) = ((l.map fun x => Z.cur (col x)).sum : Int) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ZkFormal.Chacha.Table.E.sum, ih]

theorem sum_zero_mem {f : Nat → Nat} : ∀ (l : List Nat), (l.map f).sum = 0 → ∀ x ∈ l, f x = 0
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | z :: l, h, x, hx => by
    simp only [List.map_cons, List.sum_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · exact sum_zero_mem l (by omega) x hx'

section
variable (hL : GLocal tr t pub) {r : Nat} (hr : r < tr.height t)
include hL hr

theorem bH {i : Nat} (hi : i < 14) : cv tr t r (colH i) ≤ 1 := bit hL hr (by unfold colH; omega) (by unfold colH; omega) (by unfold colH; omega)
theorem bN {i : Nat} (hi : i < 14) : cv tr t r (colN i) ≤ 1 := bit hL hr (by unfold colN; omega) (by unfold colN; omega) (by unfold colN; omega)
theorem bA : cv tr t r colA ≤ 1 := bit hL hr (by decide) (by decide) (by decide)
theorem bAcc : cv tr t r colAcc ≤ 1 := bit hL hr (by decide) (by decide) (by decide)
theorem bSt : cv tr t r colSt ≤ 1 := bit hL hr (by decide) (by decide) (by decide)

/-- `Σ H = a`. -/
theorem sumH : ((List.range 14).map fun i => cv tr t r (colH i)).sum = cv tr t r colA := by
  have hz := hL.zc hr (mem_cH (e := ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sum ((List.range 14).map fun i => ZkFormal.Chacha.Table.E.c (colH i))) (ZkFormal.Chacha.Table.E.c colA))
    (by simp [cH]))
  rw [zev_sub, zev_sumc, zev_c] at hz
  simp only [cur_cv] at hz
  have h1 := sum_range_le (f := fun i => if i < 14 then cv tr t r (colH i) else 0)
    (fun i => by split <;> first | exact bH hL hr ‹_› | omega) 14
  have e : ((List.range 14).map fun i => if i < 14 then cv tr t r (colH i) else 0) =
      ((List.range 14).map fun i => cv tr t r (colH i)) :=
    List.map_congr_left (fun i hi => by rw [if_pos (List.mem_range.mp hi)])
  rw [e] at h1
  have := bA hL hr; have := cv_lt (tr := tr) (t := t) r colA
  have := hz (by omega) (by omega); omega

/-- On an active row: the leading bit `i` of `n`. -/
theorem lead (ha : cv tr t r colA = 1) :
    ∃ i, i < 14 ∧ cv tr t r (colH i) = 1 ∧ (∀ i', i' < 14 → i' ≠ i → cv tr t r (colH i') = 0) ∧
      2 ^ i ≤ numv tr t r colN 14 ∧ numv tr t r colN 14 < 2 ^ (i + 1) := by
  have hs := sumH hL hr; rw [ha] at hs
  obtain ⟨i, hi, h1, h0⟩ := sum_one (f := fun i => if i < 14 then cv tr t r (colH i) else 0)
    (fun i => by split <;> first | exact bH hL hr ‹_› | omega) 14
    (by rw [← hs]; exact congrArg List.sum (List.map_congr_left (fun i hi => by
      rw [if_pos (List.mem_range.mp hi)])))
  simp only [hi, ite_true] at h1
  have h0' : ∀ i', i' < 14 → i' ≠ i → cv tr t r (colH i') = 0 := fun i' hi' hne => by
    have := h0 i' hi' hne; simp only [hi', ite_true] at this; exact this
  -- `N i = 1`
  have hNi : cv tr t r (colN i) = 1 := by
    have hz := hL.zc hr (mem_cH (e := .mul (ZkFormal.Chacha.Table.E.c (colH i)) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1) (ZkFormal.Chacha.Table.E.c (colN i))))
      (by unfold cH; simp only [List.mem_append]; left; right
          exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [zev_mul, zev_sub, zev_c, zev_k, cur_cv, h1] at hz
    have := bN hL hr hi; have := hz (by omega) (by omega); omega
  -- higher bits zero
  have hup : ∀ b, i + 1 ≤ b → b < 14 → cv tr t r (colN b) = 0 := by
    have hz := hL.zc hr (mem_cH (e := .mul (ZkFormal.Chacha.Table.E.c (colH i))
      (ZkFormal.Chacha.Table.E.sum ((List.range' (i + 1) (13 - i)).map fun i' => ZkFormal.Chacha.Table.E.c (colN i'))))
      (by unfold cH; simp only [List.mem_append]; right
          exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    rw [zev_mul, zev_c, zev_sumc] at hz
    simp only [cur_cv, h1] at hz
    have hb : ((List.range' (i + 1) (13 - i)).map fun i' => cv tr t r (colN i')).sum ≤ 13 - i := by
      have := sum_range_le (f := fun b => if b < 13 - i then cv tr t r (colN (i + 1 + b)) else 0)
        (fun b => by split <;> first | exact bN hL hr (by omega) | omega) (13 - i)
      rw [List.range'_eq_map_range, List.map_map]
      have e : ((List.range (13 - i)).map ((fun i' => cv tr t r (colN i')) ∘ fun b => i + 1 + b)) =
          ((List.range (13 - i)).map fun b => if b < 13 - i then cv tr t r (colN (i + 1 + b)) else 0) :=
        List.map_congr_left (fun b hb => by rw [if_pos (List.mem_range.mp hb)]; rfl)
      rw [e]; exact this
    have hz' := hz (by omega) (by omega)
    intro b hb1 hb2
    exact sum_zero_mem (f := fun i' => cv tr t r (colN i')) (List.range' (i + 1) (13 - i)) (by omega) b
      (List.mem_range'_1.mpr ⟨hb1, by omega⟩)
  refine ⟨i, hi, h1, h0', nbits_ge hi hNi, ?_⟩
  unfold numv
  rw [nbits_low (m := i + 1) (by omega) (fun b h1 h2 => hup b h1 h2)]
  exact nbits_lt (fun b hb => bN hL hr (by omega))

theorem num_lt {col : Nat → Nat} {len : Nat} (hb : ∀ b, b < len → cv tr t r (col b) ≤ 1) :
    numv tr t r col len < 2 ^ len := nbits_lt hb

theorem zev_zE {i : Nat} (hi : i < 14) (h1 : cv tr t r (colH i) = 1)
    (h0 : ∀ i', i' < 14 → i' ≠ i → cv tr t r (colH i') = 0) :
    zev (tenv tr t r pub) zE = ((2 ^ (15 - i) * numv tr t r colN 14 : Nat) : Int) := by
  unfold zE
  rw [zev_sel _ colH 14 _ i hi h1 h0, zev_smul, nE, zev_num]
  simp [Int.natCast_mul, Int.natCast_pow]

/-- **One draw.** -/
theorem draw_row (ha : cv tr t r colA = 1) (hv0 : cv tr t r colVlo < 65536)
    (hv1 : cv tr t r colVhi < 65536) :
    1 ≤ numv tr t r colN 14 ∧ numv tr t r colN 14 < 2 ^ 14 ∧
    (cv tr t r colAcc = 1 ↔
      accepts (numv tr t r colN 14) (cv tr t r colVlo + 65536 * cv tr t r colVhi) = true) ∧
    numv tr t r colM2 14 =
      (cv tr t r colVlo + 65536 * cv tr t r colVhi) * numv tr t r colN 14 / NearSpecV3.M32 := by
  obtain ⟨i, hi, h1, h0, hlo, hhi⟩ := lead hL hr ha
  have hn14 : numv tr t r colN 14 < 2 ^ 14 :=
    Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by omega))
  have bnd := fun (col : Nat → Nat) (len : Nat) (hc : ∀ b, b < len → 23 ≤ col b ∧ col b < 136) =>
    num_lt hL hr (col := col) (len := len) (fun b hb => bit hL hr (by have := (hc b hb).1; omega) (hc b hb).2 (Or.inr (hc b hb).1))
  have hm0 := bnd colM0 16 (fun b hb => by unfold colM0; omega)
  have hc0 := bnd colC0 14 (fun b hb => by unfold colC0; omega)
  have hm1 := bnd colM1 16 (fun b hb => by unfold colM1; omega)
  have hm2 := bnd colM2 14 (fun b hb => by unfold colM2; omega)
  have hdl := bnd colDl 16 (fun b hb => by unfold colDl; omega)
  have hacc := bAcc hL hr
  generalize hn : numv tr t r colN 14 = nn at *
  generalize hv0' : cv tr t r colVlo = vlo at *
  generalize hv1' : cv tr t r colVhi = vhi at *
  have hP1 : vlo * nn ≤ 65535 * 16383 := Nat.mul_le_mul (by omega) (by omega)
  have hP2 : vhi * nn ≤ 65535 * 16383 := Nat.mul_le_mul (by omega) (by omega)
  -- the two products
  have z0 := hL.zc hr (mem_cM (e := ZkFormal.Chacha.Table.E.sub (.mul (ZkFormal.Chacha.Table.E.c colVlo) nE)
    (.add m0E (ZkFormal.Chacha.Table.E.smul 65536 c0E))) (by simp [cM]))
  have z1 := hL.zc hr (mem_cM (e := ZkFormal.Chacha.Table.E.sub
    (.add (.mul (ZkFormal.Chacha.Table.E.c colVhi) nE) c0E)
    (.add m1E (ZkFormal.Chacha.Table.E.smul 65536 m2E))) (by simp [cM]))
  simp only [zev_sub, zev_mul, zev_add, zev_smul, zev_c, cur_cv, nE, m0E, c0E, m1E, m2E,
    zev_num, hn, hv0', hv1', ← Int.natCast_mul] at z0 z1
  have hvn : (vlo + 65536 * vhi) * nn = vlo * nn + 65536 * (vhi * nn) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have hacc_iff := accepts_iff (v := vlo + 65536 * vhi) hlo hhi (by omega) (by omega)
  rw [Nat.mul_comm nn] at hacc_iff
  rw [hvn] at hacc_iff ⊢
  generalize vlo * nn = P1 at *
  generalize vhi * nn = P2 at *
  have e0 := z0 (by omega) (by omega)
  have e1 := z1 (by omega) (by omega)
  -- `Z`
  have hZ := zev_zE hL hr (pub := pub) hi h1 h0
  rw [hn] at hZ
  have hZlo : 2 ^ 15 ≤ 2 ^ (15 - i) * nn := by
    have := Nat.mul_le_mul_left (2 ^ (15 - i)) hlo
    rwa [← Nat.pow_add, show 15 - i + i = 15 by omega] at this
  have hZhi : 2 ^ (15 - i) * nn < 2 ^ 16 := by
    have := Nat.mul_lt_mul_of_pos_left hhi (Nat.two_pow_pos (15 - i))
    rwa [← Nat.pow_add, show 15 - i + (i + 1) = 16 by omega] at this
  generalize 2 ^ (15 - i) * nn = Zv at *
  have z2 := hL.zc hr (mem_cM (e := ZkFormal.Chacha.Table.E.sub
    (ZkFormal.Chacha.Table.E.sub dlE (.mul (ZkFormal.Chacha.Table.E.c colAcc)
      (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.sub zE (ZkFormal.Chacha.Table.E.k 1)) m1E)))
    (.mul (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.k 1) (ZkFormal.Chacha.Table.E.c colAcc))
      (ZkFormal.Chacha.Table.E.sub m1E zE))) (by simp [cM]))
  simp only [zev_sub, zev_mul, zev_k, zev_c, cur_cv, dlE, m1E, zev_num, hZ] at z2
  refine ⟨Nat.le_trans (Nat.one_le_two_pow) hlo, hn14, ?_, ?_⟩
  · rw [hacc_iff]
    have hd := hdl; have h1' := hm1; have h0' := hm0
    rcases (show cv tr t r colAcc = 0 ∨ cv tr t r colAcc = 1 by omega) with e | e <;> rw [e] at z2 ⊢
    · have := z2 (by simp; omega) (by simp; omega)
      simp at this
      constructor
      · intro h; omega
      · intro h; omega
    · have := z2 (by simp; omega) (by simp; omega)
      simp at this
      constructor
      · intro _; omega
      · intro _; rfl
  · unfold NearSpecV3.M32; omega
end

end ZkFormal.Chacha.Rng
