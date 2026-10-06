import ZkFormal.Chacha.ZEval
import ZkFormal.Sha.Eval

/-!
# ZkFormal.Chacha.Sound.Basic — local facts of a `chachaV3` table

`ChLocal tr t pub`: table `t` of `tr` has a legal height and every constraint vanishes on
every row.  Consequences on single rows: booleanity, one-hot flags, the `dr` counter.
-/

namespace ZkFormal.Chacha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table

/-- Table `t` of `tr` is a legal ChaCha table. -/
structure ChLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop where
  log_ge : 1 ≤ tr.log t
  log_le : tr.log t ≤ Table.maxLog
  constr : ∀ r, r < tr.height t → ∀ e ∈ Table.constraints, e.eval tr t r pub = 0

/-- Cell as a natural. -/
def nv (tr : Trace Fp) (t r c : Nat) : Nat := (tr.cell t r c).toNat

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem mem_cBool {e : Expr} (h : e ∈ cBool) : e ∈ constraints := by
  unfold constraints; simp [h]
theorem mem_cKind {e : Expr} (h : e ∈ cKind) : e ∈ constraints := by
  unfold constraints; simp [h]
theorem mem_cInit {e : Expr} (h : e ∈ cInit) : e ∈ constraints := by
  unfold constraints; simp [h]
theorem mem_cCopy {e : Expr} (h : e ∈ cCopy) : e ∈ constraints := by
  unfold constraints; simp [h]
theorem mem_cQR {e : Expr} (h : e ∈ cQR) : e ∈ constraints := by
  unfold constraints; simp [h]
theorem mem_cFF {e : Expr} (h : e ∈ cFF) : e ∈ constraints := by
  unfold constraints; simp [h]

theorem height_pos (tr : Trace Fp) (t : Nat) : 0 < tr.height t := Nat.two_pow_pos _

theorem cur_eq (r x : Nat) : (tenv tr t r pub).cur x = nv tr t r x := rfl

theorem nxt_eq {r : Nat} (hr : r + 1 < tr.height t) (x : Nat) :
    (tenv tr t r pub).nxt x = nv tr t (r + 1) x := by
  show (tr.cell t ((r + 1) % tr.height t) x).toNat = _
  rw [Nat.mod_eq_of_lt hr]; rfl

theorem nv_lt (r x : Nat) : nv tr t r x < 2013265921 := (tr.cell t r x).toNat_lt

/-- A vanishing constraint with small integer value. -/
theorem zc (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {e : Expr}
    (he : e ∈ constraints) (h1 : -2013265921 < zev (tenv tr t r pub) e)
    (h2 : zev (tenv tr t r pub) e < 2013265921) : zev (tenv tr t r pub) e = 0 :=
  zev_eq_zero (hL.constr r hr e he) h1 h2

/-! ## Booleanity -/

theorem bool_of (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {x : Nat}
    (hx : x ∈ boolCols) : nv tr t r x ≤ 1 := by
  have h := hL.constr r hr (boolC x) (mem_cBool (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have h' : Fp.mul (tr.cell t r x) (Fp.add (tr.cell t r x) (Fp.neg (Fp.ofNat 1))) = 0 := h
  rcases ZkFormal.Sha.fp_mul_eq_zero h' with h0 | h1
  · unfold nv; rw [h0]; decide
  · have : tr.cell t r x = Fp.ofNat 1 := by
      have e := congrArg (fun z => Fp.add z (Fp.ofNat 1)) h1
      apply Fp.ext
      have h3 := congrArg Fp.toNat e
      simp only [Fp.toNat_add, Fp.toNat_neg, Fp.toNat_ofNat] at h3
      have := (tr.cell t r x).toNat_lt
      rw [show (0 : Fp) = Fp.ofNat 0 from rfl, Fp.toNat_ofNat] at h3
      rw [Fp.toNat_ofNat]
      unfold P at *
      omega
    unfold nv; rw [this]; decide

theorem mem_boolX {m b : Nat} (hm : m < 6) (hb : b < 32) : colX m b ∈ boolCols := by
  unfold boolCols colX; simp only [List.mem_append, List.mem_range'_1]; omega
theorem mem_boolC {q l : Nat} (hq : q < 4) (hl : l < 2) : colC q l ∈ boolCols := by
  unfold boolCols colC; simp only [List.mem_append, List.mem_range'_1]; omega
theorem mem_boolHi {x : Nat} (h1 : 250 ≤ x) (h2 : x < 272) : x ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_range'_1]; omega

theorem bX (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {m b : Nat} (hm : m < 6)
    (hb : b < 32) : nv tr t r (colX m b) ≤ 1 := bool_of hL hr (mem_boolX hm hb)
theorem bC (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {q l : Nat} (hq : q < 4)
    (hl : l < 2) : nv tr t r (colC q l) ≤ 1 := bool_of hL hr (mem_boolC hq hl)
theorem bHi (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {x : Nat} (h1 : 250 ≤ x)
    (h2 : x < 272) : nv tr t r x ≤ 1 := bool_of hL hr (mem_boolHi h1 h2)

/-! ## One-hot flags -/

theorem flagCols_eq : flagCols = [250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263] := rfl

theorem le_sum_of_mem' (f : Nat → Nat) : ∀ (l : List Nat) (x : Nat), x ∈ l → f x ≤ (l.map f).sum
  | [], _, hx => absurd hx (List.not_mem_nil)
  | z :: l, x, hx => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := le_sum_of_mem' f l x hx'; omega

theorem sum_two_le (f : Nat → Nat) : ∀ (l : List Nat), l.Nodup → ∀ x y, x ∈ l → y ∈ l → x ≠ y →
    f x + f y ≤ (l.map f).sum
  | [], _, _, _, hx, _, _ => absurd hx (List.not_mem_nil)
  | z :: l, hnd, x, y, hx, hy, hxy => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hxy
      · have : f y ≤ (l.map f).sum := le_sum_of_mem' f l y hy'
        omega
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have : f x ≤ (l.map f).sum := le_sum_of_mem' f l x hx'
        omega
      · have := sum_two_le f l hnd'.2 x y hx' hy' hxy; omega

/-- Sum of the flags of row `r`. -/
def fsum (tr : Trace Fp) (t r : Nat) : Nat := (flagCols.map (nv tr t r)).sum

theorem zev_flagSum (r : Nat) : zev (tenv tr t r pub) flagSum = (fsum tr t r : Int) := by
  unfold flagSum fsum
  rw [zev_sum, flagCols_eq]
  simp [cur_eq]

theorem fsum_le_one (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) : fsum tr t r ≤ 1 := by
  have hb : ∀ x ∈ flagCols, nv tr t r x ≤ 1 := by
    intro x hx; rw [flagCols_eq] at hx; simp at hx
    exact bHi hL hr (by omega) (by omega)
  have hle : fsum tr t r ≤ 14 := by
    unfold fsum
    have : ∀ (l : List Nat), (∀ x ∈ l, nv tr t r x ≤ 1) → (l.map (nv tr t r)).sum ≤ l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons x l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := hl x (List.mem_cons_self ..); have := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        omega
    have := this flagCols hb
    have hl : flagCols.length = 14 := rfl
    omega
  have h := zc hL hr (mem_cKind (e := .mul flagSum (E.sub flagSum (E.k 1))) (by simp [cKind]))
  simp only [zev_mul, zev_sub, zev_k, zev_flagSum, show ((1 : Nat) : Int) = 1 from rfl] at h
  rcases Nat.eq_zero_or_pos (fsum tr t r) with h0 | h0
  · omega
  have : (fsum tr t r : Int) * ((fsum tr t r : Int) - 1) = 0 := by
    apply h
    · have : (0 : Int) ≤ (fsum tr t r : Int) * ((fsum tr t r : Int) - 1) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    · have : (fsum tr t r : Int) * ((fsum tr t r : Int) - 1) ≤ 14 * 14 :=
        Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      omega
  rcases Int.mul_eq_zero.mp this with h0 | h0 <;> omega

theorem flag_unique (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {x y : Nat}
    (hx : x ∈ flagCols) (hy : y ∈ flagCols) (hxy : y ≠ x) (h1 : nv tr t r x = 1) :
    nv tr t r y = 0 := by
  have := sum_two_le (nv tr t r) flagCols (by rw [flagCols_eq]; decide) x y hx hy (Ne.symm hxy)
  have := fsum_le_one hL hr
  unfold fsum at *
  omega

theorem mem_flag_P {p : Nat} (hp : p < 8) : colP p ∈ flagCols := by
  rw [flagCols_eq]; unfold colP; simp; omega
theorem mem_flag_F {j : Nat} (hj : j < 4) : colF j ∈ flagCols := by
  rw [flagCols_eq]; unfold colF; simp; omega
theorem mem_flag_I0 : colI0 ∈ flagCols := by rw [flagCols_eq]; decide
theorem mem_flag_I1 : colI1 ∈ flagCols := by rw [flagCols_eq]; decide

/-! ## The double-round counter -/

def drv (tr : Trace Fp) (t r : Nat) : Nat :=
  nv tr t r (colDr 0) + 2 * nv tr t r (colDr 1) + 4 * nv tr t r (colDr 2) + 8 * nv tr t r (colDr 3)

theorem zev_drC (r : Nat) : zev (tenv tr t r pub) drC = (drv tr t r : Int) := by
  simp [drC, drv, zev_sum, List.range_succ, cur_eq]; omega

theorem zev_drN {r : Nat} (hr : r + 1 < tr.height t) :
    zev (tenv tr t r pub) drN = (drv tr t (r + 1) : Int) := by
  simp [drN, drv, zev_sum, List.range_succ, nxt_eq hr]; omega

theorem drBits (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) {b : Nat} (hb : b < 4) :
    nv tr t r (colDr b) ≤ 1 := bHi hL hr (by unfold colDr; omega) (by unfold colDr; omega)

theorem drv_le (hL : ChLocal tr t pub) {r : Nat} (hr : r < tr.height t) : drv tr t r ≤ 9 := by
  have h1 := zc hL hr (mem_cKind (e := .mul (E.c (colDr 3)) (E.c (colDr 1))) (by simp [cKind]))
  have h2 := zc hL hr (mem_cKind (e := .mul (E.c (colDr 3)) (E.c (colDr 2))) (by simp [cKind]))
  simp only [zev_mul, zev_c, cur_eq] at h1 h2
  have b0 := drBits hL hr (b := 0) (by decide); have b1 := drBits hL hr (b := 1) (by decide)
  have b2 := drBits hL hr (b := 2) (by decide); have b3 := drBits hL hr (b := 3) (by decide)
  unfold drv
  generalize nv tr t r (colDr 0) = x0 at *; generalize nv tr t r (colDr 1) = x1 at *
  generalize nv tr t r (colDr 2) = x2 at *; generalize nv tr t r (colDr 3) = x3 at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b3 with rfl | rfl
  · omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with rfl | rfl
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b2 with rfl | rfl
      · omega
      · simp at h2
    · simp at h1

end ZkFormal.Chacha.Sound
