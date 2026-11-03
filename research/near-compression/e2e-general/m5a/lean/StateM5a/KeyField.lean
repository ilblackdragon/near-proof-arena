import StateM5a.Trie
import ZkFormal.Sha.Sound.Bridge
import NearSpec.Trie

/-!
# StateM5a.KeyField — the `KEY` table's nibbles are `NearSpec.nibbles` of the hashed key bytes

A field-level lemma, stated about the exported AIR value itself: on any row of any trace on which
`Key.table`'s constraints vanish over BabyBear, the two nibbles the row provides on `NIB`
(`hi` at index `2j`, `lo` at `2j + 1`) are `< 16`, the byte it sends to the SHA-256 table is
`16·hi + lo < 256`, and `NearSpec.nibbles [byte] = [hi, lo]`.  So every nibble a walk row or a
`KCMP` row looks up is a nibble (in `nibbles`' order) of the key whose SHA-256 the working set binds.
-/

namespace StateM5a.KeyField

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-- Column `s + j` of `KEY` on row `r`, as a natural. -/
def cv (tr : Trace Fp) (t r : Nat) (s : String) (j : Nat := 0) : Nat :=
  (tr.cell t r (Key.L.off s + j)).toNat

theorem ev_col (i : Nat) : ev tr t r pub (.col i false) = (tr.cell t r i).toNat := rfl

theorem bool_le {x : Expr} (h : ev tr t r pub (bool x) = 0) : ev tr t r pub x ≤ 1 := by
  change ev tr t r pub (Expr.mul x (Expr.add x (Expr.neg (Expr.const 1)))) = 0 at h
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  rcases ev_mul_eq_zero h with h | h
  · omega
  · simp only [ev_add, ev_neg, ev_const] at h
    omega

theorem hold {e : Expr} (hc : ∀ e ∈ Key.table.constraints, e.eval tr t r pub = 0)
    (he : e ∈ Key.constraints) : ev tr t r pub e = 0 := ev_of_eval (hc e he)

/-- A 4-bit decomposition `x − Σ_k 2^k b_k = 0` with boolean `b_k` bounds `x < 16`. -/
theorem nib_lt (x : String) (bits : String)
    (hc : ∀ e ∈ Key.table.constraints, e.eval tr t r pub = 0)
    (hb : ∀ k, k < 4 → bool (Key.c bits k) ∈ Key.constraints)
    (hd : Key.c x - sumE ((List.range 4).map fun k => sm (2 ^ k) (Key.c bits k)) ∈ Key.constraints) :
    cv tr t r x < 16 := by
  have b0 : ev tr t r pub (Key.c bits 0) ≤ 1 := bool_le (hold hc (hb 0 (by decide)))
  have b1 : ev tr t r pub (Key.c bits 1) ≤ 1 := bool_le (hold hc (hb 1 (by decide)))
  have b2 : ev tr t r pub (Key.c bits 2) ≤ 1 := bool_le (hold hc (hb 2 (by decide)))
  have b3 : ev tr t r pub (Key.c bits 3) ≤ 1 := bool_le (hold hc (hb 3 (by decide)))
  have h := hold hc hd
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Key.c x)
  change ev tr t r pub (Expr.add (Key.c x) (Expr.neg (Expr.add (sm 1 (Key.c bits 0))
    (Expr.add (sm 2 (Key.c bits 1)) (Expr.add (sm 4 (Key.c bits 2)) (sm 8 (Key.c bits 3))))))) = 0 at h
  simp only [sm, ev_add, ev_neg, ev_mul, ev_const, Nat.reduceMod, Nat.one_mul] at h
  unfold cv
  change ev tr t r pub (Key.c x) < 16
  generalize ev tr t r pub (Key.c bits 0) = y0 at b0 h
  generalize ev tr t r pub (Key.c bits 1) = y1 at b1 h
  generalize ev tr t r pub (Key.c bits 2) = y2 at b2 h
  generalize ev tr t r pub (Key.c bits 3) = y3 at b3 h
  generalize ev tr t r pub (Key.c x) = y at hx h ⊢
  have e0 : y0 % 2013265921 = y0 := Nat.mod_eq_of_lt (by omega)
  have e1 : 2 * y1 % 2013265921 = 2 * y1 := Nat.mod_eq_of_lt (by omega)
  have e2 : 4 * y2 % 2013265921 = 4 * y2 := Nat.mod_eq_of_lt (by omega)
  have e3 : 8 * y3 % 2013265921 = 8 * y3 := Nat.mod_eq_of_lt (by omega)
  have e4 : (4 * y2 + 8 * y3) % 2013265921 = 4 * y2 + 8 * y3 := Nat.mod_eq_of_lt (by omega)
  have e5 : (2 * y1 + (4 * y2 + 8 * y3)) % 2013265921 = 2 * y1 + (4 * y2 + 8 * y3) :=
    Nat.mod_eq_of_lt (by omega)
  have e6 : (y0 + (2 * y1 + (4 * y2 + 8 * y3))) % 2013265921 = y0 + (2 * y1 + (4 * y2 + 8 * y3)) :=
    Nat.mod_eq_of_lt (by omega)
  rw [e0, e1, e2, e3, e4, e5, e6] at h
  omega

theorem mem_hib (k : Nat) (hk : k < 4) : bool (Key.c "hib" k) ∈ Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨k, hk, by simp⟩))

theorem mem_lob (k : Nat) (hk : k < 4) : bool (Key.c "lob" k) ∈ Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨k, hk, by simp⟩))

theorem mem_hi : Key.c "hi" - sumE ((List.range 4).map fun k => sm (2 ^ k) (Key.c "hib" k)) ∈
    Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_cons, true_or, or_true]

theorem mem_lo : Key.c "lo" - sumE ((List.range 4).map fun k => sm (2 ^ k) (Key.c "lob" k)) ∈
    Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_cons, true_or, or_true]

/-- **`KEY` row soundness.**  The row's nibbles are those of the byte it hashes. -/
theorem key_row_nibbles (hc : ∀ e ∈ Key.table.constraints, e.eval tr t r pub = 0) :
    cv tr t r "hi" < 16 ∧ cv tr t r "lo" < 16 ∧ 16 * cv tr t r "hi" + cv tr t r "lo" < 256 ∧
      NearSpec.nibbles [UInt8.ofNat (16 * cv tr t r "hi" + cv tr t r "lo")] =
        [cv tr t r "hi", cv tr t r "lo"] := by
  have hhi := nib_lt "hi" "hib" hc mem_hib mem_hi
  have hlo := nib_lt "lo" "lob" hc mem_lob mem_lo
  refine ⟨hhi, hlo, by omega, ?_⟩
  simp only [NearSpec.nibbles, UInt8.toNat_ofNat']
  have : (16 * cv tr t r "hi" + cv tr t r "lo") % 2 ^ 8 = 16 * cv tr t r "hi" + cv tr t r "lo" :=
    Nat.mod_eq_of_lt (by omega)
  rw [this]
  simp only [List.cons.injEq, and_true]
  omega

end StateM5a.KeyField
