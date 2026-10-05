import ZkFormal.Prover.Statements
import ZkFormal.Toy.AirDef
import ZkToySpec

/-!
# ZkFormal.Toy.Air — the M2 toy AIR ("square root of a byte") and its semantics

One table of width 4 (the bits `b₀..b₃` of the root), heights `2..16`:
* `bᵢ·(bᵢ − 1) = 0` for `i < 4`;
* `s·s − pub₀ = 0` with `s = b₀ + 2b₁ + 4b₂ + 8b₃`.

`toy_sound`: `Holds` (on the canonical claim bytes `[b]`) ⇒ `∃ w, w·w = b`
(row 0, bits boolean, `s < 16`, so `s² < 256 < p` and the field equation is the
integer one).  `toy_complete`: the honest trace (every row holds the bits of `w`,
height 2) satisfies `Holds` and has an admissible header.
-/

namespace ZkFormal.Toy

open ArenaCore Lean.Grind ZkFormal.Air ZkFormal.Algebra ZkFormal.Stark

theorem toyAir_tables : toyAir.tables ≠ [] := by simp [toyAir]

/-! ## Field facts -/

theorem fp_ext {a b : Fp} (h : a.toNat = b.toNat) : a = b := Fp.ext h

theorem bool_of {x : Fp} (h : x * (x + -(1 : Fp)) = 0) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have h1 : x + -(1 : Fp) = 0 := by
      have := congrArg (fun y => x⁻¹ * y) h
      rw [← Semiring.mul_assoc, Field.inv_mul_cancel hx, Semiring.one_mul, Semiring.mul_zero] at this
      exact this
    grind

/-! ## Soundness -/

def pubB (b : UInt8) : List Fp := Udr.pubOf Fp (ZkToySpec.encode b)

attribute [local instance] Semiring.natCast

/-- `(n : Fp)` for `n < P` has `toNat = n`. -/
theorem toNat_cast {n : Nat} (h : n < Algebra.P) : ((n : Nat) : Fp).toNat = n := by
  show (Fp.ofNat n).toNat = n
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem root_val (x0 x1 x2 x3 : Fp) (h0 : x0 = 0 ∨ x0 = 1) (h1 : x1 = 0 ∨ x1 = 1)
    (h2 : x2 = 0 ∨ x2 = 1) (h3 : x3 = 0 ∨ x3 = 1) :
    ∃ n : Nat, n < 16 ∧ x0 + (((2 : Nat) : Fp) * x1 + (((4 : Nat) : Fp) * x2 + ((8 : Nat) : Fp) * x3))
      = ((n : Nat) : Fp) := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl
  all_goals first
    | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
    | exact ⟨3, by decide, by decide⟩ | exact ⟨4, by decide, by decide⟩ | exact ⟨5, by decide, by decide⟩
    | exact ⟨6, by decide, by decide⟩ | exact ⟨7, by decide, by decide⟩ | exact ⟨8, by decide, by decide⟩
    | exact ⟨9, by decide, by decide⟩ | exact ⟨10, by decide, by decide⟩ | exact ⟨11, by decide, by decide⟩
    | exact ⟨12, by decide, by decide⟩ | exact ⟨13, by decide, by decide⟩ | exact ⟨14, by decide, by decide⟩
    | exact ⟨15, by decide, by decide⟩

theorem toy_sound (b : UInt8) (tr : Trace Fp) (h : Holds toyAir (pubB b) tr) :
    ∃ w : Nat, w * w = b.toNat := by
  have h0 : 0 < tr.height 0 := Nat.pow_pos (by decide)
  have hc := h.constr 0 (by decide) 0 h0
  have e0 := bool_of (hc (isBool (bit 0)) (by show _ ∈ toyTable.constraints; simp [toyTable]))
  have e1 := bool_of (hc (isBool (bit 1)) (by show _ ∈ toyTable.constraints; simp [toyTable]))
  have e2 := bool_of (hc (isBool (bit 2)) (by show _ ∈ toyTable.constraints; simp [toyTable]))
  have e3 := bool_of (hc (isBool (bit 3)) (by show _ ∈ toyTable.constraints; simp [toyTable]))
  have es := hc (.add (.mul root root) (.neg (.pub 0))) (by show _ ∈ toyTable.constraints; simp [toyTable])
  simp only [Expr.eval, Expr.evalWith, rowEnv, bit, root, ite_false,
    Bool.false_eq_true] at e0 e1 e2 e3 es
  obtain ⟨n, hn, hs⟩ := root_val _ _ _ _ e0 e1 e2 e3
  rw [hs] at es
  have hb : (pubB b).getD 0 0 = ((b.toNat : Nat) : Fp) := rfl
  rw [hb] at es
  have es' : ((n : Nat) : Fp) * ((n : Nat) : Fp) = ((b.toNat : Nat) : Fp) := by
    grind
  have hbl : b.toNat < 256 := b.toNat_lt
  have hP : n * n < Algebra.P := by
    have : n * n ≤ 15 * 15 := Nat.mul_le_mul (by omega) (by omega)
    unfold Algebra.P; omega
  have hP' : b.toNat < Algebra.P := by unfold Algebra.P; omega
  refine ⟨n, ?_⟩
  have := congrArg Fp.toNat es'
  rw [toNat_cast hP', show ((n : Nat) : Fp) * ((n : Nat) : Fp) = ((n * n : Nat) : Fp) from
    (Semiring.natCast_mul n n).symm, toNat_cast hP] at this
  exact this

/-! ## Completeness -/

/-- The honest trace: height 2, every row holds the 4 bits of `w`. -/
def honestTrace (w : Nat) : Trace Fp where
  log := fun _ => 1
  cell := fun _ _ c => (((w / 2 ^ c % 2 : Nat) : Nat) : Fp)

theorem bits_ok : ∀ w, w < 16 → ∀ c, c < 4 →
    ((w / 2 ^ c % 2 : Nat) : Fp) * (((w / 2 ^ c % 2 : Nat) : Fp) + -((1 : Nat) : Fp)) = 0 := by
  decide

theorem root_ok : ∀ w, w < 16 →
    (((w / 2 ^ 0 % 2 : Nat) : Fp) + (((2 : Nat) : Fp) * ((w / 2 ^ 1 % 2 : Nat) : Fp) +
      (((4 : Nat) : Fp) * ((w / 2 ^ 2 % 2 : Nat) : Fp) + ((8 : Nat) : Fp) * ((w / 2 ^ 3 % 2 : Nat) : Fp)))) *
    (((w / 2 ^ 0 % 2 : Nat) : Fp) + (((2 : Nat) : Fp) * ((w / 2 ^ 1 % 2 : Nat) : Fp) +
      (((4 : Nat) : Fp) * ((w / 2 ^ 2 % 2 : Nat) : Fp) + ((8 : Nat) : Fp) * ((w / 2 ^ 3 % 2 : Nat) : Fp))))
    + -((w * w : Nat) : Fp) = 0 := by
  decide

theorem lt16 {w : Nat} {b : UInt8} (h : w * w = b.toNat) : w < 16 := by
  have hb : b.toNat < 256 := b.toNat_lt
  refine Nat.lt_of_not_le fun hw => ?_
  have : 16 * 16 ≤ w * w := Nat.mul_le_mul hw hw
  omega

theorem toy_holds (b : UInt8) (w : Nat) (h : w * w = b.toNat) :
    Holds toyAir (pubB b) (honestTrace w) := by
  have hw := lt16 h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have : t = 0 := by simp [toyAir] at ht; omega
    subst this; exact ⟨Nat.le_refl _, show 1 ≤ 4 by decide⟩
  · intro t ht r _ e he
    have : t = 0 := by simp [toyAir] at ht; omega
    subst this
    change e ∈ toyTable.constraints at he
    have hb : (pubB b).getD 0 0 = ((w * w : Nat) : Fp) := by
      show ((b.toNat : Nat) : Fp) = _; rw [h]
    simp only [toyTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bits_ok w hw 0 (by decide)
    · exact bits_ok w hw 1 (by decide)
    · exact bits_ok w hw 2 (by decide)
    · exact bits_ok w hw 3 (by decide)
    · simp only [Expr.eval, Expr.evalWith, rowEnv, bit, root, ite_false, Bool.false_eq_true]
      rw [hb]; exact root_ok w hw
  · intro t ht r _ i hi
    have : t = 0 := by simp [toyAir] at ht; omega
    subst this
    change i ∈ ([] : List Interaction) at hi
    cases hi
  · intro bus m; rfl

theorem toy_header (w : Nat) :
    headerOk toyAir Params.default (Prover.trHdr toyAir (honestTrace w)) = true := by
  show headerOk toyAir Params.default [1] = true
  decide

end ZkFormal.Toy
