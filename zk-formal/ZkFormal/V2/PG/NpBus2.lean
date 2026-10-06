import ZkFormal.V2.PG.NpBus

/-!
# ZkFormal.V2.PG.NpBus2 (P2 copy of `Prover.NpBus2` at `dp = pg g`) — interaction factors on the trace domain

`phi_row`: on row `r`, the honest factor of interaction `i` is
`(γ - FPv α bus msg)^multNat` (the multiplicity bits are boolean by `Holds`).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- Fingerprint of a bus message (values in the base field). -/
def FPv (α : Fp8) (b : Nat) (m : List Fp) : Fp8 :=
  let r := (m.map Fp8.ofBase).foldl (fun (acc : Fp8 × Fp8) v => (acc.1 + v * acc.2, acc.2 * α)) (0, 1)
  r.1 + ((b + 1 : Nat) : Fp8) * r.2

/-- Bits value of a list of `0/1` extension values. -/
def goV : List Fp8 → Nat → Nat
  | [], _ => 0
  | v :: vs, s => (if v = 1 then 2 ^ s else 0) + goV vs (s + 1)

theorem getLastD_scanl {α β : Type} (f : α → β → α) (d : α) : ∀ (l : List β) (c : α),
    (l.scanl f c).getLastD d = l.foldl f c
  | [], c => rfl
  | x :: l, c => by
    rw [List.scanl_cons, List.getLastD_cons, getLastD_scanl f c l (f c x)]; rfl

theorem bit_pow (v q : Fp8) (hv : v = 0 ∨ v = 1) : 1 + v * (q - 1) = q ^ (if v = 1 then 1 else 0) := by
  rcases hv with rfl | rfl
  · rw [if_neg (by decide +kernel), Semiring.pow_zero]; grind
  · rw [if_pos rfl, Semiring.pow_one]; grind

theorem pow_pow_two (p : Fp8) (s : Nat) (b : Bool) :
    (p ^ (2 ^ s)) ^ (if b then 1 else 0) = p ^ (if b then 2 ^ s else 0) := by
  cases b <;> simp [Semiring.pow_zero, Semiring.pow_one]

theorem prod_bits (p : Fp8) : ∀ (vs : List Fp8) (s : Nat), (∀ v ∈ vs, v = 0 ∨ v = 1) →
    prodF ((vs.zip ((List.range vs.length).map fun j => p ^ (2 ^ (j + s)))).map
      fun (x : Fp8 × Fp8) => 1 + x.1 * (x.2 - 1)) = p ^ goV vs s
  | [], s, _ => by simp [goV, prodF_nil, Semiring.pow_zero]
  | v :: vs, s, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.zip_cons_cons, List.map_cons,
      prodF_cons, List.map_map]
    have ih := prod_bits p vs (s + 1) (fun w hw => h w (by simp [hw]))
    have e : ((fun j => p ^ (2 ^ (j + s))) ∘ Nat.succ) = fun j => p ^ (2 ^ (j + (s + 1))) := by
      funext j; simp only [Function.comp]; congr 2; omega
    rw [e, ih, bit_pow v _ (h v (by simp)), Nat.zero_add]
    show _ = p ^ ((if v = 1 then 2 ^ s else 0) + goV vs (s + 1))
    rw [Semiring.pow_add]
    by_cases hv : v = 1
    · simp only [hv, if_true, Semiring.pow_one]
    · simp only [hv, if_false, Semiring.pow_zero]

theorem tail_scanl_prod (c : Fp8) : ∀ (fac : List Fp8), fac ≠ [] →
    (fac.scanl (· * ·) c).tail.getLastD 1 = c * prodF fac
  | [], h => absurd rfl h
  | x :: l, _ => by
    rw [List.scanl_cons, List.tail_cons, getLastD_scanl, foldl_mul_eq, prodF_cons]; grind

theorem chain_phi (env : Env Fp8) (α γ : Fp8) (i : Interaction)
    (hb : ∀ v ∈ i.mult.map (·.evalWith env), v = 0 ∨ v = 1) :
    (chainOf env α γ i).2 = (γ - fingerprint env α i) ^ goV (i.mult.map (·.evalWith env)) 0 := by
  unfold chainOf
  generalize γ - fingerprint env α i = p0
  generalize i.mult.map (·.evalWith env) = bits at hb
  match bits, hb with
  | [], _ => simp [goV, Semiring.pow_zero]
  | [b], hb =>
    show 1 + b * (p0 - 1) = _
    rw [bit_pow b p0 (hb b (by simp))]
    show _ = p0 ^ ((if b = 1 then 2 ^ 0 else 0) + 0)
    simp
  | b0 :: b1 :: bs, hb =>
    show ((((b1 :: bs).zip ((List.range (b1 :: bs).length).map fun j => p0 ^ (2 ^ (j + 1)))).map
      fun (x : Fp8 × Fp8) => 1 + x.1 * (x.2 - 1)).scanl (· * ·) (1 + b0 * (p0 - 1))).tail.getLastD 1 = _
    rw [tail_scanl_prod _ _ (by simp), prod_bits p0 (b1 :: bs) 1 (fun v hv => hb v (by simp [hv])),
      bit_pow b0 p0 (hb b0 (by simp))]
    show _ = p0 ^ ((if b0 = 1 then 2 ^ 0 else 0) + goV (b1 :: bs) (0 + 1))
    rw [Semiring.pow_add]

end ZkFormal.Prover.Np.G
