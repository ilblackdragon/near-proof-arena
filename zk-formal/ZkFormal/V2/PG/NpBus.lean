import ZkFormal.V2.PG.NpGlobal2

/-!
# ZkFormal.V2.PG.NpBus (P2 copy of `Prover.NpBus` at `dp = pg g`) — the honest finals satisfy the bus equation (`BusProdStmt`)

On row `r` an interaction's factor is `(γ - fp(bus, msg))^mult` (booleanity of the bits);
each side's product of finals is `∏ (γ - fp(key))^mult` over all (row, interaction) pairs of
that side; by `Holds.balance` both sides have the same multiplicity per key.
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

/-! ## Products -/

def prodF (l : List Fp8) : Fp8 := l.foldl (· * ·) 1

theorem foldl_mul_eq (a : Fp8) : ∀ l : List Fp8, l.foldl (· * ·) a = a * prodF l
  | [] => by simp [prodF]; grind
  | x :: l => by
    simp only [List.foldl_cons, prodF]
    rw [foldl_mul_eq (a * x) l, foldl_mul_eq (1 * x) l]
    simp only [prodF]; grind

theorem prodF_nil : prodF [] = 1 := rfl

theorem prodF_cons (x : Fp8) (l : List Fp8) : prodF (x :: l) = x * prodF l := by
  show l.foldl (· * ·) (1 * x) = _
  rw [foldl_mul_eq]; grind

theorem prodF_append (l l' : List Fp8) : prodF (l ++ l') = prodF l * prodF l' := by
  induction l with
  | nil => simp [prodF_nil]; grind
  | cons x l ih => rw [List.cons_append, prodF_cons, prodF_cons, ih]; grind

theorem prodF_flatMap {α : Type} (f : α → List Fp8) : ∀ l : List α,
    prodF (l.flatMap f) = prodF (l.map fun a => prodF (f a))
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, prodF_append, List.map_cons, prodF_cons, prodF_flatMap f l]

theorem prodF_map_mul {α : Type} (f g : α → Fp8) : ∀ l : List α,
    prodF (l.map fun a => f a * g a) = prodF (l.map f) * prodF (l.map g)
  | [] => by simp [prodF_nil]; grind
  | a :: l => by simp only [List.map_cons, prodF_cons, prodF_map_mul f g l]; grind

theorem prodF_map_one {α : Type} : ∀ l : List α, prodF (l.map fun _ => (1 : Fp8)) = 1
  | [] => rfl
  | a :: l => by simp only [List.map_cons, prodF_cons, prodF_map_one l]; grind

/-- Swapping two finite products. -/
theorem prodF_swap {α β : Type} (f : α → β → Fp8) (l : List α) : ∀ m : List β,
    prodF (l.map fun a => prodF (m.map fun b => f a b)) = prodF (m.map fun b => prodF (l.map fun a => f a b))
  | [] => by simp [prodF_nil, prodF_map_one]
  | b :: m => by
    simp only [List.map_cons, prodF_cons]
    rw [prodF_map_mul (fun a => f a b) (fun a => prodF (m.map fun b => f a b)), prodF_swap f l m]

/-! ## Products of powers by multiplicity -/

section
variable {κ : Type} [DecidableEq κ]

def cntK (E : List (κ × Nat)) (k : κ) : Nat := (E.map fun e => if e.1 = k then e.2 else 0).sum

def prodPow (g : κ → Fp8) (E : List (κ × Nat)) : Fp8 := prodF (E.map fun e => g e.1 ^ e.2)

theorem prodPow_split (g : κ → Fp8) (k : κ) : ∀ E : List (κ × Nat),
    prodPow g E = g k ^ cntK E k * prodPow g (E.filter fun e => e.1 ≠ k)
  | [] => by simp [prodPow, cntK, prodF_nil, Semiring.pow_zero]; grind
  | e :: E => by
    have ih := prodPow_split g k E
    unfold prodPow cntK at *
    simp only [List.map_cons, prodF_cons, List.sum_cons, List.filter_cons]
    by_cases he : e.1 = k
    · rw [if_pos he, if_neg (by simp [he]), ih, Semiring.pow_add, he]; grind
    · rw [if_neg he, if_pos (by simp [he]), List.map_cons, prodF_cons, ih, Nat.zero_add]; grind

theorem cntK_filter (E : List (κ × Nat)) (k k' : κ) :
    cntK (E.filter fun e => e.1 ≠ k) k' = if k' = k then 0 else cntK E k' := by
  induction E with
  | nil => simp [cntK]
  | cons e E ih =>
    unfold cntK at *
    simp only [List.filter_cons]
    by_cases hk : k' = k
    · subst hk
      by_cases he : e.1 = k'
      · rw [if_neg (by simp [he]), ih, if_pos rfl, if_pos rfl]
      · rw [if_pos (by simp [he]), List.map_cons, List.sum_cons, ih, if_neg he]; simp
    · rw [if_neg hk] at ih ⊢
      by_cases he : e.1 = k
      · rw [if_neg (by simp [he]), ih, List.map_cons, List.sum_cons,
          if_neg (by rw [he]; exact fun h => hk h.symm)]; omega
      · rw [if_pos (by simp [he]), List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]

theorem prodPow_zero (g : κ → Fp8) : ∀ E : List (κ × Nat), (∀ k, cntK E k = 0) → prodPow g E = 1
  | [] => fun _ => rfl
  | e :: E => fun h => by
    have h1 := h e.1
    unfold cntK at h1
    rw [List.map_cons, List.sum_cons, if_pos rfl] at h1
    have he : e.2 = 0 := by omega
    unfold prodPow
    rw [List.map_cons, prodF_cons, he, Semiring.pow_zero, Semiring.one_mul]
    exact prodPow_zero g E (fun k => by
      have := h k; unfold cntK at this ⊢; simp only [List.map_cons, List.sum_cons] at this; omega)

/-- Products of powers only depend on the total multiplicity of each key. -/
theorem prodPow_eq (g : κ → Fp8) : ∀ (N : Nat) (E E' : List (κ × Nat)), E.length ≤ N →
    (∀ k, cntK E k = cntK E' k) → prodPow g E = prodPow g E'
  | 0, E, E', hN, h => by
    have : E = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [prodPow_zero g E' (fun k => by rw [← h k]; rfl)]; rfl
  | N + 1, [], E', _, h => by
    rw [prodPow_zero g E' (fun k => by rw [← h k]; rfl)]; rfl
  | N + 1, e :: E, E', hN, h => by
    rw [prodPow_split g e.1 (e :: E), prodPow_split g e.1 E', h e.1]
    congr 1
    apply prodPow_eq g N
    · have : ((e :: E).filter fun x => x.1 ≠ e.1).length ≤ E.length := by
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ite_false]
        exact List.length_filter_le _ _
      simp at hN; omega
    · intro k
      rw [cntK_filter, cntK_filter, h k]

end

end ZkFormal.V2.PG
