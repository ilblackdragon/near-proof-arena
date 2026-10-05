import ZkFormal.Prover.NpGlobal

/-!
# ZkFormal.Prover.NpGlobal2 — `GlobalStmt` from the bus product equality

`ali_table`: the ALI identity of each table at `z ∉ F`; `global_of`: `GlobalStmt` given
`BusProdStmt` (the honest finals satisfy the bus equation).
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- The honest finals satisfy the bus equation. -/
def BusProdStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp), Holds A (pubOf Fp cb) tr →
    headerOk A dp (hdr A tr) = true → ∀ α γ : Fp8,
      ((List.range A.tables.length).map fun t =>
        ((finsT A cb tr α γ t).take (layT A tr t).sendG).foldl (· * ·) 1).foldl (· * ·) 1 =
      ((List.range A.tables.length).map fun t =>
        ((finsT A cb tr α γ t).drop (layT A tr t).sendG).foldl (· * ·) 1).foldl (· * ·) 1

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-- **The ALI identity** of table `t` at an out-of-domain point. -/
theorem ali_table (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ αc : Fp8)
    {z : Fp8} (hz : ¬ z.IsBase) :
    combine αc (((tb A t).allConstraints.map (·.evalWith (oodEnv (F := Fp)
        (cb.map fun b => ofNatF b.toNat) (tr.log t) z (mainV A tr t z) (mainV A tr t (omg (lg tr t) * z))))) ++
      auxConstraints (tb A t) dp.auxGroup (oodEnv (F := Fp) (cb.map fun b => ofNatF b.toNat) (tr.log t) z
        (mainV A tr t z) (mainV A tr t (omg (lg tr t) * z))) α γ (auxV A cb tr α γ t z)
        (auxV A cb tr α γ t (omg (lg tr t) * z)) (finsT A cb tr α γ t)) =
      (z ^ (2 ^ tr.log t) - 1) * combine (z ^ (2 ^ tr.log t)) (quotV A cb tr α γ αc t z) := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  rw [oodEnv_eq A cb tr t hlog hz]
  show compX A cb tr α γ αc t z = _
  rw [qC_spec A cb tr hH ht α γ αc z, ev_chunks]
  rfl

theorem foldl_tables {α β : Type} (F : Bool × List α → β → Bool × List α) (g : Nat → β)
    (fins : Nat → List α) : ∀ (l : List Nat) (R X : List α), X = l.flatMap fins ++ R →
    (∀ t ∈ l, ∀ R, F (true, fins t ++ R) (g t) = (true, R)) → (l.map g).foldl F (true, X) = (true, R)
  | [], R, X, hX, _ => by simp [hX]
  | t :: l, R, X, hX, h => by
    rw [hX, List.map_cons, List.foldl_cons, List.flatMap_cons, List.append_assoc, h t (by simp)]
    exact foldl_tables F g fins l R _ rfl (fun t' ht' R' => h t' (by simp [ht']) R')

end

end ZkFormal.Prover.Np
