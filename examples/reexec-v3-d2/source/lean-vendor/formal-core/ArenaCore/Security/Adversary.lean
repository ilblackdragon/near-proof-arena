import ArenaCore.Security.OracleComp
import ArenaCore.Security.Prob

/-!
# ArenaCore.Security.Adversary — randomized adversaries

A `CoinAdversary α` is a randomized algorithm with output type `α`: an
oracle program whose only oracle is the coin oracle, together with the
tape alphabet `R` and tape length `coins` defining its probability space.
-/

namespace ArenaCore.Security

structure CoinAdversary (α : Type) where
  /-- Tape alphabet size. -/
  R : Nat
  /-- Tape length (number of coin symbols available). -/
  coins : Nat
  /-- The algorithm. -/
  comp : OracleComp coinSpec α

namespace CoinAdversary

variable {α β : Type}

/-- Output on a given tape. -/
def output (A : CoinAdversary α) (tape : List Nat) : α := runCoins A.comp tape

/-- `Pr[E(A)] ≤ num/den`. -/
def PrLE (A : CoinAdversary α) (E : α → Prop) (num den : Nat) : Prop :=
  Security.PrLE A.coins A.R (fun t => E (A.output t)) num den

/-- Post-compose a deterministic function (same coins, same probability
space). -/
def map (f : α → β) (A : CoinAdversary α) : CoinAdversary β :=
  { A with comp := A.comp.bind fun a => .pure (f a) }

theorem simulate_bind_pure {τ : Type} {spec : OracleSpec}
    (impl : (q : spec.Query) → τ → spec.Resp q × τ) (f : α → β) :
    ∀ (oa : OracleComp spec α) (t : τ),
      OracleComp.simulate impl (oa.bind fun a => .pure (f a)) t =
        (f (OracleComp.simulate impl oa t).1, (OracleComp.simulate impl oa t).2)
  | .pure a, t => rfl
  | .query q k, t => by
    simp only [OracleComp.bind, OracleComp.simulate]
    exact simulate_bind_pure impl f (k (impl q t).1) (impl q t).2

theorem output_map (f : α → β) (A : CoinAdversary α) (t : List Nat) :
    (A.map f).output t = f (A.output t) := by
  simp only [output, map, runCoins]
  rw [simulate_bind_pure]

end CoinAdversary

end ArenaCore.Security
