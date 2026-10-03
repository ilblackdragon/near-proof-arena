/-!
# ArenaCore.Security.OracleComp — adversaries as oracle-query programs

An adversary is a finite *query tree* (free monad) over an oracle signature.
It has no other source of power: randomness is itself an oracle (`coinSpec`),
and so are hash oracles and honest-proof oracles.  Query budgets are explicit
(`QueryBound`), per query kind, via a weight function.
-/

namespace ArenaCore.Security

/-- An oracle signature: query type and (dependent) response type. -/
structure OracleSpec where
  Query : Type
  Resp : Query → Type

/-- Oracle computations = query trees. -/
inductive OracleComp (spec : OracleSpec) (α : Type) : Type where
  | pure : α → OracleComp spec α
  | query : (q : spec.Query) → (spec.Resp q → OracleComp spec α) → OracleComp spec α

namespace OracleComp

variable {spec : OracleSpec} {α β : Type}

def bind : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | .pure a, f => f a
  | .query q k, f => .query q fun r => bind (k r) f

instance : Monad (OracleComp spec) where
  pure := .pure
  bind := bind

/-- Issue a single query. -/
def ask (q : spec.Query) : OracleComp spec (spec.Resp q) := .query q .pure

/-- Weighted query budget: every root-to-leaf path has total weight `≤ n`.
With `w q = 1` for one kind of query and `0` otherwise this bounds the number
of queries of that kind (adaptively, on every execution path). -/
inductive QueryBound (w : spec.Query → Nat) : OracleComp spec α → Nat → Prop
  | pure (a : α) (n : Nat) : QueryBound w (.pure a) n
  | query (q : spec.Query) (k : spec.Resp q → OracleComp spec α) (n : Nat) :
      w q ≤ n → (∀ r, QueryBound w (k r) (n - w q)) → QueryBound w (.query q k) n

/-- Run against a stateful oracle implementation. -/
def simulate {τ : Type} (impl : (q : spec.Query) → τ → spec.Resp q × τ) :
    OracleComp spec α → τ → α × τ
  | .pure a, t => (a, t)
  | .query q k, t =>
    let (r, t') := impl q t
    simulate impl (k r) t'

theorem QueryBound.mono {w : spec.Query → Nat} {oa : OracleComp spec α} {n m : Nat}
    (h : QueryBound w oa n) (hnm : n ≤ m) : QueryBound w oa m := by
  induction h generalizing m with
  | pure a n => exact .pure a m
  | query q k n hq _ ih =>
    exact .query q k m (Nat.le_trans hq hnm) fun r => ih r (Nat.sub_le_sub_right hnm _)

end OracleComp

/-! ## Coins -/

/-- Uniform-coin oracle: each query returns the next symbol of a random tape. -/
abbrev coinSpec : OracleSpec := ⟨Unit, fun _ => Nat⟩

/-- Every coin query has weight one. -/
def coinWeight : coinSpec.Query → Nat := fun _ => 1

/-- Coin oracle implementation: consume the tape (0 once exhausted; with
`QueryBound` ≤ tape length this never happens). -/
def coinImpl : (q : coinSpec.Query) → List Nat → coinSpec.Resp q × List Nat
  | _, [] => (0, [])
  | _, t :: ts => (t, ts)

/-- Run a coin-driven computation on a tape. -/
def runCoins {α : Type} (oa : OracleComp coinSpec α) (tape : List Nat) : α :=
  (OracleComp.simulate coinImpl oa tape).1

end ArenaCore.Security
