import ArenaCore.SHA256
import ArenaCore.Security.Adversary

/-!
# ArenaCore.Assumptions — governed cryptographic assumptions

Each approved assumption is an exact Lean declaration here.  Governance pins
`security/assumptions/<id>.json` → `lean_decl` to these names; the judge
inserts them as *hypotheses* into the expected theorem type.  A candidate
can never add an assumption: anything it needs must be proved from these
judge-supplied hypotheses (and any extra `axiom` fails `AXIOM_AUDIT`).

## SHA-256 collision resistance (`sha256_cr`)

SHA-256 is a fixed, keyless function, so the textbook statement "no
efficient adversary finds a collision" is not formalisable (a constant
adversary that outputs a collision *exists*, we just don't know one).  We use
the explicit-reduction ("human-ignorance", Rogaway 2006) formulation instead:

* certificates exhibit an explicit, fuel-bounded reduction program that maps
  any bad acceptance to an explicit SHA-256 collision;
* the assumption is a statement about the *specific, explicitly
  constructed* collision finder `F` (the reduction composed with an
  arbitrary adversary), namely that its success probability is at most
  `num/den`.

The resulting theorem reads: for every adversary `A` and every bound
`num/den`, if the explicit finder built from `A` finds collisions with
probability ≤ `num/den`, then `A` breaks the verifier with probability ≤
`num/den` — a tight reduction whose overhead is the reduction's fuel bound.

## SHA-256 as a random oracle (`sha256_rom`)

The random-oracle *model* is not a proposition about SHA-256 (it is
uninstantiable in general); it is a choice of security game.  The id
`sha256RandomOracle` authorises the ROM game of `ArenaCore.Security.ROM`, in
which the domain-separated protocol hash `m ↦ SHA-256("NPAI-RO-v1" ‖ m)` used
by the deployed verifier (and honest prover,
and adversary) is answered by a lazily-sampled random function.
-/

namespace ArenaCore

/-- Approved assumption identifiers (mirrors `security/assumptions/*.json`). -/
inductive AssumptionId where
  /-- `sha256_cr` → `ArenaCore.Assumptions.Sha256CollisionResistant` -/
  | sha256CollisionResistance
  /-- `sha256_rom` → `ArenaCore.Security.ROM.RomSound` (game choice). -/
  | sha256RandomOracle
  deriving DecidableEq, Repr

def AssumptionId.id : AssumptionId → String
  | .sha256CollisionResistance => "sha256_cr"
  | .sha256RandomOracle => "sha256_rom"

namespace Assumptions

open Security

/-- A SHA-256 collision. -/
def IsSha256Collision (xy : Bytes × Bytes) : Prop :=
  xy.1 ≠ xy.2 ∧ sha256 xy.1 = sha256 xy.2

/-- **Governed assumption `sha256_cr`.**  The explicit collision finder `F`
outputs a SHA-256 collision with probability at most `num/den` over its
coins. -/
def Sha256CollisionResistant (F : CoinAdversary (Bytes × Bytes)) (num den : Nat) : Prop :=
  F.PrLE IsSha256Collision num den

end Assumptions

end ArenaCore
