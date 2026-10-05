import ZkFormal.Stark.Verifier

/-!
# ZkFormal.Udr.Rbr — the L3 → L2 interface: round-by-round soundness facts

`RbrFacts V InLang Kall bad agree` packages the round-by-round (RBR) soundness
of a public-coin IOP `V` (lane L4's `IopSpec`) in the unique-decoding regime
(DESIGN.md §6.4), in the form the BCS extraction lemma (lane L2) consumes:

* a *doomed* predicate on partial transcripts (with real oracles), which
* holds initially for claims outside the language,
* survives every prover message,
* is left by at most `bad` of the challenges in `Kall` (for L1's `Fp8.all`:
  of all field elements), and
* at the query phase, for a well-shaped transcript whose clear-text (global)
  checks pass, allows at most `agree n` passing positions out of the `n`
  query positions.

Differences from the draft in DESIGN.md §6.4 (see docs/zk-formal/REQUESTS.md):
`Doomed` is a field (existential) rather than a fixed definition, so the
compiler (L2) is independent of how L3 defines it; `Agree` is the local check
itself (`ChecksPass` on the true openings), so the draft's `local` field is
`rfl` and disappears; `query` assumes the transcript is `Shaped` (the BCS
parser guarantees it) and that the clear-text checks `global` pass (the
verifier checks them before the query phase).
-/

namespace ZkFormal.Udr

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

section
variable {F K : Type}

/-- A message part has the expected shape. -/
def PartV.Fits : PartV K (Oracle F) → Part → Prop
  | .header l, .header n => l.length = n
  | .oracle o, .oracle mats =>
    o.length = mats.length ∧ ∀ k (hk : k < o.length), ∃ sh, mats[k]? = some sh ∧
      o[k].log = sh.1 ∧ o[k].width = sh.2 ∧ ∀ i, i < 2 ^ o[k].log → (o[k].row i).length = o[k].width
  | .elems xs, .elems n => xs.length = n
  | _, _ => False

/-- A transcript entry has the expected shape. -/
def Entry.Fits : Entry K (Oracle F) → Slot → Prop
  | .msg ps, .msg parts => ps.length = parts.length ∧
      ∀ k (hk : k < ps.length), ∃ pt, parts[k]? = some pt ∧ PartV.Fits ps[k] pt
  | .chal _, .chal _ => True
  | _, _ => False

/-- The transcript follows the round structure: every entry fits its slot,
there are no more entries than slots, and a present header is admissible. -/
def Shaped (V : IopSpec F K) (τ : PT K (Oracle F)) : Prop :=
  (∀ l, τ.header? = some l → V.headerOk l = true) ∧
  τ.entries.length ≤ (V.slots τ).length ∧
  ∀ k (hk : k < τ.entries.length), ∃ s, (V.slots τ)[k]? = some s ∧ Entry.Fits τ.entries[k] s

/-- Round-by-round soundness facts of an IOP for a given doomed predicate. -/
structure RbrWith [Field F] [Field K] (V : IopSpec F K) (InLang : Bytes → Prop) (Kall : List K)
    (bad : Nat) (agree : Nat → Nat) (Doomed : PT K (Oracle F) → Prop) : Prop where
  init : ∀ cb, ¬ InLang cb → Doomed (PT.init cb)
  prover : ∀ τ m, Doomed τ → V.NextIsProver τ → Doomed (τ.push m)
  chal : ∀ τ, Doomed τ → V.NextIsChal τ → count Kall (fun c => ¬ Doomed (τ.pushChal c)) ≤ bad
  query : ∀ τ, Doomed τ → V.AtQuery τ → Shaped V τ → V.global (V.prep τ.erase) = true →
    count (List.range (V.domSize τ)) (fun x => V.ChecksPass τ x (V.trueOpenings τ x)) ≤
      agree (V.domSize τ)

/-- **Round-by-round soundness facts** of an IOP (the L3 deliverable): some
doomed predicate satisfies `RbrWith`. -/
def RbrFacts [Field F] [Field K] (V : IopSpec F K) (InLang : Bytes → Prop) (Kall : List K)
    (bad : Nat) (agree : Nat → Nat) : Prop :=
  ∃ Doomed : PT K (Oracle F) → Prop, RbrWith V InLang Kall bad agree Doomed

end

/-! ## The np-udr-stark instance -/

/-- Public inputs as the verifier reads them from the claim bytes. -/
def pubOf (F : Type) [Field F] (cb : Bytes) : List F :=
  cb.map fun b => ofNatF b.toNat

/-- The claim is in the language of the AIR. -/
def AirLang (F : Type) [Field F] [DecidableEq F] (A : Air.Air) (cb : Bytes) : Prop :=
  ∃ tr : Air.Trace F, Air.Holds A (pubOf F cb) tr

/-- Query-phase agreement bound on a domain of size `n` (rate `2^-b`):
`n - e` with the unique-decoding radius `e = (n - n/2^b)/2 - 1`. -/
def agreeUdr (logBlowup n : Nat) : Nat := n - ((n - n / 2 ^ logBlowup) / 2 - 1)

end ZkFormal.Udr
